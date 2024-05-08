#include <iostream>
#include <sstream>
#include <vector>
#include <z3++.h>
#include <list>

#include <random>
#include <boost/range/algorithm_ext/erase.hpp>
#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string.hpp>

#include "souffle/RecordTable.h"
#include "souffle/SymbolTable.h"
#include <souffle/SouffleInterface.h>
#include <cassert>

#include <set>

using namespace std;
using namespace z3;


#define DEBUG true

#ifdef DEBUG
#define DEBUG_MSG(str) do { std::cout << str << std::endl; } while( false )
#else
#define DEBUG_MSG(str) do { } while ( false )
#endif


extern "C"
{

    std::map<string,string> encoded_variable_names;

    string change_representation(string smt_bv_constant){
        string symbolic_constant = smt_bv_constant;
        string substring = symbolic_constant.substr(2, symbolic_constant.length());
        substring.erase(0, std::min(substring.find_first_not_of('0'), substring.size()-1));
        return "0x"+substring;
    }

    string zeros(int len){
        string zeros = "";
        for (int i = 0; i < len; i++)
        {
            zeros.insert(0,"0");
        }
        
        return zeros;
    }
    string fs(int len){
        string fs = "";
        for (int i = 0; i < len; i++)
        {
            fs.insert(0,"f");
        }
        
        return fs;
    }

    bool char_msb_is_zero(char c){
        return c == '0' | c == '1' | c == '2' | c == '3' | c == '4' | c == '5' | c == '6' | c == '7' ;
    }

    string fixLength(string str, int hex_len){
        // str of the for 0x____, with <= hex_len hex digits
        
        if (str.length() > hex_len+2)
        {   
            throw std::invalid_argument("too long input");
        }
        
        string prefix;
        // if (char_msb_is_zero(str[2])){
        //     prefix = zeros(hex_len + 2 - str.length()); 
        // }
        // else {
        //     prefix = fs(hex_len + 2 - str.length()); 
        // }
        prefix = zeros(hex_len + 2 - str.length());
        return str.insert(2, prefix);
    }

    souffle::RamDomain map_list_to_tuples(std::list<souffle::RamDomain> l, souffle::RecordTable* recordTable){
        if(l.empty()){
            return 0;
        }
        souffle::RamDomain res[2];
        res[0] = l.front(); 
        l.pop_front();
        res[1] = map_list_to_tuples(l, recordTable);
        return recordTable->pack(res, 2);
    }




    std::list<souffle::RamDomain> get_list_of_model_entries(solver s,
                souffle::SymbolTable* symbolTable, souffle::RecordTable* recordTable)
    {
        model m = s.get_model();
        std::list<souffle::RamDomain> entry_list = {};
        // traversing the model
        for (unsigned i = 0; i < m.size(); i++) {
            func_decl v = m[i];
            // this problem contains only constants
            assert(v.arity() == 0); 
            // DEBUG_MSG(v.name() << " = " << m.get_const_interp(v));
            souffle::RamDomain modelEntry[2];
            string trimmed_variable_name = v.name().str();
                            
            string original_variable_name = encoded_variable_names.at(trimmed_variable_name);

            modelEntry[0] = symbolTable->encode(original_variable_name);
            string value = m.get_const_interp(v).to_string();
            string changed_value = change_representation(value);
            modelEntry[1] = symbolTable->encode(changed_value);

            entry_list.push_front(recordTable->pack(modelEntry, 2));

        }
        // we can evaluate expressions in the model.
        // std::cout << "x + y + 1 = " << m.eval(x + y + 1) << "\n";
        return entry_list;
    }

    souffle::RamDomain smt_response_with_model(
            souffle::SymbolTable* symbolTable, souffle::RecordTable* recordTable,
            souffle::RamDomain text)
    {

        z3::context c;
        
        string def_signextend = "(define-fun signextend ((b (_ BitVec 256)) (x (_ BitVec 256))) (_ BitVec 256)\
	(let (\
	(move (bvmul #x0000000000000000000000000000000000000000000000000000000000000008 (bvadd b #x0000000000000000000000000000000000000000000000000000000000000001 )))\
	)\
\
	(	ite (= #x0000000000000000000000000000000000000000000000000000000000000000\
			(bvand x (bvshl #x0000000000000000000000000000000000000000000000000000000000000001 (bvsub move #x0000000000000000000000000000000000000000000000000000000000000001 ))))\
	x\
	(bvor x (bvshl #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff move)))\
	)\
)\n";
        string def_byte = "\
(define-fun byte ((b (_ BitVec 256)) (x (_ BitVec 256))) (_ BitVec 256)\
	(let (\
	(move (bvmul #x0000000000000000000000000000000000000000000000000000000000000008  b ))\
	)\
	 (bvlshr (bvand x (bvlshr #xff00000000000000000000000000000000000000000000000000000000000000 move)) (bvmul #x0000000000000000000000000000000000000000000000000000000000000008 (bvsub #x000000000000000000000000000000000000000000000000000000000000001f b)) )\
	)\
)\n";

        string def_my_exp =    "(\
            define-fun my_exp ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
                ((_ int2bv 256) (to_int (^ (bv2int x) (bv2int y))) )\
            )\n";
        string def_my_bvshl = "(define-fun my_bvshl ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (bvshl y x))\n";
        string def_my_bvashr = "(define-fun my_bvashr ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (bvashr y x))\n";
        string def_my_bvlshr = "(define-fun my_bvlshr ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (bvlshr y x))\n";
        string def_my_bvgt = "(define-fun my_bvgt ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (ite (bvugt x y) \
            #x0000000000000000000000000000000000000000000000000000000000000001\
            #x0000000000000000000000000000000000000000000000000000000000000000\
        ))\n";
        string def_my_bvsgt = "(define-fun my_bvsgt ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (ite (bvsgt x y) \
            #x0000000000000000000000000000000000000000000000000000000000000001\
            #x0000000000000000000000000000000000000000000000000000000000000000\
        ))\n";
                string def_my_bvlt = "(define-fun my_bvlt ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (ite (bvult x y) \
            #x0000000000000000000000000000000000000000000000000000000000000001\
            #x0000000000000000000000000000000000000000000000000000000000000000\
        ))\n";
                string def_my_bvslt = "(define-fun my_bvslt ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (ite (bvslt x y) \
            #x0000000000000000000000000000000000000000000000000000000000000001\
            #x0000000000000000000000000000000000000000000000000000000000000000\
        ))\n";
        string def_my_eq = "(define-fun my_eq ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (ite (= x y) \
            #x0000000000000000000000000000000000000000000000000000000000000001\
            #x0000000000000000000000000000000000000000000000000000000000000000\
        ))\n";
        string def_isZero = "(define-fun isZero ((x (_ BitVec 256))) (_ BitVec 256)\
            (ite (= x #x0000000000000000000000000000000000000000000000000000000000000000) \
            #x0000000000000000000000000000000000000000000000000000000000000001\
            #x0000000000000000000000000000000000000000000000000000000000000000\
        ))\n";
        string def_sha3_1arg = "(define-fun sha3_1arg ((x (_ BitVec 256))) (_ BitVec 256)\
            #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\
        )\n";        
        string def_sha3 = "(define-fun sha3 ((x (_ BitVec 256))) (_ BitVec 256)\
            #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\
        )\n";        
        string def_sha3_2arg = "(define-fun sha3_2arg ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\
        )\n";
        z3::solver s(c);
        const std::string& stext = symbolTable->decode(text);

        DEBUG_MSG(stext);


        s.from_string((def_isZero
            +def_byte
            +def_signextend
            +def_my_exp
            +def_my_bvshl
            +def_my_bvashr
            +def_my_bvlshr
            +def_my_eq
            +def_my_bvgt
            +def_my_bvsgt
            +def_my_bvlt
            +def_my_bvslt
            +def_sha3
            +def_sha3_1arg
            +def_sha3_2arg
            +stext).c_str());

        souffle::RamDomain res[2];
        std::list<souffle::RamDomain> l;
        switch (s.check())
        {
        case unsat:
            res[0] = symbolTable->encode("unsat");
            res[1] = 0;
            return recordTable->pack(&res[0], 2);
        case sat:
            // DEBUG_MSG(s.get_model());

            l =  get_list_of_model_entries(s, symbolTable, recordTable);

            // for (list<souffle::RamDomain>::iterator i = l.begin(); i != l.end(); ++i){
            //     DEBUG_MSG(symbolTable->decode(recordTable->unpack(*i, 2)[0]));
            //     DEBUG_MSG(symbolTable->decode(recordTable->unpack(*i, 2)[1]));
            // }
            res[0] = symbolTable->encode("sat");
            res[1] = map_list_to_tuples(l, recordTable);
            return recordTable->pack(&res[0], 2);
        default:
            res[0] = symbolTable->encode("uknown");
            res[1] = 0;
            return recordTable->pack(&res[0], 2);
        }
    }

    std::set<string> globalSetForVars;
    std::set<string> globalSetForBoundedVars;
    std::map<string,string> opreratorMapping;

    void populateOperatorMapping(){

     opreratorMapping.insert(make_pair("ADD", "bvadd"));
     opreratorMapping.insert(make_pair("SUB", "bvsub"));
     opreratorMapping.insert(make_pair("MUL", "bvmul"));

     opreratorMapping.insert(make_pair("DIV", "bvudiv"));
     opreratorMapping.insert(make_pair("MOD", "bvurem"));
     opreratorMapping.insert(make_pair("SDIV", "bvsdiv"));
     opreratorMapping.insert(make_pair("SMOD", "bvsmod"));

     opreratorMapping.insert(make_pair("EQ", "my_eq")); 
     opreratorMapping.insert(make_pair("GT", "my_bvgt")); 
     
     opreratorMapping.insert(make_pair("LT", "my_bvlt")); 
     opreratorMapping.insert(make_pair("SGT", "my_bvsgt")); 
     opreratorMapping.insert(make_pair("SLT", "my_bvslt")); 
     opreratorMapping.insert(make_pair("ISZERO", "isZero"));

     opreratorMapping.insert(make_pair("AND", "bvand"));
     opreratorMapping.insert(make_pair("OR", "bvor"));
     opreratorMapping.insert(make_pair("XOR", "bvxor"));
     opreratorMapping.insert(make_pair("SHL", "my_bvshl"));
     opreratorMapping.insert(make_pair("SHR", "my_bvlshr"));
     opreratorMapping.insert(make_pair("SAR", "my_bvashr")); 
     opreratorMapping.insert(make_pair("NOT", "bvnot")); 
     
     
     /**
      *  TODO :
      * implement sha3 in smtlib ?
      * For now, i use a constant function....
     */
     opreratorMapping.insert(make_pair("SHA3", "sha3")); 
     opreratorMapping.insert(make_pair("SHA3_1ARG", "sha3_1arg")); 
     opreratorMapping.insert(make_pair("SHA3_2ARG", "sha3_2arg")); 


     opreratorMapping.insert(make_pair("BYTE", "byte")); 
     opreratorMapping.insert(make_pair("SIGNEXTEND", "signextend"));
     opreratorMapping.insert(make_pair("EXP", "my_exp")); 
     



    //  Quantifiers :
     opreratorMapping.insert(make_pair("EXISTS", "exists"));
     opreratorMapping.insert(make_pair("FORALL", "forall"));

    }

    string getRandomSpecialValue(){
        // string  out;
        vector<string> pool, out;
        pool.push_back("#x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
        pool.push_back("#x1123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
        pool.push_back("#x2123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
        pool.push_back("#x3123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
        pool.push_back("#x4123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
        pool.push_back("#x5123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
        pool.push_back("#x6123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
        
    random_device rd; // obtain a random number from hardware
    mt19937 gen(rd()); // seed the generator
    uniform_int_distribution<> distr(0, pool.size()-1); // define the range
    
        int randomIndex = distr(gen);
        return pool.at(randomIndex);
    }

    string makeConstraintForBoundedVar(string var){
        string value = getRandomSpecialValue();
        return "(assert (= "+ var +" "+ value +"))";
    }

    /**
     * TODO: 
     * parse model to find dependency from special values...
    */

    void traverse_model(solver s){
    model m = s.get_model();
    // traversing the model
    for (unsigned i = 0; i < m.size(); i++) {
        func_decl v = m[i];
        // this problem contains only constants
        assert(v.arity() == 0); 
        // DEBUG_MSG(v.name() << " = " << m.get_const_interp(v));
    }
    // we can evaluate expressions in the model.
    // std::cout << "x + y + 1 = " << m.eval(x + y + 1) << "\n";
    }

    const char *smt_response_simple(const char *text);

   

    string parseTreeExprForBoundedVars(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain arg)
    {
        // We expect a sequence of 0 or more forall* quantifiers in the start of an expression and nowhere else

        if (arg == 0)
        {
            return "";
        }

        const souffle::RamDomain *myTuple = recordTable->unpack(arg, 3);

        const souffle::RamDomain left = myTuple[1];
        const souffle::RamDomain right = myTuple[2];
        bool isLeaf = (left == 0 && right == 0);

        string rootSymbol = symbolTable->decode(myTuple[0]);
        if (isLeaf)
        {
            if (rootSymbol.rfind("0x", 0) == 0)
            {
                throw std::invalid_argument( "cant bound constant" );            
            }
            else 
            {
                return rootSymbol;
            }
        }
        
        if(rootSymbol == "FORALLSTAR"){

            string variableToBound = parseTreeExprForBoundedVars(symbolTable, recordTable, left); 
            globalSetForBoundedVars.insert(variableToBound);
            return parseTreeExprForBoundedVars(symbolTable, recordTable, right);
        }

        return "";
    }


    string parseTreeExpr(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain arg)
    {

        if (arg == 0)
        {
            return "";
        }

        const souffle::RamDomain *myTuple = recordTable->unpack(arg, 3);

        const souffle::RamDomain left = myTuple[1];
        const souffle::RamDomain right = myTuple[2];
        bool isLeaf = (left == 0 && right == 0);

        string rootSymbol = symbolTable->decode(myTuple[0]);
        DEBUG_MSG(rootSymbol);
        if (isLeaf)
        {
            if (rootSymbol.rfind("0x", 0) == 0)
            {
                //     uint256_t parsed_hex(rootSymbol);
                //     cout << "MY x : " << parsed_hex << endl;
                
                rootSymbol = fixLength(rootSymbol, 64);
                // rootSymbol = parsed_hex.str();
                // replace 0x prefix with #x .... 
                rootSymbol[0] = '#';
            } else 
            {
                string original_var_name = rootSymbol;
                // remove special characters from vars
                // boost::remove_erase_if(rootSymbol, boost::is_any_of(" .:'"));
                boost::replace_all(rootSymbol, " ", "space");
                boost::replace_all(rootSymbol, ".", "dot");
                boost::replace_all(rootSymbol, ":", "colon");
                boost::replace_all(rootSymbol, "'", "quote");
                // TODO: encode old variable names to fix the model representation later!
                globalSetForVars.insert(rootSymbol);
                encoded_variable_names.insert(make_pair(rootSymbol, original_var_name));
            }
        }
        
        if(rootSymbol == "FORALLSTAR"){
            parseTreeExpr(symbolTable, recordTable, left); // to add "bounded" variable in globalSetVars
            return parseTreeExpr(symbolTable, recordTable, right);
        }

        if(rootSymbol=="FORALL"){
            // "(forall ((x (_ BitVec 256))) P)"
            string lsymbol = parseTreeExpr(symbolTable, recordTable, left);
            string rexpr = parseTreeExpr(symbolTable, recordTable, right);
            string ans = "(forall (("+lsymbol+" (_ BitVec 256))) "+ rexpr+")";
            return ans;
        }

        string ans = (isLeaf ? "" : "(") + (isLeaf ? rootSymbol : opreratorMapping.at(rootSymbol)) + " " + parseTreeExpr(symbolTable, recordTable, left);
        ans = ans + " " + parseTreeExpr(symbolTable, recordTable, right) + (isLeaf ? "" : ")");
        return ans;
    }

    void cleanup_and_insert(string id){
        string original_identifier = id;
        // boost::remove_erase_if(id, boost::is_any_of(" .:'"));

                boost::replace_all(id, " ", "space");
                boost::replace_all(id, ".", "dot");
                boost::replace_all(id, ":", "colon");
                boost::replace_all(id, "'", "quote");
        // TODO: !
        globalSetForBoundedVars.insert(id);
        globalSetForVars.insert(id);
        encoded_variable_names.insert(make_pair(id, original_identifier));


    }

    void addBoundedVariables(
             souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain arg_bound_vars)   
    {
        string current_id;
        const souffle::RamDomain* myTuple = recordTable->unpack(arg_bound_vars, 2);
        current_id = symbolTable->decode(myTuple[0]);
        cleanup_and_insert(current_id);
        while (true)
        {   
            if (myTuple[1] == 0)
            {
                break;
            }
            myTuple = recordTable->unpack(myTuple[1], 2);
            current_id = symbolTable->decode(myTuple[0]);
            cleanup_and_insert(current_id);
            
        }
    }

    /**
     * Implement smt-lib mapping!
     */
    souffle::RamDomain printToSmtStyle(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain arg, souffle::RamDomain arg_bound_vars)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        globalSetForVars.clear();
        globalSetForBoundedVars.clear();
        populateOperatorMapping();

        string out = parseTreeExpr(symbolTable, recordTable, arg);
        parseTreeExprForBoundedVars(symbolTable, recordTable, arg);

        addBoundedVariables(symbolTable, recordTable, arg_bound_vars);

        string declarations = "";
        for (string s: globalSetForVars)
        {
            declarations += "(declare-const " + s + " (_ BitVec 256))\n";
        }

        const souffle::RamDomain *myTuple = recordTable->unpack(arg, 3);
        string rootSymbol = symbolTable->decode(myTuple[0]);

        string result;
        // if (rootSymbol == "SUB") .... 
        result = declarations + "( assert (= #x0000000000000000000000000000000000000000000000000000000000000001 " + out + ") )\n";

        string resultWithConstraints = result;
        for(string s  : globalSetForBoundedVars){
            resultWithConstraints += makeConstraintForBoundedVar(s);
        }
        return symbolTable->encode(resultWithConstraints);
    }
     
    const char *smt_response_simple(const char *text)
    {
        z3::context c;
        z3::solver s(c);
        s.from_string(text);

        switch (s.check())
        {
        case unsat:
            return "unsat";
        case sat:
            traverse_model(s);
            return "sat";
        default:
            return "unknown";
        }
    }



souffle::RamDomain id_model(
        souffle::SymbolTable* symbolTable, souffle::RecordTable* recordTable, souffle::RamDomain arg) {
    assert(symbolTable && "NULL symbol table");
    assert(recordTable && "NULL record table");
    // Argument is a list element [x, l] where
    // x is a number and l is another list element
    const souffle::RamDomain* myTuple = recordTable->unpack(arg, 2);
    // This is ugly and error-prone.  We should provide a higher-level API which
    // understands the internal data representation for ADTs
    const souffle::RamDomain* modelTuple = recordTable->unpack(myTuple[1], 2);
    cout << myTuple[0] << " - "<<  symbolTable->decode(myTuple[0]) << " - " <<  ((myTuple[1] == 0) ? 0 : myTuple[1] )<< "\n";
    
    souffle::RamDomain model = myTuple[1];
    // while (true)
    // {
    //     if (model == 0)
    //     {
    //         break;
    //     }
        
    //     const souffle::RamDomain* model2 = recordTable->unpack(model, 2);
    //     const souffle::RamDomain* modelEntry = recordTable->unpack(model2[0], 2);

        
    //     cout << "Model : " << symbolTable->decode(modelEntry[0]) << " has value "  <<  modelEntry[1]  << "\n";
        
    //     model  = model2[1];
    // }
    
    if(myTuple[1] == 0){
        return recordTable->pack(&myTuple[0], 2);
    }

    souffle::RamDomain fixedEntry[2] = {symbolTable->encode("c"), 333};
    souffle::RamDomain model2[2];
    model2[0] = recordTable->pack(fixedEntry,2);
    model2[1] = 0;

    souffle::RamDomain res[2];
    res[0] = symbolTable->encode("sat");
    res[1] = recordTable->pack(&model2[0], 2);
    return recordTable->pack(&res[0], 2);

}


}