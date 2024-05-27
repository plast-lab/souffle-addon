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


// #define DEBUG true

#ifdef DEBUG
#define DEBUG_MSG(str) do { std::cout << str << std::endl; } while( false )
#else
#define DEBUG_MSG(str) do { } while ( false )
#endif


extern "C"
{

    static string def_signextend =
        "(define-fun signextend ((b (_ BitVec 256)) (x (_ BitVec 256))) (_ BitVec 256)\
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
    static string def_byte =
        "(define-fun byte ((b (_ BitVec 256)) (x (_ BitVec 256))) (_ BitVec 256)\
            (let (\
            (move (bvmul #x0000000000000000000000000000000000000000000000000000000000000008  b ))\
            )\
            (bvlshr (bvand x (bvlshr #xff00000000000000000000000000000000000000000000000000000000000000 move)) (bvmul #x0000000000000000000000000000000000000000000000000000000000000008 (bvsub #x000000000000000000000000000000000000000000000000000000000000001f b)) )\
            )\
        )\n";

    static string def_my_exp =
        "(\
            define-fun my_exp ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
                ((_ int2bv 256) (to_int (^ (bv2int x) (bv2int y))) )\
        )\n";
    static string def_my_bvshl =
        "(define-fun my_bvshl ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (bvshl y x))\n";
    static string def_my_bvashr =
        "(define-fun my_bvashr ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (bvashr y x))\n";
    static string def_my_bvlshr =
        "(define-fun my_bvlshr ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (bvlshr y x))\n";
    static string def_my_bvgt =
        "(define-fun my_bvgt ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (ite (bvugt x y) \
            #x0000000000000000000000000000000000000000000000000000000000000001\
            #x0000000000000000000000000000000000000000000000000000000000000000\
        ))\n";
    static string def_my_bvsgt =
        "(define-fun my_bvsgt ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (ite (bvsgt x y) \
            #x0000000000000000000000000000000000000000000000000000000000000001\
            #x0000000000000000000000000000000000000000000000000000000000000000\
        ))\n";
    static string def_my_bvlt =
        "(define-fun my_bvlt ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (ite (bvult x y) \
            #x0000000000000000000000000000000000000000000000000000000000000001\
            #x0000000000000000000000000000000000000000000000000000000000000000\
        ))\n";
    static string def_my_bvslt =
        "(define-fun my_bvslt ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (ite (bvslt x y) \
            #x0000000000000000000000000000000000000000000000000000000000000001\
            #x0000000000000000000000000000000000000000000000000000000000000000\
        ))\n";
    static string def_my_eq =
        "(define-fun my_eq ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            (ite (= x y) \
            #x0000000000000000000000000000000000000000000000000000000000000001\
            #x0000000000000000000000000000000000000000000000000000000000000000\
        ))\n";
    static string def_isZero =
        "(define-fun isZero ((x (_ BitVec 256))) (_ BitVec 256)\
            (ite (= x #x0000000000000000000000000000000000000000000000000000000000000000) \
            #x0000000000000000000000000000000000000000000000000000000000000001\
            #x0000000000000000000000000000000000000000000000000000000000000000\
        ))\n";
    static string def_sha3_1arg =
        "(define-fun sha3_1arg ((x (_ BitVec 256))) (_ BitVec 256)\
            #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\
        )\n";
    static string def_sha3 =
        "(define-fun sha3 ((x (_ BitVec 256))) (_ BitVec 256)\
            #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\
        )\n";
    static string def_sha3_2arg =
        "(define-fun sha3_2arg ((x (_ BitVec 256)) (y (_ BitVec 256))) (_ BitVec 256)\
            #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\
        )\n";

    static string define_functions_prologue =
    def_isZero
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
    +def_sha3_2arg;



    z3::context c;
    z3::solver s(c);

    std::map<string,string> encoded_variable_names;

    string change_representation(string smt_bv_constant) {
        string symbolic_constant = smt_bv_constant;
        string substring = symbolic_constant.substr(2, symbolic_constant.length());
        substring.erase(0, std::min(substring.find_first_not_of('0'), substring.size()-1));
        return "0x"+substring;
    }

    string zeros(int len) {
        string zeros = "";
        for (int i = 0; i < len; i++) {
            zeros.insert(0,"0");
        }
        return zeros;
    }

    string fs(int len) {
        string fs = "";
        for (int i = 0; i < len; i++) {
            fs.insert(0,"f");
        }
        return fs;
    }

    bool char_msb_is_zero(char c) {
        return c == '0' | c == '1' | c == '2' | c == '3' | c == '4' | c == '5' | c == '6' | c == '7' ;
    }

    string fix_length(string str, int hex_len) {
        // str of the for 0x____, with <= hex_len hex digits
        
        if (str.length() > hex_len+2) {
            throw std::invalid_argument("too long input");
        }
        
        string prefix;
        // if (char_msb_is_zero(str[2])) {
        //     prefix = zeros(hex_len + 2 - str.length()); 
        // }
        // else {
        //     prefix = fs(hex_len + 2 - str.length()); 
        // }
        prefix = zeros(hex_len + 2 - str.length());
        return str.insert(2, prefix);
    }

    souffle::RamDomain map_list_to_tuples(std::list<souffle::RamDomain> l, souffle::RecordTable* recordTable) {
        if(l.empty()) {
            return 0;
        }
        souffle::RamDomain res[2];
        res[0] = l.front();
        l.pop_front();
        res[1] = map_list_to_tuples(l, recordTable);
        return recordTable->pack(res, 2);
    }




    std::list<souffle::RamDomain> get_list_of_model_entries(solver s,
                souffle::SymbolTable* symbolTable, souffle::RecordTable* recordTable) {

        model m = s.get_model();
        std::list<souffle::RamDomain> entry_list = {};
        // traversing the model
        for (unsigned i = 0; i < m.size(); i++) {
            func_decl v = m[i];
            // skip functions from the model parsing
            // we only care for the variable-constants of the model
            if (v.arity() > 0)
                continue;
            souffle::RamDomain model_entry[2];
            string trimmed_variable_name = v.name().str();

            string original_variable_name = encoded_variable_names.at(trimmed_variable_name);

            model_entry[0] = symbolTable->encode(original_variable_name);
            string value = m.get_const_interp(v).to_string();
            string changed_value = change_representation(value);
            model_entry[1] = symbolTable->encode(changed_value);

            entry_list.push_front(recordTable->pack(model_entry, 2));

        }
        // we can evaluate expressions in the model.
        // std::cout << "x + y + 1 = " << m.eval(x + y + 1) << "\n";
        return entry_list;
    }

    souffle::RamDomain smt_response_with_model(
            souffle::SymbolTable* symbolTable, souffle::RecordTable* recordTable,
            souffle::RamDomain text) {

        const std::string& stext = symbolTable->decode(text);

        DEBUG_MSG(stext);

        souffle::RamDomain res[2];
        std::list<souffle::RamDomain> l;

        s.push();
        s.from_string((
            define_functions_prologue
            +stext).c_str());
        z3::check_result solver_result = s.check();
        s.pop();

        switch (solver_result) {
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

    std::set<string> global_set_for_vars;
    std::set<string> global_set_for_bounded_vars;
    std::map<string,string> operator_mapping;

    void populate_operator_mapping() {

        operator_mapping.insert(make_pair("ADD", "bvadd"));
        operator_mapping.insert(make_pair("SUB", "bvsub"));
        operator_mapping.insert(make_pair("MUL", "bvmul"));

        operator_mapping.insert(make_pair("DIV", "bvudiv"));
        operator_mapping.insert(make_pair("MOD", "bvurem"));
        operator_mapping.insert(make_pair("SDIV", "bvsdiv"));
        operator_mapping.insert(make_pair("SMOD", "bvsmod"));

        operator_mapping.insert(make_pair("EQ", "my_eq")); 
        operator_mapping.insert(make_pair("GT", "my_bvgt")); 
        
        operator_mapping.insert(make_pair("LT", "my_bvlt")); 
        operator_mapping.insert(make_pair("SGT", "my_bvsgt")); 
        operator_mapping.insert(make_pair("SLT", "my_bvslt")); 
        operator_mapping.insert(make_pair("ISZERO", "isZero"));

        operator_mapping.insert(make_pair("AND", "bvand"));
        operator_mapping.insert(make_pair("OR", "bvor"));
        operator_mapping.insert(make_pair("XOR", "bvxor"));
        operator_mapping.insert(make_pair("SHL", "my_bvshl"));
        operator_mapping.insert(make_pair("SHR", "my_bvlshr"));
        operator_mapping.insert(make_pair("SAR", "my_bvashr")); 
        operator_mapping.insert(make_pair("NOT", "bvnot")); 
        
        
        /**
         *  TODO :
         * implement sha3 in smtlib ?
         * For now, i use a constant function....
     */
        operator_mapping.insert(make_pair("SHA3", "sha3")); 
        operator_mapping.insert(make_pair("SHA3_1ARG", "sha3_1arg")); 
        operator_mapping.insert(make_pair("SHA3_2ARG", "sha3_2arg")); 


        operator_mapping.insert(make_pair("BYTE", "byte")); 
        operator_mapping.insert(make_pair("SIGNEXTEND", "signextend"));
        operator_mapping.insert(make_pair("EXP", "my_exp")); 
        



    //  Quantifiers :
        operator_mapping.insert(make_pair("EXISTS", "exists"));
        operator_mapping.insert(make_pair("FORALL", "forall"));

    }

    string get_random_special_value() {
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
    
        int random_index = distr(gen);
        return pool.at(random_index);
    }

    string make_constraint_for_bounded_var(string var) {
        string value = get_random_special_value();
        return "(assert (= "+ var +" "+ value +"))";
    }

    /**
     * TODO: 
     * parse model to find dependency from special values...
    */

    void traverse_model(solver s) {
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

   

    string parse_tree_expr_for_bounded_vars(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain arg) {
        // We expect a sequence of 0 or more forall* quantifiers in the start of an expression and nowhere else

        if (arg == 0) {
            return "";
        }

        const souffle::RamDomain *my_tuple = recordTable->unpack(arg, 3);

        const souffle::RamDomain left = my_tuple[1];
        const souffle::RamDomain right = my_tuple[2];
        bool isLeaf = (left == 0 && right == 0);

        string root_symbol = symbolTable->decode(my_tuple[0]);
        if (isLeaf) {
            if (root_symbol.rfind("0x", 0) == 0) {
                throw std::invalid_argument( "cant bound constant" );            
            }
            else {
                return root_symbol;
            }
        }
        
        if(root_symbol == "FORALLSTAR") {

            string variableToBound = parse_tree_expr_for_bounded_vars(symbolTable, recordTable, left); 
            global_set_for_bounded_vars.insert(variableToBound);
            return parse_tree_expr_for_bounded_vars(symbolTable, recordTable, right);
        }

        return "";
    }


    string parse_tree_expr(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain arg) {

        if (arg == 0) {
            return "";
        }

        const souffle::RamDomain *my_tuple = recordTable->unpack(arg, 3);

        const souffle::RamDomain left = my_tuple[1];
        const souffle::RamDomain right = my_tuple[2];
        bool isLeaf = (left == 0 && right == 0);

        string root_symbol = symbolTable->decode(my_tuple[0]);
        DEBUG_MSG(root_symbol);
        if (isLeaf) {
            if (root_symbol.rfind("0x", 0) == 0) {
                //     uint256_t parsed_hex(root_symbol);
                //     cout << "MY x : " << parsed_hex << endl;
                
                root_symbol = fix_length(root_symbol, 64);
                // root_symbol = parsed_hex.str();
                // replace 0x prefix with #x .... 
                root_symbol[0] = '#';
            }
            else {
                string original_var_name = root_symbol;
                // remove special characters from vars
                // boost::remove_erase_if(root_symbol, boost::is_any_of(" .:'"));
                boost::replace_all(root_symbol, " ", "space");
                boost::replace_all(root_symbol, ".", "dot");
                boost::replace_all(root_symbol, ":", "colon");
                boost::replace_all(root_symbol, "'", "quote");
                // TODO: encode old variable names to fix the model representation later!
                global_set_for_vars.insert(root_symbol);
                encoded_variable_names.insert(make_pair(root_symbol, original_var_name));
            }
        }
        
        if(root_symbol == "FORALLSTAR") {
            parse_tree_expr(symbolTable, recordTable, left); // to add "bounded" variable in globalSetVars
            return parse_tree_expr(symbolTable, recordTable, right);
        }

        if(root_symbol=="FORALL") {
            // "(forall ((x (_ BitVec 256))) P)"
            string lsymbol = parse_tree_expr(symbolTable, recordTable, left);
            string rexpr = parse_tree_expr(symbolTable, recordTable, right);
            string ans = "(forall (("+lsymbol+" (_ BitVec 256))) "+ rexpr+")";
            return ans;
        }

        string ans = (isLeaf ? "" : "(") + (isLeaf ? root_symbol : operator_mapping.at(root_symbol)) + " " + parse_tree_expr(symbolTable, recordTable, left);
        ans = ans + " " + parse_tree_expr(symbolTable, recordTable, right) + (isLeaf ? "" : ")");
        return ans;
    }

    void cleanup_and_insert(string id) {
        string original_identifier = id;
        // boost::remove_erase_if(id, boost::is_any_of(" .:'"));

                boost::replace_all(id, " ", "space");
                boost::replace_all(id, ".", "dot");
                boost::replace_all(id, ":", "colon");
                boost::replace_all(id, "'", "quote");
        // TODO: !
        global_set_for_bounded_vars.insert(id);
        global_set_for_vars.insert(id);
        encoded_variable_names.insert(make_pair(id, original_identifier));


    }

    void add_bounded_variables(
             souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain arg_bound_vars) {
        string current_id;
        const souffle::RamDomain* my_tuple = recordTable->unpack(arg_bound_vars, 2);
        current_id = symbolTable->decode(my_tuple[0]);
        cleanup_and_insert(current_id);
        while (true) {
            if (my_tuple[1] == 0) {
                break;
            }
            my_tuple = recordTable->unpack(my_tuple[1], 2);
            current_id = symbolTable->decode(my_tuple[0]);
            cleanup_and_insert(current_id);
            
        }
    }

    /**
     * Implement smt-lib mapping!
     */
    souffle::RamDomain printToSmtStyle(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain arg, souffle::RamDomain arg_bound_vars) {

        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        global_set_for_vars.clear();
        global_set_for_bounded_vars.clear();
        populate_operator_mapping();

        string out = parse_tree_expr(symbolTable, recordTable, arg);
        parse_tree_expr_for_bounded_vars(symbolTable, recordTable, arg);

        add_bounded_variables(symbolTable, recordTable, arg_bound_vars);

        string declarations = "";
        for (string s: global_set_for_vars) {
            declarations += "(declare-const " + s + " (_ BitVec 256))\n";
        }

        const souffle::RamDomain *my_tuple = recordTable->unpack(arg, 3);
        string root_symbol = symbolTable->decode(my_tuple[0]);

        string result;
        // if (root_symbol == "SUB") .... 
        result = declarations + "( assert (= #x0000000000000000000000000000000000000000000000000000000000000001 " + out + ") )\n";

        string result_with_constraints = result;
        for(string s  : global_set_for_bounded_vars) {
            result_with_constraints += make_constraint_for_bounded_var(s);
        }
        return symbolTable->encode(result_with_constraints);
    }
     
    const char *smt_response_simple(const char *text) {
        z3::context c;
        z3::solver s(c);
        s.from_string(text);

        switch (s.check()) {
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
        const souffle::RamDomain* my_tuple = recordTable->unpack(arg, 2);
        // This is ugly and error-prone.  We should provide a higher-level API which
        // understands the internal data representation for ADTs
        const souffle::RamDomain* modelTuple = recordTable->unpack(my_tuple[1], 2);
        cout << my_tuple[0] << " - "<<  symbolTable->decode(my_tuple[0]) << " - " <<  ((my_tuple[1] == 0) ? 0 : my_tuple[1] )<< "\n";
        
        souffle::RamDomain model = my_tuple[1];
        // while (true) {
        //     if (model == 0) {
        //         break;
        //     }
            
        //     const souffle::RamDomain* model2 = recordTable->unpack(model, 2);
        //     const souffle::RamDomain* model_entry = recordTable->unpack(model2[0], 2);

            
        //     cout << "Model : " << symbolTable->decode(model_entry[0]) << " has value "  <<  model_entry[1]  << "\n";
            
        //     model  = model2[1];
        // }
        
        if(my_tuple[1] == 0) {
            return recordTable->pack(&my_tuple[0], 2);
        }

        souffle::RamDomain fixed_entry[2] = {symbolTable->encode("c"), 333};
        souffle::RamDomain model2[2];
        model2[0] = recordTable->pack(fixed_entry,2);
        model2[1] = 0;

        souffle::RamDomain res[2];
        res[0] = symbolTable->encode("sat");
        res[1] = recordTable->pack(&model2[0], 2);
        return recordTable->pack(&res[0], 2);

    }


}
