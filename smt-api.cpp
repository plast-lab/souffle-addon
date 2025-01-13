#include <souffle/SouffleInterface.h>
#include <z3++.h>

#include <boost/algorithm/string.hpp>
#include <boost/algorithm/string/classification.hpp>
#include <boost/range/algorithm_ext/erase.hpp>
#include <cassert>
#include <iostream>
#include <list>
#include <random>
#include <set>
#include <sstream>
#include <unordered_map>
#include <vector>

#include "souffle/RecordTable.h"
#include "souffle/SymbolTable.h"

using namespace std;
using namespace z3;

// #define DEBUG true

#ifdef DEBUG
#define DEBUG_MSG(str)             \
  do {                             \
    std::cout << str << std::endl; \
  } while (false)
#else
#define DEBUG_MSG(str) \
  do {                 \
  } while (false)
#endif

#define BIT_VEC_LENGTH 256

#if BIT_VEC_LENGTH == 256
#define SMTLIB_TRUE_VAL "#x0000000000000000000000000000000000000000000000000000000000000001"
#define SMTLIB_FALSE_VAL "#x0000000000000000000000000000000000000000000000000000000000000000"
#define SMTLIB_MINUS_ONE "#xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
#define SMTLIB_8 "#x0000000000000000000000000000000000000000000000000000000000000008"
#define NUM_OF_BYTES_IN_BV "#x000000000000000000000000000000000000000000000000000000000000001f"
#define MASK_M_S_BYTE "#xff00000000000000000000000000000000000000000000000000000000000000"

#define RANDOM_VALUE_0 "#x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#define RANDOM_VALUE_1 "#x1123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#define RANDOM_VALUE_2 "#x2123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#define RANDOM_VALUE_3 "#x3123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#define RANDOM_VALUE_4 "#x4123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#define RANDOM_VALUE_5 "#x5123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#define RANDOM_VALUE_6 "#x6123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"

#else
#define SMTLIB_TRUE_VAL "#x00000001"
#define SMTLIB_FALSE_VAL "#x00000000"
#define SMTLIB_MINUS_ONE "#xffffffff"
#define SMTLIB_8 "#x00000008"
#define NUM_OF_BYTES_IN_BV "#x00000003"
#define MASK_M_S_BYTE "#xff000000"

#define RANDOM_VALUE_0 "#x01234567"
#define RANDOM_VALUE_1 "#x11234567"
#define RANDOM_VALUE_2 "#x21234567"
#define RANDOM_VALUE_3 "#x31234567"
#define RANDOM_VALUE_4 "#x41234567"
#define RANDOM_VALUE_5 "#x51234567"
#define RANDOM_VALUE_6 "#x61234567"
#endif

extern "C" {
z3::context ctx;
z3::solver smt_solver(ctx);

std::map<string, string> encoded_variable_names;

// Enable printing SMT queries to stdout when
// SMT_DEBUG env variable is set
const bool smt_debug = std::getenv("SMT_DEBUG") != nullptr;

bool isPredefinedFunction(string op) {
  if (op == "isZero" || op == "isNotZero" || op == "byte" || op == "signextend" || op == "my_exp" || op == "my_bvshl" || op == "my_bvashr" ||
      op == "my_bvlshr" || op == "my_eq" || op == "my_not_eq" || op == "my_bvgt" || op == "my_bvsgt" || op == "my_bvlt" || op == "my_bvslt" ||
      op == "my_land" || op == "my_lor" || op == "my_lnot" || op == "my_bvge" || op == "my_bvle" ||

      op == "sha3" || op == "sha3_1arg" || op == "sha3_2arg") {
    return false;
  } else {
    return true;
  }
}

string inline_user_defined_function(string op, string lexpr, string rexpr) {
  if (op == "isZero") {
    return "(ite (= " + lexpr + " " + SMTLIB_FALSE_VAL +
           ")"
           " " +
           SMTLIB_TRUE_VAL " " + SMTLIB_FALSE_VAL ")";
  }
  if (op == "isNotZero") {
    return "(ite (= " + lexpr + " " + SMTLIB_FALSE_VAL +
           ")"
           " " +
           SMTLIB_FALSE_VAL " " + SMTLIB_TRUE_VAL ")";
  }
  if (op == "byte") {
    return std::string("(let (") + " (move (bvmul " + SMTLIB_8 + " " + lexpr +
           " ))"
           " )"
           " (bvlshr (bvand " +
           //  rexpr + " (bvlshr " + MASK_M_S_BYTE + " " + "move)) (bvmul " + SMTLIB_8 + " " + "(bvsub " + NUM_OF_BYTES_IN_BV + " " + lexpr + ")) )" + ")";
           rexpr + " (bvlshr " + MASK_M_S_BYTE + " " + "move)) (bvmul " + SMTLIB_8 + " " + "(bvsub " + NUM_OF_BYTES_IN_BV + " " + lexpr + ")) )" + ")";
  }
  if (op == "signextend") {
    return std::string("(let (") + "(move (bvmul" + SMTLIB_8 + " " + "(bvadd " + lexpr + " " + SMTLIB_TRUE_VAL + " )))" + ")" + "(ite (= " + SMTLIB_FALSE_VAL +
           " (bvand " + rexpr + " (bvshl " + SMTLIB_TRUE_VAL + " " + "(bvsub move " + SMTLIB_TRUE_VAL +
           " ))))"
           " " +
           rexpr + " " + "(bvor " + rexpr + " (bvshl " + SMTLIB_MINUS_ONE + " " + "move)))" + ")";
  }
  if (op == "my_exp") {
    if (BIT_VEC_LENGTH == 256) {
      return "((_ int2bv 256) (to_int (^ (bv2int " + lexpr + ") (bv2int " + rexpr + "))) )";
    } else {
      return "((_ int2bv 32) (to_int (^ (bv2int " + lexpr + ") (bv2int " + rexpr + "))) )";
    }
  }
  if (op == "my_bvshl") {
    return "(bvshl " + rexpr + " " + lexpr + ")";
  }
  if (op == "my_bvashr") {
    return "(bvashr " + rexpr + " " + lexpr + ")";
  }
  if (op == "my_bvlshr") {
    return "(bvlshr " + rexpr + " " + lexpr + ")";
  }
  if (op == "my_not_eq") {
    return "(ite (= " + lexpr + " " + rexpr +
           ")"
           " " +
           SMTLIB_FALSE_VAL " " + SMTLIB_TRUE_VAL ")";
  }
  if (op == "my_eq") {
    return "(ite (= " + lexpr + " " + rexpr +
           ")"
           " " +
           SMTLIB_TRUE_VAL " " + SMTLIB_FALSE_VAL ")";
  }

  if (op == "my_land") {
    return "(ite (= " + lexpr + " " + SMTLIB_FALSE_VAL + ") " + SMTLIB_FALSE_VAL + " (ite (= " + rexpr + " " + SMTLIB_FALSE_VAL + " )" + SMTLIB_FALSE_VAL +
           " " + SMTLIB_TRUE_VAL + "))";
  }
  if (op == "my_lor") {
    return "(ite (= " + lexpr + " " + SMTLIB_FALSE_VAL + ") " + " (ite (= " + rexpr + " " + SMTLIB_FALSE_VAL + " )" + SMTLIB_FALSE_VAL + " " +
           SMTLIB_TRUE_VAL ")" + SMTLIB_TRUE_VAL + ")";
  }
  if (op == "my_lnot") {
    return "(ite (= " + lexpr + " " + SMTLIB_FALSE_VAL + ") " + SMTLIB_TRUE_VAL + " " + SMTLIB_FALSE_VAL + ")";
  }

  if (op == "my_bvge") {
    return "(ite (bvuge " + lexpr + " " + rexpr +
           ")"
           " " +
           SMTLIB_TRUE_VAL " " + SMTLIB_FALSE_VAL ")";
  }
  if (op == "my_bvle") {
    return "(ite (bvule " + lexpr + " " + rexpr +
           ")"
           " " +
           SMTLIB_TRUE_VAL " " + SMTLIB_FALSE_VAL ")";
  }

  if (op == "my_bvgt") {
    return "(ite (bvugt " + lexpr + " " + rexpr +
           ")"
           " " +
           SMTLIB_TRUE_VAL " " + SMTLIB_FALSE_VAL ")";
  }
  if (op == "my_bvsgt") {
    return "(ite (bvsgt " + lexpr + " " + rexpr +
           ")"
           " " +
           SMTLIB_TRUE_VAL " " + SMTLIB_FALSE_VAL ")";
  }
  if (op == "my_bvlt") {
    return "(ite (bvult " + lexpr + " " + rexpr +
           ")"
           " " +
           SMTLIB_TRUE_VAL " " + SMTLIB_FALSE_VAL ")";
  }
  if (op == "my_bvslt") {
    return "(ite (bvslt " + lexpr + " " + rexpr +
           ")"
           " " +
           SMTLIB_TRUE_VAL " " + SMTLIB_FALSE_VAL ")";
  }
  if (op == "sha3") {
    return SMTLIB_MINUS_ONE;
  }
  if (op == "sha3_1arg") {
    return SMTLIB_MINUS_ONE;
  }
  if (op == "sha3_2arg") {
    return SMTLIB_MINUS_ONE;
  }
  throw op;
}

string change_representation(string smt_bv_constant) {
  string symbolic_constant = smt_bv_constant;
  string substring = symbolic_constant.substr(2, symbolic_constant.length());
  substring.erase(0, std::min(substring.find_first_not_of('0'), substring.size() - 1));
  return "0x" + substring;
}

string repeat_symbol_n_times(string symbol, int n) {
  string str = "";
  for (int i = 0; i < n; i++) {
    str.insert(0, symbol);
  }
  return str;
}

string zeros(int len) {
  string zeros = "";
  for (int i = 0; i < len; i++) {
    zeros.insert(0, "0");
  }
  return zeros;
}

string fs(int len) {
  string fs = "";
  for (int i = 0; i < len; i++) {
    fs.insert(0, "f");
  }
  return fs;
}

bool char_msb_is_zero(char c) { return c == '0' | c == '1' | c == '2' | c == '3' | c == '4' | c == '5' | c == '6' | c == '7'; }

string fix_length(string str, int hex_len) {
  // str of the form 0x____, with <= hex_len hex digits

  if (str.length() > hex_len + 2) {
    throw std::invalid_argument(str + " too long input");
  }

  string prefix;

  prefix = zeros(hex_len + 2 - str.length());
  return str.insert(2, prefix);
}

souffle::RamDomain map_list_to_tuples(std::list<souffle::RamDomain> l, souffle::RecordTable *record_table) {
  if (l.empty()) {
    return 0;
  }
  souffle::RamDomain res[2];
  res[0] = l.front();
  l.pop_front();
  res[1] = map_list_to_tuples(l, record_table);
  return record_table->pack(res, 2);
}

std::list<souffle::RamDomain> get_list_of_model_entries(solver smt_solver, souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table) {
  z3::model model = smt_solver.get_model();
  std::list<souffle::RamDomain> entry_list = {};
  // traversing the model
  for (unsigned i = 0; i < model.size(); i++) {
    func_decl var = model[i];
    // skip functions from the model parsing
    // we only care for the variable-constants of the model
    if (var.arity() > 0) continue;
    souffle::RamDomain model_entry[2];
    string trimmed_variable_name = var.name().str();

    string original_variable_name = encoded_variable_names.at(trimmed_variable_name);

    model_entry[0] = symbol_table->encode(original_variable_name);
    string value = model.get_const_interp(var).to_string();
    string changed_value = change_representation(value);
    model_entry[1] = symbol_table->encode(changed_value);
    entry_list.push_front(record_table->pack(model_entry, 2));
  }
  // we can evaluate expressions in the model.
  // std::cout << "x + y + 1 = " << model.eval(x + y + 1) << "\n";
  return entry_list;
}

// hash<string> hasher;
unordered_map<string, souffle::RamDomain> cache_smt_response_with_model = {};
souffle::RamDomain smt_response_with_model(souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table, souffle::RamDomain text) {
  const std::string &query = symbol_table->decode(text);

  if (cache_smt_response_with_model.find(query) != cache_smt_response_with_model.end()) {
    // we have already make this computation once!
    return cache_smt_response_with_model.at(query);
  }

  DEBUG_MSG(query);

  souffle::RamDomain res[2];
  std::list<souffle::RamDomain> assignments;

  smt_solver.push();
  try {
    smt_solver.from_string((
                               // define_functions_prologue+
                               query)
                               .c_str());
  } catch (z3::exception ex) {
    // cout << query << endl;
    cout << "Exception: Invalid SMT query" << endl;
  }
  z3::check_result solver_result = smt_solver.check();

  souffle::RamDomain result;
  switch (solver_result) {
    case unsat:
      res[0] = symbol_table->encode("unsat");
      res[1] = 0;
      result = record_table->pack(&res[0], 2);
      cache_smt_response_with_model[query] = result;
      break;
    case sat:
      assignments = get_list_of_model_entries(smt_solver, symbol_table, record_table);
      res[0] = symbol_table->encode("sat");
      res[1] = map_list_to_tuples(assignments, record_table);
      result = record_table->pack(&res[0], 2);
      cache_smt_response_with_model[query] = result;
      break;
    default:
      res[0] = symbol_table->encode("unknown");
      res[1] = 0;
      result = record_table->pack(&res[0], 2);
      cache_smt_response_with_model[query] = result;
      break;
  }
  smt_solver.pop();
  if (smt_debug) {
    std::cerr << "(push)" << std::endl;
    std::cerr << query << "(check-sat) ; " << symbol_table->decode(res[0]) << std::endl;
    if (symbol_table->decode(res[0]) == "sat") {
      std::cerr << "(get-model) ; ";
      for (souffle::RamDomain entry : assignments) {
        const souffle::RamDomain *my_tuple = record_table->unpack(entry, 2);
        std::cerr << symbol_table->decode(my_tuple[0]) << " = " << symbol_table->decode(my_tuple[1]) << " ";
      }
      std::cerr << std::endl << "(pop)" << std::endl;
    }
  }
  return result;
}

std::set<string> global_set_for_vars = {};
std::set<string> global_set_for_bounded_vars = {};
std::set<string> global_set_let_defines = {};
std::set<string> global_set_let_uses = {};
std::map<string, string> operator_mapping = {};

void populate_operator_mapping() {
  operator_mapping.insert(make_pair("NOT_EQ", "my_not_eq"));
  operator_mapping.insert(make_pair("binop_mul", "bvmul"));
  operator_mapping.insert(make_pair("UNOP_NEG", "bvneg"));
  operator_mapping.insert(make_pair("UNOP_ISZERO", "isZero"));

  operator_mapping.insert(make_pair("ADD", "bvadd"));
  operator_mapping.insert(make_pair("SUB", "bvsub"));
  operator_mapping.insert(make_pair("MUL", "bvmul"));

  operator_mapping.insert(make_pair("DIV", "bvudiv"));
  operator_mapping.insert(make_pair("MOD", "bvurem"));
  operator_mapping.insert(make_pair("SDIV", "bvsdiv"));
  operator_mapping.insert(make_pair("SMOD", "bvsmod"));

  operator_mapping.insert(make_pair("EQ", "my_eq"));
  operator_mapping.insert(make_pair("GT", "my_bvgt"));

  operator_mapping.insert(make_pair("GE", "my_bvge"));
  operator_mapping.insert(make_pair("LE", "my_bvle"));

  operator_mapping.insert(make_pair("LT", "my_bvlt"));
  operator_mapping.insert(make_pair("SGT", "my_bvsgt"));
  operator_mapping.insert(make_pair("SLT", "my_bvslt"));
  operator_mapping.insert(make_pair("ISZERO", "isZero"));
  operator_mapping.insert(make_pair("ISNOTZERO", "isNotZero"));

  operator_mapping.insert(make_pair("AND", "bvand"));
  operator_mapping.insert(make_pair("OR", "bvor"));
  operator_mapping.insert(make_pair("XOR", "bvxor"));
  operator_mapping.insert(make_pair("SHL", "my_bvshl"));
  operator_mapping.insert(make_pair("SHR", "my_bvlshr"));
  operator_mapping.insert(make_pair("SAR", "my_bvashr"));
  operator_mapping.insert(make_pair("NOT", "bvnot"));

  operator_mapping.insert(make_pair("LAND", "my_land"));
  operator_mapping.insert(make_pair("LOR", "my_lor"));
  operator_mapping.insert(make_pair("LNOT", "my_lnot"));
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
  pool.push_back(RANDOM_VALUE_0);
  pool.push_back(RANDOM_VALUE_1);
  pool.push_back(RANDOM_VALUE_2);
  pool.push_back(RANDOM_VALUE_3);
  pool.push_back(RANDOM_VALUE_4);
  pool.push_back(RANDOM_VALUE_5);
  pool.push_back(RANDOM_VALUE_6);

  random_device rd;                                      // obtain a random number from hardware
  mt19937 gen(rd());                                     // seed the generator
  uniform_int_distribution<> distr(0, pool.size() - 1);  // define the range

  int random_index = distr(gen);
  return pool.at(random_index);
}

string make_constraint_for_bounded_var(string var) {
  string value = get_random_special_value();
  return "(assert (= " + var + " " + value + "))\n";
}

void traverse_model(solver smt_solver) {
  z3::model model = smt_solver.get_model();
  // traversing the model
  for (unsigned i = 0; i < model.size(); i++) {
    func_decl var = model[i];
    // this problem contains only constants
    assert(var.arity() == 0);
    if (smt_debug) {
      std::cerr << var.name() << " = " << model.get_const_interp(var) << std::endl;
    }
  }
  // we can evaluate expressions in the model.
  // std::cout << "x + y + 1 = " << m.eval(x + y + 1) << "\n";
}

void cleanup_and_insert(string id) {
  string original_identifier = id;
  // boost::remove_erase_if(id, boost::is_any_of(" .:'"));

  boost::replace_all(id, " ", "space");
  boost::replace_all(id, ".", "dot");
  boost::replace_all(id, ":", "colon");
  boost::replace_all(id, "'", "quote");

  global_set_for_bounded_vars.insert(id);
  global_set_for_vars.insert(id);
  encoded_variable_names.insert(make_pair(id, original_identifier));
}

string parse_tree_expr_for_bounded_vars(souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table, souffle::RamDomain arg) {
  // We expect a sequence of 0 or more forall* quantifiers in the start of an
  // expression and nowhere else

  if (arg == 0) {
    return "";
  }

  const souffle::RamDomain *my_tuple = record_table->unpack(arg, 3);

  const souffle::RamDomain left = my_tuple[1];
  const souffle::RamDomain right = my_tuple[2];
  bool is_leaf = (left == 0 && right == 0);

  string root_symbol = symbol_table->decode(my_tuple[0]);
  if (is_leaf) {
    if (root_symbol.rfind("0x", 0) == 0 && root_symbol.rfind("sv", 0) == 0) {
      throw std::invalid_argument("cant bound constant");
    } else {
      return root_symbol;
    }
  }

  if (root_symbol == "FORALLSTAR") {
    string variable_to_bound = parse_tree_expr_for_bounded_vars(symbol_table, record_table, left);
    // global_set_for_bounded_vars.insert(variable_to_bound);
    cleanup_and_insert(variable_to_bound);
    return parse_tree_expr_for_bounded_vars(symbol_table, record_table, right);
  }

  return "";
}

string parse_tree_expr(souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table, souffle::RamDomain arg) {
  if (arg == 0) {
    return "";
  }

  const souffle::RamDomain *my_tuple = record_table->unpack(arg, 3);

  const souffle::RamDomain left = my_tuple[1];
  const souffle::RamDomain right = my_tuple[2];
  bool is_leaf = (left == 0 && right == 0) || (symbol_table->decode(record_table->unpack(left, 3)[0]) == "");

  string root_symbol = symbol_table->decode(my_tuple[0]);
  DEBUG_MSG(root_symbol);
  if (is_leaf) {
    if (root_symbol.rfind("0x", 0) == 0) {
//     uint256_t parsed_hex(root_symbol);
#if BIT_VEC_LENGTH == 256
      root_symbol = fix_length(root_symbol, 64);  // 64 lenght is for 256 bit vectors
#else
      root_symbol = fix_length(root_symbol, 8);  // 8 lenght is for 32 bit vectors
#endif
      // root_symbol = parsed_hex.str();
      // replace 0x prefix with #x ....
      root_symbol[0] = '#';
    } else if (root_symbol == "") {
      // this case may happen if the node is the right child of unary operator
      ;  // do nothing
    } else {
      string original_var_name = root_symbol;
      // remove special characters from vars
      // boost::remove_erase_if(root_symbol, boost::is_any_of(" .:'"));
      boost::replace_all(root_symbol, " ", "space");
      boost::replace_all(root_symbol, ".", "dot");
      boost::replace_all(root_symbol, ":", "colon");
      boost::replace_all(root_symbol, "'", "quote");

      global_set_for_vars.insert(root_symbol);
      encoded_variable_names.insert(make_pair(root_symbol, original_var_name));
    }
  }

  if (root_symbol == "FORALLSTAR") {
    parse_tree_expr(symbol_table, record_table,
                    left);  // to add "bounded" variable in globalSetVars
    return parse_tree_expr(symbol_table, record_table, right);
  }

  if (root_symbol == "FORALL") {
    // "(forall ((x (_ BitVec 256))) P)"
    string lsymbol = parse_tree_expr(symbol_table, record_table, left);
    string rexpr = parse_tree_expr(symbol_table, record_table, right);
#if BIT_VEC_LENGTH == 256
    // string ans = "(forall (("+lsymbol+" (_ BitVec 256))) "+ rexpr+")";
    string ans = "(ite (forall ((" + lsymbol + " (_ BitVec 256))) (=  " + std::string(SMTLIB_TRUE_VAL) + " " + rexpr + ") )" + std::string(SMTLIB_TRUE_VAL) +
                 " " + std::string(SMTLIB_FALSE_VAL) + "  )";
#else
    // string ans = "(forall ((" + lsymbol + " (_ BitVec 32))) " + rexpr + ")";
    string ans = "(ite (forall ((" + lsymbol + " (_ BitVec 256))) (=  " + std::string(SMTLIB_TRUE_VAL) + " " + rexpr + ") )" + std::string(SMTLIB_TRUE_VAL) +
                 " " + std::string(SMTLIB_FALSE_VAL) + "  )";
#endif
    return ans;
  }

  if (root_symbol == "EXISTS") {
    // "(exists ((x (_ BitVec 256))) P)"
    string lsymbol = parse_tree_expr(symbol_table, record_table, left);
    string rexpr = parse_tree_expr(symbol_table, record_table, right);
#if BIT_VEC_LENGTH == 256
    // string ans = "(exists (("+lsymbol+" (_ BitVec 256))) "+ rexpr+")";
    string ans = "(ite (exists ((" + lsymbol + " (_ BitVec 256))) (=  " + std::string(SMTLIB_TRUE_VAL) + " " + rexpr + ") )" + std::string(SMTLIB_TRUE_VAL) +
                 " " + std::string(SMTLIB_FALSE_VAL) + "  )";
#else
    // string ans = "(exists ((" + lsymbol + " (_ BitVec 32))) " + rexpr + ")";
    string ans = "(ite (exists ((" + lsymbol + " (_ BitVec 32))) (=  " + std::string(SMTLIB_TRUE_VAL) + " " + rexpr + ") )" + std::string(SMTLIB_TRUE_VAL) +
                 " " + std::string(SMTLIB_FALSE_VAL) + "  )";
#endif
    return ans;
  }

  string lexpr = parse_tree_expr(symbol_table, record_table, left);
  string rexpr = parse_tree_expr(symbol_table, record_table, right);
  string ans;
  if (is_leaf) {
    ans = root_symbol;
    ans = ans + " ";
  } else {
    string op = operator_mapping.at(root_symbol);
    if (isPredefinedFunction(op)) {
      ans = "(" + op + " " + lexpr;
      ans = ans + " " + rexpr + ")";
    } else {
      // inlining the user-definfed functions
      ans = inline_user_defined_function(op, lexpr, rexpr);
    }
  }
  return ans;
}

void add_bounded_variables(souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table, souffle::RamDomain arg_bound_vars) {
  string current_id;
  if (arg_bound_vars == 0) {
    return;
  }
  const souffle::RamDomain *my_tuple = record_table->unpack(arg_bound_vars, 2);
  current_id = symbol_table->decode(my_tuple[0]);
  cleanup_and_insert(current_id);
  while (true) {
    if (my_tuple[1] == 0) {
      break;
    }
    my_tuple = record_table->unpack(my_tuple[1], 2);
    current_id = symbol_table->decode(my_tuple[0]);
    cleanup_and_insert(current_id);
  }
}

bool is_op_string(string v) {
  map<string, string>::iterator it = operator_mapping.find(v);
  if (it != operator_mapping.end()) {
    return true;
  }
  return false;
}

bool is_symbolic_var(string v) {
  // exclude from symbolic vars strings starting with "0x", AKA constants
  if (v == "") {
    return false;
  }
  if (is_op_string(v)) {
    return false;
  }
  return (v.rfind("0x", 0) != 0);
}

void handle_let_used_vars(souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table, souffle::RamDomain rside) {
  const souffle::RamDomain *rside_unpacked = record_table->unpack(rside, 3);
  string x0 = symbol_table->decode(rside_unpacked[0]);
  string x1 = (rside_unpacked[1] == 0) ? "" : symbol_table->decode(record_table->unpack(rside_unpacked[1], 3)[0]);
  string x2 = (rside_unpacked[2] == 0) ? "" : symbol_table->decode(record_table->unpack(rside_unpacked[2], 3)[0]);

  if (is_symbolic_var(x0)) {
    global_set_let_uses.insert(x0);
  }
  if (is_symbolic_var(x1)) {
    global_set_let_uses.insert(x1);
  }
  if (is_symbolic_var(x2)) {
    global_set_let_uses.insert(x2);
  }
}

int calculate_let_exprs_length(souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table, souffle::RamDomain let_expr_list) {
  if (let_expr_list == 0) {
    return 0;
  }
  const souffle::RamDomain *my_tuple = record_table->unpack(let_expr_list, 2);
  const souffle::RamDomain *top_element_unpacked = record_table->unpack(my_tuple[0], 2);
  if (symbol_table->decode(top_element_unpacked[0]).rfind("0x", 0) == 0) {
    return calculate_let_exprs_length(symbol_table, record_table, my_tuple[1]);
  }
  return 1 + calculate_let_exprs_length(symbol_table, record_table, my_tuple[1]);
}

string print_let_exprs(souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table, souffle::RamDomain let_expr_list) {
  if (let_expr_list == 0) {
    return "";
  }
  const souffle::RamDomain *top_element = record_table->unpack(let_expr_list, 2);
  const souffle::RamDomain *top_element_unpacked = record_table->unpack(top_element[0], 2);
  string rside = parse_tree_expr(symbol_table, record_table, top_element_unpacked[1]);
  string let_def_var = symbol_table->decode(top_element_unpacked[0]);
  if (let_def_var.rfind("0x", 0) == 0) {
    return print_let_exprs(symbol_table, record_table, top_element[1]);
  }

  global_set_let_defines.insert(let_def_var);
  handle_let_used_vars(symbol_table, record_table, top_element_unpacked[1]);

  string top_let_str = "(let ((" + let_def_var + " " + rside + ")) \n";

  //  change the order of addition to reverse the order of lets!
  //  return top_let_str + print_let_exprs(symbol_table, record_table, top_element[1]);
  return print_let_exprs(symbol_table, record_table, top_element[1]) + top_let_str;
}

string find_best_logic(string smtlib_query) {
  vector<string> words_in_query;
  boost::split(words_in_query, smtlib_query, boost::is_any_of(" \t\n()"));
  bool has_quantifier = false;
  for (auto w : words_in_query) {
    if (w == "int2bv" || w == "bv2int" || w == "to_int") {
      return "(set-logic ALL)\n";
    }
    if (w == "forall" || w == "exists") {
      has_quantifier = true;
    }
  }
  if (has_quantifier) {
    return "(set-logic BV)\n";
  } else {
    return "(set-logic QF_BV)\n";
  }
  return "(set-logic ALL)\n";
}

std::map<pair<std::string, set<std::string>>, souffle::RamDomain> cache_print_to_smt_style;

/**
 * Implement smt-lib mapping!
 */
souffle::RamDomain print_to_smt_style(souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table, souffle::RamDomain arg,
                                      souffle::RamDomain arg_bound_vars, souffle::RamDomain let_expr_list) {
  // global sets have to be cleared in every print_to_smt call, since we
  // bound
  global_set_for_bounded_vars.clear();
  global_set_for_vars.clear();

  assert(symbol_table && "NULL symbol table");
  assert(record_table && "NULL record table");

  global_set_for_vars.clear();
  global_set_for_bounded_vars.clear();

  global_set_let_defines.clear();
  global_set_let_uses.clear();

  populate_operator_mapping();

  string out = parse_tree_expr(symbol_table, record_table, arg);
  parse_tree_expr_for_bounded_vars(symbol_table, record_table, arg);

  add_bounded_variables(symbol_table, record_table, arg_bound_vars);

  string declarations = "";
  for (string s : global_set_for_vars) {
#if BIT_VEC_LENGTH == 256
    declarations += "(declare-const " + s + " (_ BitVec 256))\n";
#else
    declarations += "(declare-const " + s + " (_ BitVec 32))\n";
#endif
  }

  std::set<string> temp_set_for_vars = global_set_for_vars;

  const souffle::RamDomain *my_tuple = record_table->unpack(arg, 3);
  string root_symbol = symbol_table->decode(my_tuple[0]);

  string result;
  string let_exprs = print_let_exprs(symbol_table, record_table, let_expr_list);

  int let_length = calculate_let_exprs_length(symbol_table, record_table, let_expr_list);
  string let_declarations = "";
  for (string s : global_set_let_uses) {
    if (temp_set_for_vars.find(s) != temp_set_for_vars.end()) {
      // already declared
      continue;
    }

#if BIT_VEC_LENGTH == 256
    let_declarations += "(declare-const " + s + " (_ BitVec 256))\n";
#else
    let_declarations += "(declare-const " + s + " (_ BitVec 32))\n";
#endif
  }
  result =
      declarations + let_declarations + "( assert " + let_exprs + " (= " + SMTLIB_TRUE_VAL + " " + out + ") " + repeat_symbol_n_times(")", let_length) + " )\n";
  string result_with_constraints = result;

  pair<std::string, set<std::string>> key = make_pair(result_with_constraints, global_set_for_bounded_vars);

  if (cache_print_to_smt_style.find(key) != cache_print_to_smt_style.end()) {
    // we have already made this computation once!
    return cache_print_to_smt_style.at(key);
  }

  for (string s : global_set_for_bounded_vars) {
    result_with_constraints += make_constraint_for_bounded_var(s);
  }
  string result_with_constraints_and_logic = find_best_logic(result_with_constraints) + result_with_constraints;
  souffle::RamDomain encoded_result = symbol_table->encode(result_with_constraints_and_logic);
  cache_print_to_smt_style[key] = encoded_result;
  return encoded_result;
}

const char *smt_response_simple(const char *query) {
  z3::context ctx;
  z3::solver smt_solver(ctx);

  smt_solver.from_string(query);
  const char *result;
  switch (smt_solver.check()) {
    case unsat:
      result = "unsat";
      break;
    case sat:
      traverse_model(smt_solver);
      result = "sat";
      break;
    default:
      result = "unknown";
      break;
  }
  if (smt_debug) {
    std::cerr << query << "(check-sat) ; " << result << std::endl;
  }
  return result;
}

souffle::RamDomain id_model(souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table, souffle::RamDomain arg) {
  assert(symbol_table && "NULL symbol table");
  assert(record_table && "NULL record table");
  // Argument is a list element [x, l] where
  // x is a number and l is another list element
  const souffle::RamDomain *my_tuple = record_table->unpack(arg, 2);
  // This is ugly and error-prone.  We should provide a higher-level API which
  // understands the internal data representation for ADTs
  const souffle::RamDomain *model_tuple = record_table->unpack(my_tuple[1], 2);
  cout << my_tuple[0] << " - " << symbol_table->decode(my_tuple[0]) << " - " << ((my_tuple[1] == 0) ? 0 : my_tuple[1]) << "\n";

  souffle::RamDomain model = my_tuple[1];
  // while (true) {
  //     if (model == 0) {
  //         break;
  //     }

  //     const souffle::RamDomain* model2 = record_table->unpack(model, 2);
  //     const souffle::RamDomain* model_entry = record_table->unpack(model2[0],
  //     2);

  //     cout << "Model : " << symbol_table->decode(model_entry[0]) << " has
  //     value "  <<  model_entry[1]  << "\n";

  //     model  = model2[1];
  // }

  if (my_tuple[1] == 0) {
    return record_table->pack(&my_tuple[0], 2);
  }

  souffle::RamDomain fixed_entry[2] = {symbol_table->encode("c"), 333};
  souffle::RamDomain model2[2];
  model2[0] = record_table->pack(fixed_entry, 2);
  model2[1] = 0;

  souffle::RamDomain res[2];
  res[0] = symbol_table->encode("sat");
  res[1] = record_table->pack(&model2[0], 2);
  return record_table->pack(&res[0], 2);
}
}
