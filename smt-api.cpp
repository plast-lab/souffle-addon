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

extern "C" {
z3::context c;
z3::solver s(c);

std::map<string, string> encoded_variable_names;

bool isPredefinedFunction(string op) {
  if (op == "isZero" || op == "byte" || op == "signextend" || op == "my_exp" || op == "my_bvshl" || op == "my_bvashr" || op == "my_bvlshr" || op == "my_eq" ||
      op == "my_bvgt" || op == "my_bvsgt" || op == "my_bvlt" || op == "my_bvslt" || op == "sha3" || op == "sha3_1arg" || op == "sha3_2arg") {
    return false;
  } else {
    return true;
  }
}

string inline_user_defined_function(string op, string lexpr, string rexpr) {
  if (op == "isZero") {
    return "(ite (= " + lexpr +
           " #x0000000000000000000000000000000000000000000000000000000000000000)"
           " #x0000000000000000000000000000000000000000000000000000000000000001"
           " #x0000000000000000000000000000000000000000000000000000000000000000"
           ")";
  }
  if (op == "byte") {
    return "(let ("
           " (move (bvmul #x0000000000000000000000000000000000000000000000000000000000000008  " +
           lexpr +
           " ))"
           " )"
           " (bvlshr (bvand " +
           rexpr +
           " (bvlshr #xff00000000000000000000000000000000000000000000000000000000000000 move)) (bvmul "
           "#x0000000000000000000000000000000000000000000000000000000000000008 (bvsub #x000000000000000000000000000000000000000000000000000000000000001f " +
           lexpr +
           ")) )"
           ")";
  }
  if (op == "signextend") {
    return "(let ("
           "(move (bvmul #x0000000000000000000000000000000000000000000000000000000000000008 (bvadd " +
           lexpr +
           " #x0000000000000000000000000000000000000000000000000000000000000001 )))"
           ")"
           "(ite (= #x0000000000000000000000000000000000000000000000000000000000000000"
           "        (bvand " +
           rexpr +
           " (bvshl #x0000000000000000000000000000000000000000000000000000000000000001 (bvsub move "
           "#x0000000000000000000000000000000000000000000000000000000000000001 ))))"
           " " +
           rexpr +
           " "
           "(bvor " +
           rexpr +
           " (bvshl #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff move)))"
           ")";
  }
  if (op == "my_exp") {
    return "((_ int2bv 256) (to_int (^ (bv2int " + lexpr + ") (bv2int " + rexpr + "))) )";
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
  if (op == "my_eq") {
    return "(ite (= " + lexpr + " " + rexpr +
           ")"
           " #x0000000000000000000000000000000000000000000000000000000000000001"
           " #x0000000000000000000000000000000000000000000000000000000000000000"
           ")";
  }
  if (op == "my_bvgt") {
    return "(ite (bvugt " + lexpr + " " + rexpr +
           ")"
           " #x0000000000000000000000000000000000000000000000000000000000000001"
           " #x0000000000000000000000000000000000000000000000000000000000000000"
           ")";
  }
  if (op == "my_bvsgt") {
    return "(ite (bvsgt " + lexpr + " " + rexpr +
           ")"
           " #x0000000000000000000000000000000000000000000000000000000000000001"
           " #x0000000000000000000000000000000000000000000000000000000000000000"
           ")";
  }
  if (op == "my_bvlt") {
    return "(ite (bvult " + lexpr + " " + rexpr +
           ")"
           " #x0000000000000000000000000000000000000000000000000000000000000001"
           " #x0000000000000000000000000000000000000000000000000000000000000000"
           ")";
  }
  if (op == "my_bvslt") {
    return "(ite (bvslt " + lexpr + " " + rexpr +
           ")"
           " #x0000000000000000000000000000000000000000000000000000000000000001"
           " #x0000000000000000000000000000000000000000000000000000000000000000"
           ")";
  }
  if (op == "sha3") {
    return "#xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
  }
  if (op == "sha3_1arg") {
    return "#xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
  }
  if (op == "sha3_2arg") {
    return "#xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
  }
  throw op;
}

string change_representation(string smt_bv_constant) {
  string symbolic_constant = smt_bv_constant;
  string substring = symbolic_constant.substr(2, symbolic_constant.length());
  substring.erase(0, std::min(substring.find_first_not_of('0'), substring.size() - 1));
  return "0x" + substring;
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
  // str of the for 0x____, with <= hex_len hex digits

  if (str.length() > hex_len + 2) {
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

std::list<souffle::RamDomain> get_list_of_model_entries(solver s, souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table) {
  model m = s.get_model();
  std::list<souffle::RamDomain> entry_list = {};
  // traversing the model
  for (unsigned i = 0; i < m.size(); i++) {
    func_decl v = m[i];
    // skip functions from the model parsing
    // we only care for the variable-constants of the model
    if (v.arity() > 0) continue;
    souffle::RamDomain model_entry[2];
    string trimmed_variable_name = v.name().str();

    string original_variable_name = encoded_variable_names.at(trimmed_variable_name);

    model_entry[0] = symbol_table->encode(original_variable_name);
    string value = m.get_const_interp(v).to_string();
    string changed_value = change_representation(value);
    model_entry[1] = symbol_table->encode(changed_value);

    entry_list.push_front(record_table->pack(model_entry, 2));
  }
  // we can evaluate expressions in the model.
  // std::cout << "x + y + 1 = " << m.eval(x + y + 1) << "\n";
  return entry_list;
}

// hash<string> hasher;
unordered_map<string, souffle::RamDomain> cache_smt_response_with_model = {};
souffle::RamDomain smt_response_with_model(souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table, souffle::RamDomain text) {
  const std::string &stext = symbol_table->decode(text);

  if (cache_smt_response_with_model.find(stext) != cache_smt_response_with_model.end()) {
    // we have already make this computation once!
    return cache_smt_response_with_model.at(stext);
  }

  DEBUG_MSG(stext);

  souffle::RamDomain res[2];
  std::list<souffle::RamDomain> l;

  s.push();
  s.from_string((
                    // define_functions_prologue+
                    stext)
                    .c_str());
  z3::check_result solver_result = s.check();
  s.pop();

  souffle::RamDomain result;
  switch (solver_result) {
    case unsat:
      res[0] = symbol_table->encode("unsat");
      res[1] = 0;
      result = record_table->pack(&res[0], 2);
      cache_smt_response_with_model[stext] = result;
      return result;
    case sat:
      // DEBUG_MSG(s.get_model());

      l = get_list_of_model_entries(s, symbol_table, record_table);

      // for (list<souffle::RamDomain>::iterator i = l.begin(); i != l.end(); ++i){
      //     DEBUG_MSG(symbol_table->decode(record_table->unpack(*i, 2)[0]));
      //     DEBUG_MSG(symbol_table->decode(record_table->unpack(*i, 2)[1]));
      // }
      res[0] = symbol_table->encode("sat");
      res[1] = map_list_to_tuples(l, record_table);
      result = record_table->pack(&res[0], 2);
      cache_smt_response_with_model[stext] = result;
      return result;
    default:
      res[0] = symbol_table->encode("uknown");
      res[1] = 0;
      result = record_table->pack(&res[0], 2);
      cache_smt_response_with_model[stext] = result;
      return result;
  }
}

std::set<string> global_set_for_vars = {};
std::set<string> global_set_for_bounded_vars = {};
std::map<string, string> operator_mapping = {};

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

  random_device rd;                                      // obtain a random number from hardware
  mt19937 gen(rd());                                     // seed the generator
  uniform_int_distribution<> distr(0, pool.size() - 1);  // define the range

  int random_index = distr(gen);
  return pool.at(random_index);
}

string make_constraint_for_bounded_var(string var) {
  string value = get_random_special_value();
  return "(assert (= " + var + " " + value + "))";
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

string parse_tree_expr_for_bounded_vars(souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table, souffle::RamDomain arg) {
  // We expect a sequence of 0 or more forall* quantifiers in the start of an expression and nowhere else

  if (arg == 0) {
    return "";
  }

  const souffle::RamDomain *my_tuple = record_table->unpack(arg, 3);

  const souffle::RamDomain left = my_tuple[1];
  const souffle::RamDomain right = my_tuple[2];
  bool is_leaf = (left == 0 && right == 0);

  string root_symbol = symbol_table->decode(my_tuple[0]);
  if (is_leaf) {
    if (root_symbol.rfind("0x", 0) == 0) {
      throw std::invalid_argument("cant bound constant");
    } else {
      return root_symbol;
    }
  }

  if (root_symbol == "FORALLSTAR") {
    string variable_to_bound = parse_tree_expr_for_bounded_vars(symbol_table, record_table, left);
    global_set_for_bounded_vars.insert(variable_to_bound);
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
  bool is_leaf = (left == 0 && right == 0);

  string root_symbol = symbol_table->decode(my_tuple[0]);
  DEBUG_MSG(root_symbol);
  if (is_leaf) {
    if (root_symbol.rfind("0x", 0) == 0) {
      //     uint256_t parsed_hex(root_symbol);
      //     cout << "MY x : " << parsed_hex << endl;

      root_symbol = fix_length(root_symbol, 64);
      // root_symbol = parsed_hex.str();
      // replace 0x prefix with #x ....
      root_symbol[0] = '#';
    } else {
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

  if (root_symbol == "FORALLSTAR") {
    parse_tree_expr(symbol_table, record_table, left);  // to add "bounded" variable in globalSetVars
    return parse_tree_expr(symbol_table, record_table, right);
  }

  if (root_symbol == "FORALL") {
    // "(forall ((x (_ BitVec 256))) P)"
    string lsymbol = parse_tree_expr(symbol_table, record_table, left);
    string rexpr = parse_tree_expr(symbol_table, record_table, right);
    string ans = "(forall ((" + lsymbol + " (_ BitVec 256))) " + rexpr + ")";
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
      // do the inlineing of the user-definfed functions
      ans = inline_user_defined_function(op, lexpr, rexpr);
    }
  }
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

map<pair<std::string, set<std::string>>, souffle::RamDomain> cache_print_to_smt_style;

/**
 * Implement smt-lib mapping!
 */
souffle::RamDomain print_to_smt_style(souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table, souffle::RamDomain arg,
                                      souffle::RamDomain arg_bound_vars) {
  // TODO: global sets have to be cleared in every print_to_smt call, since we bound
  global_set_for_bounded_vars.clear();
  global_set_for_vars.clear();

  assert(symbol_table && "NULL symbol table");
  assert(record_table && "NULL record table");

  global_set_for_vars.clear();
  global_set_for_bounded_vars.clear();
  populate_operator_mapping();

  string out = parse_tree_expr(symbol_table, record_table, arg);
  parse_tree_expr_for_bounded_vars(symbol_table, record_table, arg);

  add_bounded_variables(symbol_table, record_table, arg_bound_vars);

  string declarations = "";
  for (string s : global_set_for_vars) {
    declarations += "(declare-const " + s + " (_ BitVec 256))\n";
  }

  const souffle::RamDomain *my_tuple = record_table->unpack(arg, 3);
  string root_symbol = symbol_table->decode(my_tuple[0]);

  string result;
  // if (root_symbol == "SUB") ....
  result = declarations + "( assert (= #x0000000000000000000000000000000000000000000000000000000000000001 " + out + ") )\n";

  string result_with_constraints = result;

  pair<std::string, set<std::string>> key = make_pair(result_with_constraints, global_set_for_bounded_vars);

  if (cache_print_to_smt_style.find(key) != cache_print_to_smt_style.end()) {
    // we have already made this computation once!
    return cache_print_to_smt_style.at(key);
  }

  for (string s : global_set_for_bounded_vars) {
    result_with_constraints += make_constraint_for_bounded_var(s);
  }
  souffle::RamDomain encoded_result = symbol_table->encode(result_with_constraints);
  cache_print_to_smt_style[key] = encoded_result;
  return encoded_result;
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
  //     const souffle::RamDomain* model_entry = record_table->unpack(model2[0], 2);

  //     cout << "Model : " << symbol_table->decode(model_entry[0]) << " has value "  <<  model_entry[1]  << "\n";

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
