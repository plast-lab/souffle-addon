#include <souffle/SouffleInterface.h>
#include <z3++.h>

#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdlib>
#include <iostream>
#include <map>
#include <random>
#include <set>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "souffle/RecordTable.h"
#include "souffle/SymbolTable.h"

// ------------------------------------------------------------------------
// Debug helpers
// ------------------------------------------------------------------------

#define DEBUG 1
#define DEBUG_LOG_FILE "/tmp/souffle_functor_debug.log"

#ifdef DEBUG
#include <fstream>
#include <mutex>
static void debug_log(const std::string& str) {
  static std::mutex m;
  std::lock_guard<std::mutex> lock(m);
  std::ofstream log(DEBUG_LOG_FILE, std::ios::app);
  log << str << std::endl;
}
#define DEBUG_MSG(str) debug_log(str)
#else
#define DEBUG_MSG(str) \
  do {                 \
  } while (false)
#endif


// Width of every bit-vector in the encoding. EVM words are 256-bit; the 32-bit
// branch exists only for quick local experiments.
#define BIT_VEC_LENGTH 256

#if BIT_VEC_LENGTH == 256
#define RANDOM_VALUE_0 "#x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#define RANDOM_VALUE_1 "#x1123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#define RANDOM_VALUE_2 "#x2123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#define RANDOM_VALUE_3 "#x3123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#define RANDOM_VALUE_4 "#x4123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#define RANDOM_VALUE_5 "#x5123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#define RANDOM_VALUE_6 "#x6123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#else
#define RANDOM_VALUE_0 "#x01234567"
#define RANDOM_VALUE_1 "#x11234567"
#define RANDOM_VALUE_2 "#x21234567"
#define RANDOM_VALUE_3 "#x31234567"
#define RANDOM_VALUE_4 "#x41234567"
#define RANDOM_VALUE_5 "#x51234567"
#define RANDOM_VALUE_6 "#x61234567"
#endif

// Enable printing SMT queries to stderr when SMT_DEBUG is set in the environment.
static const bool smt_debug = std::getenv("SMT_DEBUG") != nullptr;

// ------------------------------------------------------------------------
// Per-thread Z3 state
//
// Souffle may evaluate functors on several OpenMP worker threads
// (`souffle -j<N>`). A z3::context is NOT thread-safe, so a single shared
// context/solver crashes (Z3 assertion violation + segfault) under parallel
// evaluation. Giving every thread its own context/solver keeps parallel
// solving while isolating Z3 state. The response caches are likewise
// per-thread: lower hit rate than a shared cache, but correct without locks.
// ------------------------------------------------------------------------

static thread_local z3::context ctx;
static thread_local z3::solver smt_solver(ctx);

static thread_local std::unordered_map<std::string, souffle::RamDomain> cache_smt_response_with_model;
static thread_local std::map<std::pair<std::string, std::set<std::string>>, souffle::RamDomain> cache_print_to_smt_style;

namespace {

// ------------------------------------------------------------------------
// Small utilities
// ------------------------------------------------------------------------

bool is_hex_literal(const std::string& s) { return s.rfind("0x", 0) == 0 || s.rfind("0X", 0) == 0; }

// Z3 prints bit-vector model values as "#x0000..00ab". Souffle-side we want
// "0xab": drop the "#x"/"0x" prefix and leading zeros (keep at least one digit).
std::string change_representation(const std::string& smt_bv_constant) {
  std::string digits = smt_bv_constant.substr(2);
  digits.erase(0, std::min(digits.find_first_not_of('0'), digits.size() - 1));
  return "0x" + digits;
}

// One of a small fixed pool of "random-ish" constants, used to pin
// FORALLSTAR-bound and caller-listed variables to a concrete value.
std::string get_random_special_value() {
  static const std::string pool[] = {RANDOM_VALUE_0, RANDOM_VALUE_1, RANDOM_VALUE_2, RANDOM_VALUE_3,
                                     RANDOM_VALUE_4, RANDOM_VALUE_5, RANDOM_VALUE_6};
  static thread_local std::mt19937 gen{std::random_device{}()};
  std::uniform_int_distribution<std::size_t> pick(0, (sizeof(pool) / sizeof(pool[0])) - 1);
  return pool[pick(gen)];
}

// Pipe-quote a symbol for SMT-LIB. `|foo|` and `foo` denote the same symbol,
// so quoting unconditionally always matches whatever z3's own printer chose
// for the same name inside the assertion body.
std::string quote_symbol(const std::string& s) {
  if (s.find('|') != std::string::npos || s.find('\\') != std::string::npos) {
    throw std::runtime_error("smt-api: symbol contains '|' or '\\', cannot encode: " + s);
  }
  return "|" + s + "|";
}

// ------------------------------------------------------------------------
// Expression tree -> Z3 AST
//
// The Souffle-side tree (Expr = [base, left, right]) is translated straight
// into z3::expr. Every value is a BIT_VEC_LENGTH-bit bit-vector. "Truthy" is
// the value 1; comparison / logical operators return 1 or 0 so they can be
// nested like any other sub-expression, matching the original encoding.
// ------------------------------------------------------------------------

struct Translator {
  z3::context& c;
  unsigned width;

  z3::expr zero;          // 0
  z3::expr one;           // 1  (canonical "true")
  z3::expr all_ones;      // -1 / 0xffff..ff
  z3::expr eight;         // 8
  z3::expr msbyte_index;  // width/8 - 1  (index of the most significant byte)
  z3::expr msbyte_mask;   // 0xff << (width - 8)

  std::map<std::string, z3::expr> free_consts;  // name -> bv const, emitted as declare-fun
  std::map<std::string, z3::expr> let_subst;    // name -> definition (inlined on use)
  std::set<std::string> pinned;                 // names constrained to a random value

  bool has_quantifier = false;  // real FORALL/EXISTS present -> logic BV
  bool uses_int_arith = false;  // EXP present (int2bv/power) -> logic ALL

  Translator(z3::context& ctx_, unsigned w)
      : c(ctx_),
        width(w),
        zero(ctx_.bv_val(0, w)),
        one(ctx_.bv_val(1, w)),
        all_ones(~ctx_.bv_val(0, w)),
        eight(ctx_.bv_val(8, w)),
        msbyte_index(ctx_.bv_val(static_cast<int>(w / 8 - 1), w)),
        msbyte_mask(z3::shl(ctx_.bv_val(0xff, w), ctx_.bv_val(static_cast<int>(w - 8), w))) {}

  z3::expr truthy(const z3::expr& cond) { return z3::ite(cond, one, zero); }

  z3::expr get_const(const std::string& name) {
    auto it = free_consts.find(name);
    if (it != free_consts.end()) return it->second;
    z3::expr e = c.bv_const(name.c_str(), width);
    free_consts.emplace(name, e);
    return e;
  }

  // "0x1a3" (any length up to width/4 hex digits) -> width-bit numeral, built
  // from 4-bit chunks so only long-stable Z3 API is used.
  z3::expr bv_from_hex(const std::string& lit) {
    std::string h;
    for (std::size_t i = (lit.size() >= 2 ? 2 : 0); i < lit.size(); ++i) {
      char ch = lit[i];
      if (!std::isxdigit(static_cast<unsigned char>(ch))) {
        throw std::runtime_error("smt-api: malformed hex literal: " + lit);
      }
      h.push_back(ch);
    }
    if (h.empty()) h = "0";
    const std::size_t max_digits = width / 4;
    if (h.size() > max_digits) h = h.substr(h.size() - max_digits);  // keep low bits

    z3::expr_vector chunks(c);
    for (char ch : h) {
      int v = (ch <= '9') ? (ch - '0') : (std::tolower(static_cast<unsigned char>(ch)) - 'a' + 10);
      chunks.push_back(c.bv_val(v, 4));
    }
    z3::expr val = z3::concat(chunks);
    unsigned bits = 4u * static_cast<unsigned>(h.size());
    if (bits < width) val = z3::zext(val, width - bits);
    return val;
  }

  z3::expr translate(souffle::SymbolTable* st, souffle::RecordTable* rt, souffle::RamDomain node,
                     const std::map<std::string, z3::expr>& bound) {
    if (node == 0) throw std::runtime_error("smt-api: unexpected nil expression node");

    const souffle::RamDomain* t = rt->unpack(node, 3);
    std::string base = st->decode(t[0]);
    const souffle::RamDomain left = t[1];
    const souffle::RamDomain right = t[2];

    // ---- leaf ----
    if (left == 0 && right == 0) {
      if (is_hex_literal(base)) return bv_from_hex(base);
      if (base.empty()) throw std::runtime_error("smt-api: empty leaf symbol");
      auto b = bound.find(base);
      if (b != bound.end()) return b->second;
      auto s = let_subst.find(base);
      if (s != let_subst.end()) return s->second;
      return get_const(base);
    }

    // ---- quantifiers ----
    if (base == "FORALL" || base == "EXISTS") {
      has_quantifier = true;
      const souffle::RamDomain* vt = rt->unpack(left, 3);
      std::string vname = st->decode(vt[0]);
      z3::expr qv = c.bv_const(vname.c_str(), width);
      std::map<std::string, z3::expr> inner(bound);
      inner.insert_or_assign(vname, qv);
      z3::expr body = translate(st, rt, right, inner);
      z3::expr q = (base == "FORALL") ? z3::forall(qv, body == one) : z3::exists(qv, body == one);
      return truthy(q);
    }
    if (base == "FORALLSTAR") {
      const souffle::RamDomain* vt = rt->unpack(left, 3);
      std::string vname = st->decode(vt[0]);
      get_const(vname);
      pinned.insert(vname);
      return translate(st, rt, right, bound);
    }

    // ---- operators ----
    z3::expr L = translate(st, rt, left, bound);
    const bool unary = (right == 0);
    z3::expr R = unary ? L : translate(st, rt, right, bound);

    if (base == "ADD") return L + R;
    if (base == "SUB") return L - R;
    if (base == "MUL" || base == "binop_mul") return L * R;
    if (base == "DIV") return z3::udiv(L, R);
    if (base == "MOD") return z3::urem(L, R);
    if (base == "SDIV") return L / R;  // bvsdiv
    if (base == "SMOD") return z3::smod(L, R);
    if (base == "AND") return L & R;
    if (base == "OR") return L | R;
    if (base == "XOR") return L ^ R;
    if (base == "NOT") return ~L;       // unary
    if (base == "UNOP_NEG") return -L;  // unary
    if (base == "SHL") return z3::shl(R, L);   // shift amount is the LEFT child
    if (base == "SHR") return z3::lshr(R, L);
    if (base == "SAR") return z3::ashr(R, L);
    if (base == "EQ") return truthy(L == R);
    if (base == "NOT_EQ") return truthy(L != R);
    if (base == "GT") return truthy(z3::ugt(L, R));
    if (base == "LT") return truthy(z3::ult(L, R));
    if (base == "GE") return truthy(z3::uge(L, R));
    if (base == "LE") return truthy(z3::ule(L, R));
    if (base == "SGT") return truthy(L > R);  // signed
    if (base == "SLT") return truthy(L < R);  // signed
    if (base == "ISZERO" || base == "UNOP_ISZERO") return truthy(L == zero);  // unary
    if (base == "ISNOTZERO") return truthy(L != zero);                        // unary
    if (base == "LAND") return z3::ite(L == zero, zero, z3::ite(R == zero, zero, one));
    if (base == "LOR") return z3::ite(L == zero, z3::ite(R == zero, zero, one), one);
    if (base == "LNOT") return z3::ite(L == zero, one, zero);  // unary
    if (base == "SHA3" || base == "SHA3_1ARG" || base == "SHA3_2ARG") return all_ones;

    if (base == "BYTE") {
      // byte L (counting from the most-significant end) of R
      z3::expr shift_up = eight * L;
      z3::expr isolated = R & z3::lshr(msbyte_mask, shift_up);
      z3::expr shift_down = eight * (msbyte_index - L);
      return z3::lshr(isolated, shift_down);
    }
    if (base == "SIGNEXTEND") {
      // sign-extend R taking byte L as the sign byte
      z3::expr move = eight * (L + one);
      z3::expr sign_bit = z3::shl(one, move - one);
      z3::expr is_neg = (R & sign_bit) != zero;
      return z3::ite(is_neg, R | z3::shl(all_ones, move), R);
    }
    if (base == "EXP") {
      uses_int_arith = true;
      z3::expr b_int(c, Z3_mk_bv2int(c, L, false));
      z3::expr e_int(c, Z3_mk_bv2int(c, R, false));
      z3::expr p(c, Z3_mk_power(c, b_int, e_int));
      z3::expr p_int = p.is_int() ? p : z3::expr(c, Z3_mk_real2int(c, p));
      return z3::expr(c, Z3_mk_int2bv(c, width, p_int));
    }

    throw std::runtime_error("smt-api: unknown operator: " + base);
  }

  // Full query text minus the pinning constraints (this is the cache key).
  std::string render_base(const z3::expr& assertion) {
    std::string logic = uses_int_arith ? "ALL" : (has_quantifier ? "BV" : "QF_BV");
    std::string out = "(set-logic " + logic + ")\n";
    for (const auto& kv : free_consts) {
      out += "(declare-fun " + quote_symbol(kv.first) + " () (_ BitVec " + std::to_string(width) + "))\n";
    }
    out += "(assert " + assertion.to_string() + ")\n";
    return out;
  }

  std::string render_pins() {
    std::string out;
    for (const auto& name : pinned) {
      out += "(assert (= " + quote_symbol(name) + " " + get_random_special_value() + "))\n";
    }
    return out;
  }
};

// let list: [ [var, expr], rest ].  Processed tail-first so the list head is
// the innermost scope -- a head binding sees every other binding, a tail
// binding sees none of them. This reproduces the original nesting, including
// the deliberate "leak" exercised by the order-sensitivity tests.
void collect_lets(Translator& tr, souffle::SymbolTable* st, souffle::RecordTable* rt, souffle::RamDomain node) {
  if (node == 0) return;
  const souffle::RamDomain* cell = rt->unpack(node, 2);
  collect_lets(tr, st, rt, cell[1]);  // outer scopes first

  const souffle::RamDomain* pair = rt->unpack(cell[0], 2);
  std::string var = st->decode(pair[0]);
  if (is_hex_literal(var)) return;  // legacy: skip 0x-named bindings
  z3::expr rhs = tr.translate(st, rt, pair[1], {});
  tr.let_subst.insert_or_assign(var, rhs);
}

// model -> list of [name, "0x..value"] record tuples
std::vector<souffle::RamDomain> model_entries(z3::solver& solver, souffle::SymbolTable* st, souffle::RecordTable* rt) {
  z3::model model = solver.get_model();
  std::vector<souffle::RamDomain> entries;
  for (unsigned i = 0; i < model.size(); ++i) {
    z3::func_decl d = model[i];
    if (d.arity() > 0) continue;  // only constants
    souffle::RamDomain entry[2];
    entry[0] = st->encode(d.name().str());
    entry[1] = st->encode(change_representation(model.get_const_interp(d).to_string()));
    entries.push_back(rt->pack(entry, 2));
  }
  return entries;
}

souffle::RamDomain to_model_list(const std::vector<souffle::RamDomain>& entries, souffle::RecordTable* rt) {
  souffle::RamDomain rest = 0;
  for (auto it = entries.rbegin(); it != entries.rend(); ++it) {
    souffle::RamDomain cell[2] = {*it, rest};
    rest = rt->pack(cell, 2);
  }
  return rest;
}

// RAII push/pop so an exception from check() can't leak a solver scope.
struct SolverScope {
  z3::solver& s;
  explicit SolverScope(z3::solver& s_) : s(s_) { s.push(); }
  ~SolverScope() { s.pop(); }
};

void traverse_model(z3::solver& solver) {
  if (!smt_debug) return;
  z3::model model = solver.get_model();
  for (unsigned i = 0; i < model.size(); ++i) {
    z3::func_decl d = model[i];
    if (d.arity() > 0) continue;
    std::cerr << d.name() << " = " << model.get_const_interp(d) << std::endl;
  }
}

}  // namespace

// ------------------------------------------------------------------------
// Souffle functor entry points
// ------------------------------------------------------------------------

extern "C" {

souffle::RamDomain print_to_smt_style(souffle::SymbolTable* symbol_table, souffle::RecordTable* record_table,
                                      souffle::RamDomain arg, souffle::RamDomain arg_bound_vars,
                                      souffle::RamDomain let_expr_list) {
  assert(symbol_table && "NULL symbol table");
  assert(record_table && "NULL record table");

  Translator tr(ctx, BIT_VEC_LENGTH);

  // caller-listed bound vars: declare and pin each
  for (souffle::RamDomain n = arg_bound_vars; n != 0;) {
    const souffle::RamDomain* cell = record_table->unpack(n, 2);
    std::string name = symbol_table->decode(cell[0]);
    tr.get_const(name);
    tr.pinned.insert(name);
    n = cell[1];
  }

  collect_lets(tr, symbol_table, record_table, let_expr_list);

  z3::expr assertion = tr.translate(symbol_table, record_table, arg, {}) == tr.one;

  std::string base = tr.render_base(assertion);
  std::pair<std::string, std::set<std::string>> key(base, tr.pinned);

  auto hit = cache_print_to_smt_style.find(key);
  if (hit != cache_print_to_smt_style.end()) return hit->second;

  std::string full = base + tr.render_pins();
  souffle::RamDomain encoded = symbol_table->encode(full);
  cache_print_to_smt_style.emplace(std::move(key), encoded);
  return encoded;
}

souffle::RamDomain smt_response_with_model(souffle::SymbolTable* symbol_table, souffle::RecordTable* record_table,
                                          souffle::RamDomain text) {
  const std::string& query = symbol_table->decode(text);

  auto cached = cache_smt_response_with_model.find(query);
  if (cached != cache_smt_response_with_model.end()) return cached->second;

  DEBUG_MSG(query);

  bool parse_ok = true;
  SolverScope scope(smt_solver);
  try {
    smt_solver.from_string(query.c_str());
  } catch (const z3::exception& ex) {
    parse_ok = false;
    std::cerr << "smt-api: invalid SMT query: " << ex.msg() << std::endl;
  }

  z3::check_result verdict = parse_ok ? smt_solver.check() : z3::unknown;
  const char* tag = (verdict == z3::unsat) ? "unsat" : (verdict == z3::sat) ? "sat" : "unknown";

  DEBUG_MSG(std::string("Result: ") + tag);

  std::vector<souffle::RamDomain> assignments;
  souffle::RamDomain res[2];
  res[0] = symbol_table->encode(tag);
  if (verdict == z3::sat) {
    DEBUG_MSG(std::string("Model: ") + smt_solver.get_model().to_string());
    assignments = model_entries(smt_solver, symbol_table, record_table);
    res[1] = to_model_list(assignments, record_table);
  } else {
    res[1] = 0;
  }
  souffle::RamDomain result = record_table->pack(res, 2);

  if (parse_ok) cache_smt_response_with_model.emplace(query, result);

  if (smt_debug) {
    std::cerr << "(push)\n" << query << "(check-sat) ; " << tag << std::endl;
    if (verdict == z3::sat) {
      std::cerr << "(get-model) ; ";
      for (souffle::RamDomain entry : assignments) {
        const souffle::RamDomain* tup = record_table->unpack(entry, 2);
        std::cerr << symbol_table->decode(tup[0]) << " = " << symbol_table->decode(tup[1]) << " ";
      }
      std::cerr << "\n(pop)" << std::endl;
    }
  }
  return result;
}

const char* smt_response_simple(const char* query) {
  z3::context local_ctx;
  z3::solver local_solver(local_ctx);
  local_solver.from_string(query);

  const char* result;
  switch (local_solver.check()) {
    case z3::unsat:
      result = "unsat";
      break;
    case z3::sat:
      traverse_model(local_solver);
      result = "sat";
      break;
    default:
      result = "unknown";
      break;
  }
  if (smt_debug) std::cerr << query << "(check-sat) ; " << result << std::endl;
  return result;
}

}  // extern "C"
