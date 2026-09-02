// set_functors.cpp
//
// Soufflé functors:
//   .functor empty_set(): symbol
//   .functor add_set(symbol, symbol): symbol
//   .functor in_set(symbol, symbol): number
//   .functor len_set(symbol): number
//   .functor set_to_string(symbol): symbol
//   .functor set_eq(symbol, symbol): number
//   .functor union_set(symbol, symbol): symbol
//
// NOTE: verify the exact C ABI your installed Soufflé version expects for
// symbol-typed functor params/returns (raw const char* vs. stateful/
// SymbolTable-based) before linking this in — it has changed across
// versions. Adjust signatures accordingly if needed.

#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <string>
#include <shared_mutex>
#include <mutex>
#include <cstdint>
#include <sstream>

// ---------------------------------------------------------------------
// Storage
// ---------------------------------------------------------------------
struct SetEntry {
    std::unordered_set<std::string> elems;
    uint64_t contentHash;
};

static std::vector<SetEntry> table;                          // internal id -> set
static std::unordered_map<std::string, int32_t> symToId;     // "S42" -> 42
static std::unordered_map<uint64_t, int32_t> contentIntern;  // contentHash -> id (dedup)
static std::shared_mutex mu;

static inline uint64_t hashStr(const std::string& s) {
    // FNV-1a
    uint64_t h = 1469598103934665603ULL;
    for (unsigned char c : s) { h ^= c; h *= 1099511628211ULL; }
    return h;
}

static inline uint64_t mixOrderIndependent(uint64_t acc, uint64_t elemHash) {
    // commutative/associative mix so set content hash doesn't depend on insertion order
    return acc ^ (elemHash + 0x9e3779b97f4a7c15ULL + (acc << 6) + (acc >> 2));
}

static int32_t resolveId(const std::string& sym) {
    std::shared_lock lk(mu);
    auto it = symToId.find(sym);
    return it == symToId.end() ? -1 : it->second;
}

static std::string mintSymbol(int32_t id) {
    return "S" + std::to_string(id);
}

// allocate a fresh id for a given set body, deduping on exact content match
static int32_t allocSet(std::unordered_set<std::string> elems, uint64_t contentHash) {
    std::unique_lock lk(mu); // exclusive — mutates table/symToId/contentIntern
    auto it = contentIntern.find(contentHash);
    if (it != contentIntern.end() && table[it->second].elems == elems) {
        return it->second;
    }
    table.push_back({std::move(elems), contentHash});
    int32_t id = (int32_t)table.size() - 1;
    contentIntern[contentHash] = id;
    symToId[mintSymbol(id)] = id;
    return id;
}

// ---------------------------------------------------------------------
// Functors
// ---------------------------------------------------------------------
extern "C" {

// empty_set() : symbol
const char* empty_set() {
    // Magic static: thread-safe, exactly-once initialization, no explicit locking,
    // and the string is computed once and reused for the lifetime of the process.
    static const std::string sym = [] {
        int32_t id = allocSet(std::unordered_set<std::string>{}, 0);
        return mintSymbol(id);
    }();
    return sym.c_str();
}

// add_set(symbol set, symbol elem) : symbol
const char* add_set(const char* setSym, const char* elem) {
    int32_t id = resolveId(setSym);

    std::unordered_set<std::string> copy;
    uint64_t h = 0;
    if (id != -1) {
        std::shared_lock lk(mu);
        copy = table[id].elems;      // O(n) copy
        h = table[id].contentHash;
    }

    std::string e(elem);
    if (copy.insert(e).second) {     // only changes hash if actually new
        h = mixOrderIndependent(h, hashStr(e));
    }

    int32_t newId = allocSet(std::move(copy), h);

    static thread_local std::string buf;
    buf = mintSymbol(newId);
    return buf.c_str();
}

// in_set(symbol set, symbol elem) : number
int32_t in_set(const char* setSym, const char* elem) {
    int32_t id = resolveId(setSym);
    if (id == -1) return 0;
    std::shared_lock lk(mu);
    return table[id].elems.count(elem) ? 1 : 0;
}

// len_set(symbol set) : number
int32_t len_set(const char* setSym) {
    int32_t id = resolveId(setSym);
    if (id == -1) return 0;
    std::shared_lock lk(mu);
    return (int32_t)table[id].elems.size();
}

// set_to_string(symbol set) : symbol   -- debugging / witness output
const char* set_to_string(const char* setSym) {
    int32_t id = resolveId(setSym);
    static thread_local std::string buf;
    if (id == -1) { buf = "{}"; return buf.c_str(); }

    std::ostringstream oss;
    oss << "{";
    {
        std::shared_lock lk(mu);
        bool first = true;
        for (const auto& e : table[id].elems) {
            if (!first) oss << ",";
            oss << e;
            first = false;
        }
    }
    oss << "}";
    buf = oss.str();
    return buf.c_str();
}

// set_eq(symbol a, symbol b) : number   -- O(1): same content-id iff same set
int32_t set_eq(const char* aSym, const char* bSym) {
    int32_t a = resolveId(aSym);
    int32_t b = resolveId(bSym);
    return (a == b && a != -1) ? 1 : 0;
}

// union_set(symbol a, symbol b) : symbol
const char* union_set(const char* aSym, const char* bSym) {
    int32_t aId = resolveId(aSym);
    int32_t bId = resolveId(bSym);

    std::unordered_set<std::string> merged;
    {
        std::shared_lock lk(mu);
        int32_t n = (int32_t)table.size();
        if (aId >= 0 && aId < n) merged = table[aId].elems;
        if (bId >= 0 && bId < n)
            for (const auto& e : table[bId].elems) merged.insert(e);
    }

    uint64_t h = 0;
    for (const auto& e : merged) h = mixOrderIndependent(h, hashStr(e));

    static thread_local std::string buf;
    buf = mintSymbol(allocSet(std::move(merged), h));
    return buf.c_str();
}

} // extern "C"