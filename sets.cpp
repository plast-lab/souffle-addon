//
// Sets are immutable once created. A set handle is a symbol "S<id>" whose id
// indexes an internal table. Because handles are fully determined by the id,
// no symbol->id map is needed — the id is parsed back out of the symbol.
//

#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <string>
#include <shared_mutex>
#include <cstdint>
#include <cstdio>
#include <sstream>
#include <mutex>

// ---------------------------------------------------------------------
// Storage
//
// Invariant: entries in `table` are write-once. Once allocSet publishes an
// entry, its contents never change. Therefore readers only ever race with the
// *writer* (allocSet growing the containers), never with each other — which is
// exactly what shared_mutex is for: many concurrent readers, one exclusive
// writer.
// ---------------------------------------------------------------------
struct SetEntry {
    std::unordered_set<std::string> elems;
    uint64_t contentHash;
};

// id -> set
static std::vector<SetEntry> table;
// hash -> every id that hashed here (usually exactly one)
static std::unordered_map<uint64_t, std::vector<int32_t>> contentIntern;
static std::shared_mutex mu;

static inline uint64_t hashStr(const std::string& s) {
    // FNV-1a
    uint64_t h = 1469598103934665603ULL;
    for (unsigned char c : s) { h ^= c; h *= 1099511628211ULL; }
    return h;
}

// splitmix64 finalizer — spreads each element's bits before combining, so the
// plain XOR below doesn't suffer from structured/linear element hashes.
static inline uint64_t finalize(uint64_t h) {
    h ^= h >> 30; h *= 0xbf58476d1ce4e5b9ULL;
    h ^= h >> 27; h *= 0x94d049bb133111ebULL;
    h ^= h >> 31;
    return h;
}

// Commutative AND associative: order of insertion cannot affect the result.
static inline uint64_t mixOrderIndependent(uint64_t acc, uint64_t elemHash) {
    return acc ^ finalize(elemHash);
}

// Parse "S<digits>" back to an id; -1 on any malformed input.
static int32_t parseId(const char* sym) {
    if (!sym || sym[0] != 'S' || sym[1] == '\0') return -1;
    int64_t v = 0;
    for (const char* p = sym + 1; *p; ++p) {
        if (*p < '0' || *p > '9') return -1;
        v = v * 10 + (*p - '0');
        if (v > INT32_MAX) return -1;
    }
    return (int32_t)v;
}

static std::string mintSymbol(int32_t id) {
    return "S" + std::to_string(id);
}

// The sole writer. Dedups on exact content, else appends. Exclusive lock.
static int32_t allocSet(std::unordered_set<std::string> elems, uint64_t contentHash) {
    std::unique_lock lk(mu);
    auto& bucket = contentIntern[contentHash]; // creates empty vector on first sight
    for (int32_t existing : bucket) {
        if (table[existing].elems == elems) return existing;
    }
    table.push_back({std::move(elems), contentHash});
    int32_t id = (int32_t)table.size() - 1;
    bucket.push_back(id); // add alongside any colliders
    return id;
}

// ---------------------------------------------------------------------
// Functors
// ---------------------------------------------------------------------
extern "C" {

// empty_set() : symbol
// Magic static: exactly-once, thread-safe init with no explicit locking, and
// the resulting symbol string is computed once and reused forever.
const char* empty_set() {
    static const std::string sym = [] {
        return mintSymbol(allocSet(std::unordered_set<std::string>{}, 0));
    }();
    return sym.c_str();
}

// add_set(symbol set, symbol elem) : symbol
const char* add_set(const char* setSym, const char* elem) {
    int32_t id = parseId(setSym);
    std::string e(elem);

    std::unordered_set<std::string> copy;
    uint64_t h = 0;
    bool alreadyPresent = false;

    // Single shared lock covers both the membership check and the copy, so we
    // only copy when the element is genuinely new.
    {
        std::shared_lock lk(mu);
        if (id >= 0 && id < (int32_t)table.size()) {
            const SetEntry& entry = table[id];
            if (entry.elems.count(e)) {
                alreadyPresent = true;
            } else {
                copy = entry.elems;      // O(n) copy, only on the new-element path
                h = entry.contentHash;
            }
        }
    }

    // Adding an element already in the set yields the same set
    static thread_local std::string buf;
    if (alreadyPresent) { buf = setSym; return buf.c_str(); }

    copy.insert(e);
    h = mixOrderIndependent(h, hashStr(e));
    buf = mintSymbol(allocSet(std::move(copy), h));
    return buf.c_str();
}

// in_set(symbol set, symbol elem) : number   -- O(1) avg, shared lock
int32_t in_set(const char* setSym, const char* elem) {
    int32_t id = parseId(setSym);
    if (id < 0) return 0;
    std::shared_lock lk(mu);
    if (id >= (int32_t)table.size()) return 0;
    return table[id].elems.count(elem) ? 1 : 0;
}

// len_set(symbol set) : number   -- O(1), shared lock
int32_t len_set(const char* setSym) {
    int32_t id = parseId(setSym);
    if (id < 0) return 0;
    std::shared_lock lk(mu);
    if (id >= (int32_t)table.size()) return 0;
    return (int32_t)table[id].elems.size();
}

// set_to_string(symbol set) : symbol   -- debugging / witness output
const char* set_to_string(const char* setSym) {
    int32_t id = parseId(setSym);
    static thread_local std::string buf;

    std::ostringstream oss;
    oss << "{";
    {
        std::shared_lock lk(mu);
        if (id >= 0 && id < (int32_t)table.size()) {
            bool first = true;
            for (const auto& e : table[id].elems) {
                if (!first) oss << ",";
                oss << e;
                first = false;
            }
        }
    }
    oss << "}";
    buf = oss.str();
    return buf.c_str();
}

// set_eq(symbol a, symbol b) : number   -- O(1)
// Relies on content dedup: identical sets always share one id, so id equality is set equality.
int32_t set_eq(const char* aSym, const char* bSym) {
    int32_t a = parseId(aSym);
    int32_t b = parseId(bSym);
    if (a < 0 || b < 0) return 0;
    std::shared_lock lk(mu);
    int32_t n = (int32_t)table.size();
    if (a >= n || b >= n) return 0;
    return (a == b) ? 1 : 0;
}

// union_set(symbol a, symbol b) : symbol
const char* union_set(const char* aSym, const char* bSym) {
    int32_t aId = parseId(aSym);
    int32_t bId = parseId(bSym);

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