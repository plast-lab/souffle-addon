#include <cassert>
#include <cstring>
#include <list>
#include <mutex>
#include <utility>
#include <fstream>
#include <iostream>

#define PTR_TO_INT(x) (uint32_t) ((long)(x) % 0xffffffff)

using Tick = int32_t;
using Key = const char*;
using Value = const char*;
using HashTriplet = std::tuple<Tick, Key, Value>;
using Bucket = std::list<HashTriplet>;

// TODO: Add tests.
class Hash {
    uint32_t no_buckets;
    Bucket* table;

public:
    Hash(uint32_t _no_buckets) : no_buckets(_no_buckets) {
        table = new Bucket[no_buckets];
    }

    ~Hash() {
        delete[] table;
    }

    void insert(Tick _tick, Key _key, Value _value) {
        size_t hash = PTR_TO_INT(_key);
        Bucket& bucket = table[hash % no_buckets];

        // The tick of the bucketlist's front should be greater than the tick
	// of every other elemement in the bucketlist. This also helps with
	// double insertion of the same element due to the functor evaluating
	// twich in the same rule.
        if (bucket.size() > 0 && std::get<0>(bucket.front()) >= _tick) {
            return;
        }

        table[hash % no_buckets].emplace_front(_tick, _key, _value);
    }

    Value get(Tick _tick, Key _key) {
        uint32_t hash = PTR_TO_INT(_key);
        Bucket& bucket = table[hash % no_buckets];

        for (auto const& [tick, key, value] : bucket) {
            if (key == _key && _tick >= tick) {
                return value;
            }
        }

        assert(false);
    }
};

extern "C" {
    static struct Hash ht(1024);
    static std::mutex ht_lock;

    int32_t init_state(void) {
        return 0;
    }

    Tick update_state(Tick _tick, Key _key, Value _value) {
        std::lock_guard<std::mutex> lock(ht_lock);
        ht.insert(_tick, _key, _value);
        return _tick+1;
    }

    Value get_state(Tick _tick, Key _key) {
        std::lock_guard<std::mutex> lock(ht_lock);
        return ht.get(_tick, _key);
    }

    Tick no_update_state(Tick _tick) {
        return _tick+1;
    }
}
