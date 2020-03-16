// A data structure and API for maintaining and manipulating maps of
// dependencies. These come from a Datalog program analysis and are
// treated opaquely. They are supposed to be mappings of variables to
// expressions.

#include <string.h>
#include <vector>
#include <unordered_map>
#include <map>
#include <memory>
#include <mutex>
#include <openssl/md5.h>
#include <stdio.h>
#include <stdlib.h>
#include <x86intrin.h>

using namespace std;

#define PTR_TO_INT(x) (unsigned int) ((long)(x) % 0xffffffff)

unsigned char* short_hash(const char* data1, const char* data2 = "") {
    string buf(data1);
    buf.append(data2);
    unsigned char* md5 = new unsigned char[MD5_DIGEST_LENGTH];
    MD5((const unsigned char*) buf.c_str(), buf.length(), md5);

    unsigned char* result = new unsigned char[4];
    for (int i=0; i < 4; i++) result[i] = 0;
    
    for (int i = 0; i < MD5_DIGEST_LENGTH; i++) {
      result[i * 4 / MD5_DIGEST_LENGTH] ^= md5[i];
    }

    delete md5;
    return result;
}

struct uint256 {
  __m256i value;

  uint256() { }

  inline uint256(const __m256i v) : value(v) {}
  
  static uint256 from_uint_64(const u_int64_t v) {
    __m256i value;
    value = _mm256_xor_si256(value, value); // set all 0s
    u_int64_t *val_arr = (u_int64_t*) &value;
    val_arr[3] = v;
    return uint256(value);
  }

  // all zeros except bit number
  static uint256 from_onehot(const unsigned char bit_no) {
    __m256i value;
    value = _mm256_xor_si256(value, value); // set all 0s
    u_int64_t t = 1 << (bit_no % 64);
    u_int64_t *val_arr = (u_int64_t*) &value;
    val_arr[bit_no / 64] = t;
    return uint256(value);
  }

  inline uint256 operator|(const uint256 other) const {
    return uint256(_mm256_or_si256(value, other.value));
  }

  inline uint256 operator|=(const uint256 other) {
    value = _mm256_or_si256(value, other.value);
    return *this;
  }
  
  inline uint256 operator&(const uint256 other) const {
    return uint256(_mm256_and_si256(value, other.value));
  }

  inline uint256 operator^(const uint256 other) const {
    return uint256(_mm256_xor_si256(value, other.value));
  }

  inline uint256 operator^=(const uint256 other) {
    value = _mm256_xor_si256(value, other.value);
    return *this;
  }
  
  inline bool operator==(const uint256 other) const {
    __m256i temp = _mm256_cmpeq_epi64(value, other.value);
    // swap low/high words in each dword
    temp &=  _mm256_permute4x64_epi64(temp, 0b10110001); 
    // swap low and high dwords
    temp &= _mm256_permute2x128_si256(temp, temp, 0b00000001);
    return ((u_int32_t*) &temp)[7];
  }

  inline u_int64_t hash() const {
    __m256i temp = value;
    // swap low/high words in each dword
    temp ^=  _mm256_permute4x64_epi64(temp, 0b10110001); 
    // swap low and high dwords
    temp ^= _mm256_permute2x128_si256(temp, temp, 0b00000001);
    return ((u_int64_t*) &temp)[3];
  }
  
  inline u_int32_t count_bits() const {
    auto v = (u_int64_t*) &value;
    return __builtin_popcount(v[0]) +
           __builtin_popcount(v[1]) +
           __builtin_popcount(v[2]) +
           __builtin_popcount(v[3]);
  }
  
  inline u_int64_t to_uint64() const {
    return ((u_int64_t*) &value)[3];
  }
  
};

struct MappingNodes {
    uint256 keys;
    uint256 values;

    MappingNodes() {}

    MappingNodes(const char* _key, const char* _val_id) {
       const unsigned char* md5hash_key = short_hash(_key);
       const unsigned char* md5hash_val = short_hash(_key, _val_id);

       keys = uint256::from_onehot(md5hash_key[0]) |
              uint256::from_onehot(md5hash_key[1]) |
              uint256::from_onehot(md5hash_key[2]); 
       
       values = uint256::from_onehot(md5hash_val[0]) |
                uint256::from_onehot(md5hash_val[1]) |
                uint256::from_onehot(md5hash_val[2]); 

       delete md5hash_key;
       delete md5hash_val;
     }


     MappingNodes(const uint256 _keys, const uint256 _values) :
       keys(_keys), values(_values) { }

     inline MappingNodes* combine_strict(const MappingNodes& m) {
       /*printf("keys: %d ; values: %d ; diff1: %d ; diff2: %d \n",
              (int) (keys | m.keys).count_bits(),
              (int) (values | m.values).count_bits(),
              (int) (keys ^ values).count_bits(),
              (int) (m.keys ^ m.values).count_bits()
              );*/
       int n_intersection_keys = (keys & m.keys).count_bits() / 3 * 3;
       if (n_intersection_keys == 0 ||
           (values & m.values).count_bits() >= n_intersection_keys) {
         return new MappingNodes(keys | m.keys, values | m.values);

       }
       return nullptr;
     }
  
     inline MappingNodes combine_loose(const MappingNodes& m) {
       return MappingNodes(keys | m.keys, values | m.values);
     }

     size_t size() {
       return (keys.count_bits() + values.count_bits()) / 6;
     }

     inline bool operator==(const MappingNodes& rhs) const {
        return values == rhs.values && keys == rhs.keys; 
     }

    struct Hash {
      inline size_t operator()(const MappingNodes& mappings) const {
         return mappings.values.hash();
      }
   };

};

#define COLID_TO_INDEX(i) (i-1)
#define INDEX_TO_COLID(i) (i+1)
// index cannot be zero (special value), so we use one-plus
// the real index as an id.

// A dictionary of mapping collections. Added linearly, retrievable by
// their addition index, but also quickly indexed by the MappingsCol
// objects' hash.
extern "C" {
    static vector<MappingNodes> mappings_seq;

    // REVIEW: is the number type big enough for all future uses?
    static unordered_map<MappingNodes, int32_t, MappingNodes::Hash> all_mappings;
    
    static std::mutex mappings_lock;

    // creates (if not existent) an empty mapping and returns its sequential index
    int32_t empty_mapping() {
        MappingNodes m;
        lock_guard<mutex> lock(mappings_lock);
        auto got = all_mappings.find(m);
        if (got != all_mappings.end()) {
            return got->second;
        }
        // it's a new one, need to add it to both structures
        int32_t col_id = INDEX_TO_COLID(mappings_seq.size());
        mappings_seq.push_back(m);
        all_mappings[m] = col_id;
        return col_id;
    }
    
    // creates (if not existent) a singleton mapping and returns its
    // sequential index
    int32_t singleton_mapping(const char* key, const char* val_id, const char* val_text) {
        MappingNodes m(key, val_id);

        std::lock_guard<std::mutex> lock(mappings_lock);

        auto got = all_mappings.find(m);
        if (got != all_mappings.end()) {
            return got->second;
        }
        // it's a new one, need to add it to both structures
        int32_t col_id = INDEX_TO_COLID(mappings_seq.size());
        mappings_seq.push_back(m);
        all_mappings[m] = col_id;
        return col_id;
    }

    // Combine two mappings-collections to create a new one. If the
    // two collections disagree at any element (i.e., both contain a
    // mapping for a key, but with different value) zero is returned.
    // If the resulting collection exists, the existing entry is returned.
    int32_t combine_strict(int32_t map1_id, int32_t map2_id) {

        if (map1_id == 0 || map2_id == 0)
            return 0;
        if (map1_id == map2_id)
            return map1_id;

        
        lock_guard<mutex> lock(mappings_lock);
        
        MappingNodes& m1 = mappings_seq.at(COLID_TO_INDEX(map1_id));
        MappingNodes& m2 = mappings_seq.at(COLID_TO_INDEX(map2_id));  

        auto new_map = unique_ptr<MappingNodes>(m1.combine_strict(m2));

        if (!new_map) return 0;
        
        auto got = all_mappings.find(*new_map.get());
        if (got != all_mappings.end()) {
            return got->second;
        }
        // it's a new one, need to add it to both structures
        int32_t new_map_id = INDEX_TO_COLID(mappings_seq.size());
        mappings_seq.push_back(*new_map.get());
        all_mappings[*new_map.get()] = new_map_id;
        return new_map_id;
    }

    
    // Combine two mappings-collections to create a new one. If the
    // two collections disagree at any element (i.e., both contain a
    // mapping for a key, but with different value) both mappings are removed!
    // If the resulting collection exists, the existing entry is returned.
    int32_t combine_loose(int32_t map1_id, int32_t map2_id) {

        if (map1_id == 0 || map2_id == 0)
            return 0;

        if (map1_id == map2_id)
            return map1_id;

        std::lock_guard<std::mutex> lock(mappings_lock);

        MappingNodes& m1 = mappings_seq.at(COLID_TO_INDEX(map1_id));
        MappingNodes& m2 = mappings_seq.at(COLID_TO_INDEX(map2_id));  // both have to exist

        MappingNodes new_map(m1.combine_loose(m2));

        auto got = all_mappings.find(new_map);
        if (got != all_mappings.end()) {
            return got->second;
        }
        // it's a new one, need to add it to both structures
        int32_t new_map_id = INDEX_TO_COLID(mappings_seq.size());
        mappings_seq.push_back(new_map);
        all_mappings[new_map] = new_map_id;
        return new_map_id;
    }
    

    // returns uninterned strings, should only be used for reporting
    const char* mapcol_to_string(int32_t map_id) {
      return "todo";
    }

}
