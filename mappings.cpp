// A data structure and API for maintaining and manipulating maps of
// dependencies. These come from a Datalog program analysis and are
// treated opaquely. They are supposed to be mappings of variables to
// expressions.

#include <string.h>
#include <vector>
#include <unordered_map>
#include <iostream>
#include <mutex>
using namespace std;

// Quick, rusty C++, Java-like naming
// Also, I'm lazy and making everything public, so that the functors can
// directly access, rather than add accessors and combining ops.
struct MappingNode {
    const char* key;
    const char* val_id;
    const char* val_text; // val ids are enough for data structure
                          // correctness, but the text is so that the
                          // C++ side can print humanly-consumable
                          // information. Should be a function of val_id
    unsigned int hash;

    MappingNode() {}

    MappingNode(const char* _key, const char* _val_id, const char* _val_text) :
        key(_key), val_id(_val_id), val_text(_val_text)
    {
        hash = 0;
        // rudimentary hash
        for (const char* i = key; *i != '\0'; i++)
            hash += *i;
        for (const char* i = val_id; *i != '\0'; i++)
            hash += *i;
    }

    bool operator==(const MappingNode& rhs) const {
        return key == rhs.key && val_id == rhs.val_id; // strings should come interned
        //        return (strcmp(key, rhs.key) == 0) && (strcmp(val_id, rhs.val_id) == 0);
    }

};



// A collection of mapping nodes, i.e., a multimap, implemented as a linear
// sequence.

// This is a lightweight class. Its objects are often passed around by-value.
struct MappingsCol {
    const unsigned int size;
    const MappingNode* contents;
     // an array is fine for now. Never resized (new collections are
     // created). "contents" not owned by the collection!
      // REVIEW: a smart pointer would be perfect here, for now we are
      // just careful to delete in the same routine as allocating, if
      // we detect the mapping is invalid.
    unsigned int hash;

    MappingsCol(const int _size, const MappingNode *_contents) : size(_size), contents(_contents) {
        hash = 0;
        for (int i = 0; i < size; i++) {
            hash += contents[i].hash;
        }
    }

    bool operator==(const MappingsCol& rhs) const {
        if (hash != rhs.hash || size != rhs.size) {
            return false;
        }
        for (int i = 0; i < size; i++) {
            if (!(contents[i] == rhs.contents[i]))
                return false;
        }
        return true;
    }

    struct Hash {
        size_t operator()(const MappingsCol& mappings) const {            
            return size_t(mappings.hash);
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
    static vector<MappingsCol> mappings_seq;

    // REVIEW: is the number type big enough for all future uses?
    static unordered_map<MappingsCol, int32_t, MappingsCol::Hash> all_mappings;

    static std::mutex mappings_lock;

    // creates (if not existent) an empty mapping and returns its sequential index
    int32_t empty_mapping() {
        std::lock_guard<std::mutex> lock(mappings_lock);
        MappingsCol m(0,nullptr);
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
        std::lock_guard<std::mutex> lock(mappings_lock);
        MappingNode *mn = new MappingNode(key, val_id, val_text);
        MappingsCol m(1,mn);
        auto got = all_mappings.find(m);
        if (got != all_mappings.end()) {
            delete mn;
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
        
        std::lock_guard<std::mutex> lock(mappings_lock);
        MappingsCol& m1 = mappings_seq.at(COLID_TO_INDEX(map1_id));
        MappingsCol& m2 = mappings_seq.at(COLID_TO_INDEX(map2_id));  // both have to exist

        // First traversal: see if they agree, figure out resulting size
        int new_size = 0;
        {
            int index1 = 0, index2 = 0;
            while (index1 < m1.size && index2 < m2.size) {
                int comp = strcmp(m1.contents[index1].key, m2.contents[index2].key);
                if (comp == 0) {
                    if (m1.contents[index1].val_id != m2.contents[index2].val_id)
                        return 0;  // mappings don't agree on same key!
                    else {
                        index1++;
                        index2++;
                    }
                } else if (comp < 0) {
                    index1++;
                } else {
                    index2++;
                }
                new_size++;
            }
            // no conflict detected
            if (index1 < m1.size)
                new_size += m1.size - index1;
            else if (index2 < m2.size)
                new_size += m2.size - index2;
        }
            
        MappingNode *new_contents = new MappingNode[new_size];
        // Second traversal: fill in new contents by merging
        // REVIEW: if too slow, consider single traversal but larger
        // up-front allocation
        {
            int index1 = 0, index2 = 0;
            int index = 0;
            while (index1 < m1.size && index2 < m2.size) {
                int comp = strcmp(m1.contents[index1].key, m2.contents[index2].key);
                if (comp == 0) {
                    new_contents[index] = m1.contents[index1];
                    index1++;
                    index2++;
                } else if (comp < 0) {
                    new_contents[index] = m1.contents[index1];
                    index1++;
                } else {
                    new_contents[index] = m2.contents[index2];
                    index2++;
                }
                index++;
            }
            for ( ; index1 < m1.size; index1++)
                new_contents[index++] = m1.contents[index1];
            for ( ; index2 < m2.size; index2++)
                new_contents[index++] = m2.contents[index2];
        }
        MappingsCol new_map(new_size, new_contents);

        auto got = all_mappings.find(new_map);
        if (got != all_mappings.end()) {
            delete new_contents;
            return got->second;
        }
        // it's a new one, need to add it to both structures
        int32_t new_map_id = INDEX_TO_COLID(mappings_seq.size());
        mappings_seq.push_back(new_map);
        all_mappings[new_map] = new_map_id;
        return new_map_id;
    }

    
    // Combine two mappings-collections to create a new one. If the
    // two collections disagree at any element (i.e., both contain a
    // mapping for a key, but with different value) both mappings are removed!
    // If the resulting collection exists, the existing entry is returned.
    int32_t combine_loose(int32_t map1_id, int32_t map2_id) {
        if (map1_id == 0 || map2_id == 0)
            return 0;
        
        std::lock_guard<std::mutex> lock(mappings_lock);
        MappingsCol& m1 = mappings_seq.at(COLID_TO_INDEX(map1_id));
        MappingsCol& m2 = mappings_seq.at(COLID_TO_INDEX(map2_id));  // both have to exist

        // First traversal: see if they agree, figure out resulting size
        int new_size = 0;
        {
            int index1 = 0, index2 = 0;
            while (index1 < m1.size && index2 < m2.size) {
                int comp = strcmp(m1.contents[index1].key, m2.contents[index2].key);
                if (comp == 0) {
                    bool remove = m1.contents[index1].val_id != m2.contents[index2].val_id;
                      // mappings don't agree on same key, will remove both
                    index1++;
                    index2++;
                    if (remove) continue;
                } else if (comp < 0) {
                    index1++;
                } else {
                    index2++;
                }
                new_size++;
            }
            if (index1 < m1.size)
                new_size += m1.size - index1;
            else if (index2 < m2.size)
                new_size += m2.size - index2;
        }
            
        MappingNode *new_contents = new MappingNode[new_size];
        // Second traversal: fill in new contents by merging
        // REVIEW: if too slow, consider single traversal but larger
        // up-front allocation
        {
            int index1 = 0, index2 = 0;
            int index = 0;
            while (index1 < m1.size && index2 < m2.size) {
                int comp_key = strcmp(m1.contents[index1].key, m2.contents[index2].key);
                if (comp_key == 0) {
                    const MappingNode& possibleContents = m1.contents[index1];
                    int comp_val = strcmp(possibleContents.val_id, m2.contents[index2].val_id);
                    index1++;
                    index2++;                    
                    if (comp_val != 0)
                        continue;  // skip copying
                    else {
                        new_contents[index] = possibleContents;
                    }                     
                } else if (comp_key < 0) {
                    new_contents[index] = m1.contents[index1];
                    index1++;
                } else {
                    new_contents[index] = m2.contents[index2];
                    index2++;
                }
                index++;
            }
            for ( ; index1 < m1.size; index1++)
                new_contents[index++] = m1.contents[index1];
            for ( ; index2 < m2.size; index2++)
                new_contents[index++] = m2.contents[index2];
        }
        MappingsCol new_map(new_size, new_contents);

        auto got = all_mappings.find(new_map);
        if (got != all_mappings.end()) {
            delete new_contents;
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
        MappingsCol& m1 = mappings_seq.at(COLID_TO_INDEX(map_id));
        string accum = "[";
        for (int i = 0; i < m1.size; i++) {
            //            if (strcmp(m1.contents[i].key, "") != 0) {  // don't print mappings with empty keys
                accum += "[";
                accum += m1.contents[i].key;
                accum += " -> ";
                accum += m1.contents[i].val_text;
                accum += "]";
                //            }
        }
        accum += "]";
        char* out = new char[accum.length() + 1];
        strcpy(out, accum.c_str());
        //        cout << accum.c_str() << endl;
        return out;
    }

}
    
