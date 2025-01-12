#include "souffle/SouffleFunctor.h"
#include "souffle/utility/MiscUtil.h"
#include <cassert>

#if RAM_DOMAIN_SIZE == 64
using FF_int = int64_t;
using FF_uint = uint64_t;
using FF_float = double;
#else
using FF_int = int32_t;
using FF_uint = uint32_t;
using FF_float = float;
#endif

extern "C" {
    souffle::RamDomain hashsum(souffle::SymbolTable* symbolTable, souffle::RecordTable* recordTable,
            souffle::RamDomain arg1, souffle::RamDomain arg2);
    souffle::RamDomain hash_function(const souffle::RamDomain &num);
}

souffle::RamDomain hashsum(souffle::SymbolTable* symbolTable, souffle::RecordTable* recordTable, souffle::RamDomain arg1, souffle::RamDomain arg2) {
    assert(symbolTable && "NULL symbol table");
    assert(recordTable && "NULL record table");

    // std::string result = std::to_string(arg1 + djb2(std::to_string(arg2)));
    // return arg1 + djb2(std::to_string(arg2));
    return arg1 ^ hash_function(arg2);
}

souffle::RamDomain hash_function(const souffle::RamDomain &num) {
    // unsigned long hash = 5381; // Initialize hash with a prime number
    // hash += (num * num) ^ num;
    // return hash;
    uint32_t x = static_cast<uint32_t>(num); // Ensure unsigned for consistent behavior
    x = ~x + (x << 15); // Invert and shift left
    x = x ^ (x >> 12);  // XOR with right-shifted value
    x = x + (x << 2);   // Add and shift left
    x = x ^ (x >> 4);   // XOR with right-shifted value
    x = x * 2057;       // Multiply with a prime number
    x = x ^ (x >> 16);  // Final XOR with right-shifted value
    return static_cast<int>(x); // Return as int
}
