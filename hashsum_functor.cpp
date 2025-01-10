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
    unsigned long djb2(const std::string &str);
}

souffle::RamDomain hashsum(souffle::SymbolTable* symbolTable, souffle::RecordTable* recordTable, souffle::RamDomain arg1, souffle::RamDomain arg2) {
    assert(symbolTable && "NULL symbol table");
    assert(recordTable && "NULL record table");

    std::string result = std::to_string(arg1 + djb2(std::to_string(arg2)));
    //return arg1 + djb2(std::to_string(arg2));
    return arg1 + djb2(std::to_string(arg2));
}

unsigned long djb2(const std::string &str) {
    unsigned long hash = 5381; // Initialize hash with a prime number
    for (char c : str) {
        // Multiply hash by 33 and add the current character
        hash = ((hash << 5) + hash) + c; // hash * 33 + c
    }
    return hash;
}
