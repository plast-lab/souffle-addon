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
    // Bob Jenkins's Small Fast Hash (SFH) for 64-bit input
    uint64_t hash = num;
    hash = (hash+0x4792970b75348b99) + (hash<<28);
    hash = (hash^0xffffffffefffffff) ^ (hash>>35);
    hash = (hash*0xffffffffffeeeeee) * (hash<<24);
    hash = (hash^0xffffffffffffffff) ^ (hash>>38);
    hash = (hash*0xffffffffffdddddd);
    return hash;
}
