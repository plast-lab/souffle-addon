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
souffle::RamDomain lub(souffle::SymbolTable* symbolTable, souffle::RecordTable* recordTable,
        souffle::RamDomain i1, souffle::RamDomain i2);
souffle::RamDomain lub_number(souffle::SymbolTable* symbolTable, souffle::RecordTable* recordTable,
        souffle::RamDomain i, souffle::RamDomain x);
}

souffle::RamDomain lub(souffle::SymbolTable*, souffle::RecordTable* recordTable, souffle::RamDomain i1,
        souffle::RamDomain i2) {
    const souffle::RamDomain* interval1 = recordTable->unpack(i1, 2);
    const souffle::RamDomain* interval2 = recordTable->unpack(i2, 2);
    auto lb = std::min(interval1[0], interval2[0]);
    auto ub = std::max(interval1[1], interval2[1]);
    const souffle::RamDomain res[2] = {lb, ub};
    return recordTable->pack(res, 2);
}

souffle::RamDomain lub_number(souffle::SymbolTable*, souffle::RecordTable* recordTable, souffle::RamDomain i,
        souffle::RamDomain x) {
    const souffle::RamDomain* interval = recordTable->unpack(i, 2);
    auto lb = std::min(interval[0], x);
    auto ub = std::max(interval[1], x);
    const souffle::RamDomain res[2] = {lb, ub};
    return recordTable->pack(res, 2);
}