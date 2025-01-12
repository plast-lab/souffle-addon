#include "souffle/SouffleFunctor.h"
#include "souffle/utility/MiscUtil.h"
#include <cassert>
#include <string.h>
#include <list>

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
    souffle::RamDomain list_fold(
        souffle::SymbolTable* symbolTable, souffle::RecordTable* recordTable, souffle::RamDomain list, souffle::RamDomain elem) {

        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        if (list == 0) {
            souffle::RamDomain new_list[2] = {elem, 0};
            return recordTable->pack(new_list, 2);
        }
        else {
            souffle::RamDomain innerMost[2] = {elem, 0};
            const souffle::RamDomain* myTuple1 = recordTable->unpack(list, 2);
            std::list <souffle::RamDomain> l = {};

            while (1) {
                l.push_front(myTuple1[0]);
                if (myTuple1[1] == 0)
                    break;
                myTuple1 = recordTable->unpack(myTuple1[1], 2);
            }

            souffle::RamDomain curr = recordTable->pack(innerMost, 2);
            while (l.size() > 0) {
                souffle::RamDomain temp[2] = {l.front(), curr};
                l.pop_front();
                curr = recordTable->pack(temp, 2);
            }
            return curr;
        }
    }
}