#include <souffle/SouffleInterface.h>

#include "souffle/RecordTable.h"
#include "souffle/SymbolTable.h"

extern "C" {
souffle::RamDomain print_to_smt_style(souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table, souffle::RamDomain arg,
                                      souffle::RamDomain arg_bound_vars, souffle::RamDomain let_expr_list);

souffle::RamDomain smt_response_with_model(souffle::SymbolTable *symbol_table, souffle::RecordTable *record_table, souffle::RamDomain text);
}