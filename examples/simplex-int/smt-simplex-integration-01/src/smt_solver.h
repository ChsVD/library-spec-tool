#ifndef SMT_SOLVER_H
#define SMT_SOLVER_H 1
#include "smt_lang.h"
#include"nelson_oppen.h"

//0:unsat, 1:sat, -1: 永真
int smt_solver(SmtProp* p);

#endif