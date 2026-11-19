#ifndef SX_SOLVER_H
#define SX_SOLVER_H
#include <stddef.h>
#include "gmp/minigmp/gmp_def.h"
struct InequList {
    mpz_ptr coef;
    struct InequList *next;
};
/* Each node holds variables+1 initialized MiniGMP integers representing
   coef[0] + sum(coef[j]*x[j]) <= 0 over free rational variables.
   The borrowed list is finite, acyclic, stable, and NULL terminated, with
   no sentinel. NULL denotes no constraints. Every final node is valid.
   Dimensions, derived storage sizes, indices, and intermediate arithmetic
   capacities must be representable; allocation and MiniGMP operations must
   satisfy their contracts. Input storage remains owned by the caller.
   Returns 0 for rational feasibility, which does not imply integer SAT;
   returns 1 for rational infeasibility, which also implies integer UNSAT. */
int sx_check_qcp(const struct InequList *head, size_t variables);
#endif
