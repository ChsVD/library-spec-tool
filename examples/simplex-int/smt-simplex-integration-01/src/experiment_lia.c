#include "experiment_lia.h"
#include "../simplex/simplex.h"
#include <limits.h>

/* Inputs are the original LIA conjunction after SMT preprocessing.
   eq is caller-owned, ineq is a private copy handed to the LIA engine. */
int experiment_lia(InequList *eq, InequList *ineq, int *used, int n,
                   int i8, int i16, int i32, int i64) {
    int rows[SX_ROWS][SX_INPUT_VARS + 1] = {{0}}, m = 0;
    struct SxState st;
    const char *reason = NULL;
    if (n < 0 || n > SX_INPUT_VARS) reason = "variable_capacity";
    else if (i8 >= 0 || i16 >= 0 || i32 >= 0 || i64 >= 0) reason = "special_constant";
    for (int e = 0; e < 2 && !reason; ++e) {
        for (const InequList *p = e ? eq : ineq; p && p->next; p = p->next) {
            if (p->strict != (e ? 0 : -1)) { reason = "relation"; break; }
            if (m + 1 + e > SX_ROWS) { reason = "row_capacity"; break; }
            for (int j = 0; j <= n; ++j) {
                if (p->coef[j] == INT_MIN) { reason = "coefficient_range"; break; }
                rows[m][j] = p->coef[j];
                if (e) rows[m+1][j] = -p->coef[j];
            }
            if (reason) break;
            m += 1 + e;
        }
    }
    if (!reason) {
        int status = sx_check(&st, m, n, rows, 10000);
        if (status == SX_UNSAT) {
            fprintf(stderr,"TRACE simplex unsat rows=%d vars=%d\n",m,n);
            free_InequList(ineq);
            return 0;
        }
        reason = "simplex_unknown";
        if (status == SX_FEASIBLE) {
            reason = NULL;
            for (int j = 0; j < n; ++j)
                if (st.value[j].den != 1) reason = "fractional_witness";
            for (int e = 0; e < 2 && !reason; ++e)
                for (const InequList *p = e ? eq : ineq; p && p->next; p = p->next) {
                    __int128 sum = p->coef[0];
                    for (int j = 0; j < n; ++j)
                        sum += (__int128)p->coef[j+1] * st.value[j].num;
                    if (e ? sum != 0 : sum > 0) { reason = "witness_check"; break; }
                }
            if (!reason) {
                fprintf(stderr,"TRACE simplex integer_witness rows=%d vars=%d\n",m,n);
                free_InequList(ineq);
                return 1;
            }
        }
    }
    fprintf(stderr,"TRACE fallback %s\n",reason);
    return lia_theory_deduction(eq,ineq,used,n,i8,i16,i32,i64);
}
