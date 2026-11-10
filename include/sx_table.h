#ifndef SX_TABLE_H
#define SX_TABLE_H
#include "sx_solver_contract.h"
/* Lower-level P2 table operations, also used by internal preprocessing.
   This header is not a top-level feasibility-checking API. */
/* Row-major borrowed integer coefficients: row [constant, x0, ..., x(n-1)].
   Each object is a valid initialized project MiniGMP integer, not system GMP. */
typedef struct {
    size_t rows, variables;
    const __mpz_struct *coefficients;
} SxProblem;
typedef struct SxTable SxTable;
struct InequList;
typedef enum {
    SX_T_NONE,
    SX_T_ARGUMENT,
    SX_T_DIMENSION,
    SX_T_OBJECT,
    SX_T_CYCLE,
    SX_T_TOTAL_BYTES,
    SX_T_ARITH_BYTES,
    SX_T_LIMBS,
    SX_T_OVERFLOW,
    SX_T_ALLOC,
    SX_T_BOUND,
    SX_T_PIVOT,
    SX_T_INVARIANT,
    SX_T_REENTRY
} SxTableReason;
typedef struct {
    SxLimits arithmetic;
    size_t max_table_bytes, fail_at;
} SxTableLimits;
typedef struct {
    SxTableReason reason;
    SxArithReason arithmetic_reason;
    size_t allocations, peak_table_bytes, retained_table_bytes;
} SxTableStats;
/* Create requires *out==NULL. Flat input rows are [constant,x0,...].
   All row/limb storage must really be readable; pointers cannot prove length.
   QCP nodes have original fields mpz_ptr coef; struct InequList *next.
   Every coef has variables+1 readable initialized integers, no extra metadata. */
SxError sx_table_create(SxTable **out, const SxProblem *, const SxTableLimits *, SxTableStats *);
SxError sx_table_create_qcp(SxTable **out, const struct InequList *, size_t variables,
                            const SxTableLimits *, SxTableStats *);
void sx_table_destroy(SxTable *);
/* Mutations replace *table on success only. Every borrowed pointer is invalid
   after successful mutation/destroy. Failed calls preserve table and pointers.
   Objects belong to one thread, cannot be shallow-copied or transferred. */
SxError sx_table_bounds(SxTable **table, size_t variable, const SxRat *lower, const SxRat *upper,
                        const SxTableLimits *, SxTableStats *);
SxError sx_table_move(SxTable **table, size_t nonbasic, const SxRat *value, const SxTableLimits *,
                      SxTableStats *);
/* Select a violated basic row; to_lower is 1 for lower, 0 for upper.
   Entering variable is nonbasic and has a nonzero legal repair direction.
   New basic may violate a bound; departing basic is set to chosen bound. */
SxError sx_table_pivot(SxTable **table, size_t row, size_t entering, int to_lower,
                       const SxTableLimits *, SxTableStats *);
SxError sx_table_recompute(SxTable **table, const SxTableLimits *, SxTableStats *);
/* Exact structural/canonical/equation/equivalence/nonbasic-bound checks;
   mismatch is SX_INTERNAL, resource failure preserves distinct diagnostics. */
SxError sx_table_check(const SxTable *, const SxTableLimits *, SxTableStats *);
size_t sx_table_rows(const SxTable *);
size_t sx_table_variables(const SxTable *); /* original + expressions */
size_t sx_table_original_variables(const SxTable *);
size_t sx_table_basic(const SxTable *, size_t row); /* SIZE_MAX on bad index */
size_t sx_table_nonbasic(const SxTable *, size_t column);
size_t sx_table_basic_row(const SxTable *, size_t variable); /* SIZE_MAX if nonbasic */
size_t sx_table_nonbasic_column(const SxTable *, size_t variable);
const SxRat *sx_table_beta(const SxTable *, size_t row);
const SxRat *sx_table_coefficient(const SxTable *, size_t row, size_t variable);
const SxRat *sx_table_value(const SxTable *, size_t variable);
const SxRat *sx_table_lower(const SxTable *, size_t variable); /* NULL means absent */
const SxRat *sx_table_upper(const SxTable *, size_t variable);
size_t sx_table_bytes(const SxTable *); /* retained charge incl allocation headers */
#endif
