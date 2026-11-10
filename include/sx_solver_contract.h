/* Public list-only solver interface; historical contracts are retained in docs. */
#ifndef SX_SOLVER_CONTRACT_H
#define SX_SOLVER_CONTRACT_H
#include "sx_arith.h"
typedef enum { SX_Q_NOT_RUN, SX_Q_FEASIBLE, SX_Q_UNSAT, SX_Q_UNKNOWN } SxQStatus;
typedef enum { SX_Z_NOT_DECIDED, SX_Z_SAT, SX_Z_UNSAT, SX_Z_UNKNOWN } SxZStatus;
typedef enum {
    SX_REASON_NONE,
    SX_REASON_FRACTIONAL,
    SX_REASON_SPACE,
    SX_REASON_LIMBS,
    SX_REASON_PIVOTS,
    SX_REASON_TIME,
    SX_REASON_CONFLICT,
    SX_REASON_ARITH_SPACE,
    SX_REASON_INVALID_INPUT,
    SX_REASON_ALLOCATION,
    SX_REASON_INTERNAL,
    SX_REASON_SIZE_OVERFLOW
} SxReason;
enum {
    SX_OPT_CONSTANT_ROWS = 1u,
    SX_OPT_CONSTANT_CONFLICT = 2u,
    SX_OPT_UNUSED_VARIABLES = 4u,
    SX_OPT_ROW_GCD = 8u,
    SX_OPT_ALL = 15u
};
/* Flags disable individual P4 transformations. 0=all enabled; ALL=P3-shaped
   reference path (with common telemetry and zero-coefficient verification skip). */
typedef struct {
    SxLimits arithmetic;
    size_t max_table_bytes, max_pivots;
    unsigned long long max_milliseconds;
    size_t fail_at; /* Unified full-call allocation injection; arithmetic.fail_at must be 0. */
    unsigned int disable_optimizations;
    int collect_matrix_stats; /* Explicit optional O(mN) snapshots; default off. */
} SxSolverLimits;
typedef struct {
    size_t pivots, allocations, peak_bytes;
    size_t comparisons, verified_rows, conflict_terms;
    size_t input_rows, input_variables, active_rows, active_variables;
    size_t input_nonzeros, input_cells, active_nonzeros, active_cells;
    size_t dropped_true_rows, removed_variables, gcd_reduced_rows, constant_conflicts;
    size_t preprocess_coefficients_scanned, verification_coefficients_skipped;
    size_t matrix_snapshots, matrix_cells_scanned, table_nonzeros, table_cells;
    size_t max_coefficient_limbs;
    SxWorkStats arithmetic;
} SxSolverStats;
typedef enum {
    SX_D_NONE,
    SX_D_ARGUMENT,
    SX_D_DIMENSION,
    SX_D_OBJECT,
    SX_D_TOTAL_BYTES,
    SX_D_ARITH_BYTES,
    SX_D_LIMBS,
    SX_D_PIVOTS,
    SX_D_TIME,
    SX_D_ALLOC,
    SX_D_INVARIANT,
    SX_D_REENTRY,
    SX_D_CLOCK,
    SX_D_OVERFLOW,
    SX_D_CYCLE
} SxDiagnostic;
typedef struct {
    size_t variable, source_row; /* SIZE_MAX means no original-row source. */
    int is_lower;
    SxRat coefficient, bound;
} SxBlocker;
typedef struct {
    int present, to_lower;
    size_t row, basic_variable, bound_source_row;
    SxRat constant, required, attainable;
    SxBlocker *blockers;
    size_t blocker_count;
} SxConflict;
typedef struct {
    SxError error;
    SxQStatus rational_status;
    SxZStatus integer_status;
    SxReason reason;
    SxRat *witness;
    size_t witness_length;
    SxSolverStats stats;
    SxDiagnostic diagnostic;
    SxArithReason arithmetic_reason;
    SxConflict conflict;
} SxResult;
/* Initialized, cleared result required. Input remains borrowed/read-only.
   Success: SX_OK + FEASIBLE/UNSAT/UNKNOWN; resource exhaustion is SX_OK with
   Q/Z UNKNOWN and precise reason. Other errors: NOT_RUN/NOT_DECIDED, no output.
   FEASIBLE publishes only an original-row verified witness. UNSAT publishes
   verified local blocking-row evidence (not a full original-constraint proof).
   Every allocation is included in the full-call limit; clear is idempotent.
   Defaults when 0: 100000 pivots, 10000 ms, 256 MiB total; finite, not unlimited.
   QCP list entry borrows the original coef/next layout, each coef has n+1
   readable project integers. NULL list is empty, cycles/NULL coef invalid. */
void sx_result_init(SxResult *out);
struct InequList;
void sx_check_qcp(const struct InequList *, size_t variables, const SxSolverLimits *,
                  SxResult *out);
void sx_result_clear(SxResult *out);
#endif
