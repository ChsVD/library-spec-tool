#ifndef QCP_SIMPLEX_H
#define QCP_SIMPLEX_H

/* Experimental limits, not mathematical restrictions of Simplex. */
#define SX_INPUT_VARS 8
#define SX_ROWS 16
#define SX_VARS (SX_INPUT_VARS + SX_ROWS)
#define SX_UNKNOWN (-1)
#define SX_FEASIBLE 0
#define SX_UNSAT 1

struct SxRat { int num; int den; };

/* Same null-terminated representation as QCP's fme.c (no sentinel node). */
struct InequList { int *coef; struct InequList *next; };

/* row i: basic[i] = rhs[i] + sum_j a[i][j] * value[j].
 * All basic-variable columns are zero. Nonbasic values satisfy their bounds.
 * Successful arithmetic produces reduced fractions with positive denominators.
 */
struct SxState {
    int rows, vars, inputs;
    int basic[SX_ROWS];
    int is_basic[SX_VARS];
    int has_lower[SX_VARS], has_upper[SX_VARS];
    struct SxRat lower[SX_VARS], upper[SX_VARS], value[SX_VARS];
    struct SxRat rhs[SX_ROWS], a[SX_ROWS][SX_VARS];
};

/* Input rows: c[i][0] + sum_j c[i][j+1] * x[j] <= 0.
 * Input arrays must have the declared C dimensions. No ownership transfer.
 * On UNKNOWN the state may be partially updated: reinitialize before reuse.
 * On FEASIBLE value[0..inputs) is an exact rational witness, NOT an integer
 * witness. UNSAT excludes rational solutions and therefore integer solutions.
 */
int sx_initialize(struct SxState *s, int rows, int inputs,
                  const int c[SX_ROWS][SX_INPUT_VARS + 1]);
int sx_recompute(struct SxState *s);
int sx_find_violation(struct SxState *s, int *row, int *direction);
int sx_find_entering(struct SxState *s, int row, int direction, int *entering);
int sx_pivot(struct SxState *s, int row, int entering);
int sx_solve(struct SxState *s, int pivot_limit);
int sx_check(struct SxState *s, int rows, int inputs,
             const int c[SX_ROWS][SX_INPUT_VARS + 1], int pivot_limit);
/* Read-only adapter. Each node owns/readably references inputs+1 coefficients.
 * Caller must supply valid nodes/arrays; no list memory is modified or freed.
 * More than SX_ROWS nodes (including a cycle) yields UNKNOWN.
 */
int simplex_deduction(struct SxState *s, const struct InequList *list,
                       int inputs, int pivot_limit);

#endif
