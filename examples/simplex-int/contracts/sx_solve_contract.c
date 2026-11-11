/* Independently proved sx_solve interface.
 * Run simplex_solve-20261104112017; independent final-check done/passed/errors[].
 * Exact checked bounded execution with partial failure states, fixed entrance A,
 * actual rational FEASIBLE witness and unrestricted rational UNSAT.
 * negative_budget needs no s pointee; normal_state has actual initialized origin.
 * Native a stride24; logical400 slots are not one C array. Inactive cells frame.
 * Unknown permissions do not assert old bytes or initialization tags.
 * This file is a declaration/contract, with no duplicate callee declarations.
 */
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

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_pivot.simplex_pivot_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_solve.simplex_solve_lib */
/*@ Extern Coq (simplex_solve_snapshot :: *) */
/*@ Extern Coq
 (simplex_pivot_memory : Z -> Z -> Z -> list Z -> list Z -> Assertion)
*/
/*@ Extern Coq
 (simplex_solve_pack : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> simplex_solve_snapshot)
 (simplex_solve_normal : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> simplex_solve_snapshot -> Prop)
 (simplex_solve_origin : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> simplex_solve_snapshot -> Prop)
 (simplex_solve_result : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
 (simplex_solve_witness : list Z -> Z -> Z -> list Z -> list Z -> Prop)
 (simplex_solve_unsat : list Z -> Z -> Z -> Prop)
 (simplex_solve_variables : Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Assertion)
*/
int sx_solve(struct SxState *s, int pivot_limit)
/*@ negative_budget
 With L
 Require pivot_limit == L && -2147483648 <= L && L < 0
 Ensure __return == -1
*/
/*@ normal_state
 With S L M I V (A N D B IB HL HU LN LD UN UD VN VD : list Z)
 Require s == S && pivot_limit == L && 0 <= L && L <= 2147483647 &&
 0 <= M && M <= 16 && 0 <= I && I <= 8 && V == M+I && 0 <= V && V <= 24 &&
 Zlength(N) == 400 && Zlength(D) == 400 && Zlength(B) == M &&
 Zlength(IB) == V && Zlength(HL) == V && Zlength(HU) == V &&
 Zlength(LN) == V && Zlength(LD) == V && Zlength(UN) == V && Zlength(UD) == V &&
 Zlength(VN) == V && Zlength(VD) == V &&
 (forall (i: Z) (j: Z), (0 <= i && i < M && 0 <= j && j <= I) =>
   (-2147483647 <= Znth(i*9+j,A,0) && Znth(i*9+j,A,0) <= 2147483647)) &&
 simplex_solve_normal(A,HL,HU,LN,LD,UN,UD,M,I,simplex_solve_pack(N,D,B,IB,VN,VD)) &&
 simplex_solve_origin(A,HL,HU,LN,LD,UN,UD,M,I,simplex_solve_pack(N,D,B,IB,VN,VD)) &&
 store(&(s->rows),M) * store(&(s->vars),V) * store(&(s->inputs),I) *
 IntArray::full(s->basic,M,B) * IntArray::full(s->is_basic,V,IB) *
 simplex_pivot_memory(s,M,V,N,D) * simplex_solve_variables(s,V,HL,HU,VN,VD,LN,LD,UN,UD)
 Ensure exists ON OD OB OIB OVN OVD,
 (__return == -1 || __return == 0 || __return == 1) &&
 simplex_solve_result(HL,HU,LN,LD,UN,UD,M,V,L,N,D,B,IB,VN,VD,__return,ON,OD,OB,OIB,OVN,OVD) &&
 (__return != -1 =>
   (simplex_solve_normal(A,HL,HU,LN,LD,UN,UD,M,I,simplex_solve_pack(ON,OD,OB,OIB,OVN,OVD)) &&
    simplex_solve_origin(A,HL,HU,LN,LD,UN,UD,M,I,simplex_solve_pack(ON,OD,OB,OIB,OVN,OVD)))) &&
 (__return == 0 => simplex_solve_witness(A,M,I,OVN,OVD)) &&
 (__return == 1 => simplex_solve_unsat(A,M,I)) &&
 store(&(((struct SxState *)S)->rows),M) * store(&(((struct SxState *)S)->vars),V) *
 store(&(((struct SxState *)S)->inputs),I) *
 IntArray::full(((struct SxState *)S)->basic,M,OB) * IntArray::full(((struct SxState *)S)->is_basic,V,OIB) *
 simplex_pivot_memory(S,M,V,ON,OD) * simplex_solve_variables(S,V,HL,HU,OVN,OVD,LN,LD,UN,UD)
*/
;
