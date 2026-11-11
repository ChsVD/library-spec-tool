/* Independently proved sx_check interface.
 * Run simplex_check-20261104154530; independent final-check done/passed/errors[].
 * All six named branches, exact checked result/state and rational soundness.
 * Mixed known/unknown old state and inactive input/state frame preserved.
 * Unknown permission does not assert byte or initialization-tag snapshots.
 * No duplicate callee function declarations.
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

/*@ Extern Coq (Forall : {A} -> (A -> Prop) -> list A -> Prop) (Z::le : Z -> Z -> Prop) (Z::ge : Z -> Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_initialize.simplex_initialize_lib */
/*@ Extern Coq
 (simplex_init_return : Z -> Z -> Prop)
 (simplex_init_bounds : Z -> Z -> Z -> Z -> Assertion)
 (simplex_init_unreachable : Z -> Z -> Prop)
 (simplex_init_value_at : list Z -> Z -> Z -> Z -> Z)
 (simplex_init_basic : Z -> Z -> list Z) (simplex_init_flags : Z -> Z -> list Z)
 (simplex_init_rhs : list Z -> Z -> list Z) (simplex_init_an : list Z -> Z -> Z -> list Z)
 (simplex_init_zeroes : Z -> list Z) (simplex_init_ones : Z -> list Z)
 (simplex_init_input : Z -> list Z -> Z -> Z -> Assertion)
 (simplex_init_input_except : Z -> list Z -> Z -> Z -> Z -> Z -> Assertion)
 (simplex_init_vars : Z -> Z -> Z -> Z -> Z -> list Z -> Z -> Assertion)
 (simplex_init_vars_except : Z -> Z -> Z -> Z -> Z -> list Z -> Z -> Z -> Assertion)
 (simplex_init_rows : Z -> list Z -> Z -> Z -> Z -> Z -> Assertion)
 (simplex_init_rows_except : Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Assertion)
 (simplex_init_a_row : Z -> list Z -> Z -> Z -> Z -> Z -> Assertion)
 (simplex_init_a_row_except : Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Assertion)
 (simplex_init_coeff : list Z -> Z -> Z -> Z -> Z)
*/
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
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_check.simplex_check_lib */
/*@ Extern Coq (simplex_check_memory_snapshot :: *) */
/*@ Extern Coq
 (simplex_init_values : list Z -> Z -> Z -> list Z)
 (simplex_check_initial_num : list Z -> Z -> Z -> list Z)
 (simplex_check_old : Z -> Z -> Z -> simplex_check_memory_snapshot -> Assertion)
 (simplex_check_frame : Z -> Z -> Z -> simplex_check_memory_snapshot -> Assertion)
 (simplex_check_input_frame : Z -> Z -> Z -> simplex_check_memory_snapshot -> Assertion)
 (simplex_check_rejected_result : list Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_check_result : list Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
*/
/*@ Extern Coq (simplex_check_invalid_dimensions : Z -> Z -> Prop) */

int sx_check(struct SxState *s, int rows, int inputs,
             const int c[SX_ROWS][SX_INPUT_VARS + 1], int pivot_limit)
/*@ check_invalid_dimensions
 With M N S C L
 Require s == S && c == C && rows == M && inputs == N && pivot_limit == L &&
 (M < 0 || M > 16 || N < 0 || N > 8) && emp
 Ensure __return == -1 && emp
*/
/*@ check_rejected_coefficient
 With (A : list Z) M N S C L
 Require s == S && c == C && rows == M && inputs == N && pivot_limit == L &&
 0 <= M && M <= 16 && 0 <= N && N <= 8 &&
 Zlength(A) == M*9 && Forall(Z::le(-2147483648),A) && Forall(Z::ge(2147483647),A) &&
 (exists (x: Z) (y: Z), 0 <= x && x < M && 0 <= y && y <= N && Znth(x*9+y,A,0) == -2147483648) &&
 simplex_init_input(C,A,M,N)
 Ensure __return == -1 && simplex_check_rejected_result(A,M,N,L,__return) && simplex_init_input(C,A,M,N)
*/
/*@ zero_negative_budget
 With N S C L (Old : simplex_check_memory_snapshot)
 Require s == S && c == C && inputs == N && pivot_limit == L && rows == 0 && 0 <= N && N <= 8 && -2147483648 <= L && L < 0 &&
 simplex_check_old(S,0,N,Old) * simplex_check_frame(S,0,N,Old)
 Ensure __return == -1 && simplex_check_result(nil,0,N,L,__return,simplex_check_initial_num(nil,0,N),simplex_init_ones(400),simplex_init_basic(N,0),simplex_init_flags(N,0+N),simplex_init_values(nil,0,N),simplex_init_ones(0+N)) && store(&(((struct SxState *)S)->rows), 0) * store(&(((struct SxState *)S)->inputs), N) * store(&(((struct SxState *)S)->vars), 0+N) * simplex_init_vars(S,N,0+N,0,0+N,simplex_init_rhs(nil,0),1) * simplex_init_rows(S,nil,N,0,0,0+N) * simplex_check_frame(S,0,N,Old)
*/
/* Zero rows with nonnegative budget returns FEASIBLE(0):
 * simplex_init_return(ret,0) is definitionally ret=0. Its opaque spelling
 * defers the impossible solver-code branches to genuine proof obligations. */
/*@ zero_normal_budget
 With N S C L (Old : simplex_check_memory_snapshot)
 Require s == S && c == C && inputs == N && pivot_limit == L && rows == 0 && 0 <= N && N <= 8 && 0 <= L && L <= 2147483647 &&
 simplex_check_old(S,0,N,Old) * simplex_check_frame(S,0,N,Old)
 Ensure exists ON OD OB OIB OVN OVD,
 simplex_init_return(__return,0) &&
 (__return == -1 || __return == 0 || __return == 1) &&
 simplex_check_result(nil,0,N,L,__return,ON,OD,OB,OIB,OVN,OVD) &&
 (__return == 0 => simplex_solve_witness(nil,0,N,OVN,OVD)) &&
 (__return == 1 => simplex_solve_unsat(nil,0,N)) &&
 (__return != -1 => (simplex_solve_normal(nil,simplex_init_zeroes(0+N),simplex_init_flags(N,0+N),simplex_init_zeroes(0+N),simplex_init_ones(0+N),simplex_init_zeroes(0+N),simplex_init_ones(0+N),0,N,simplex_solve_pack(ON,OD,OB,OIB,OVN,OVD)) && simplex_solve_origin(nil,simplex_init_zeroes(0+N),simplex_init_flags(N,0+N),simplex_init_zeroes(0+N),simplex_init_ones(0+N),simplex_init_zeroes(0+N),simplex_init_ones(0+N),0,N,simplex_solve_pack(ON,OD,OB,OIB,OVN,OVD)))) &&
 store(&(((struct SxState *)S)->rows),0) * store(&(((struct SxState *)S)->inputs),N) *
 store(&(((struct SxState *)S)->vars),0+N) *
 IntArray::full(((struct SxState *)S)->basic,0,OB) *
 IntArray::full(((struct SxState *)S)->is_basic,0+N,OIB) *
 simplex_pivot_memory(S,0,0+N,ON,OD) *
 simplex_solve_variables(S,0+N,simplex_init_zeroes(0+N),simplex_init_flags(N,0+N),OVN,OVD,simplex_init_zeroes(0+N),simplex_init_ones(0+N),simplex_init_zeroes(0+N),simplex_init_ones(0+N)) * simplex_check_frame(S,0,N,Old)
*/
/*@ matrix_negative_budget
 With (A : list Z) M N S C L (Old : simplex_check_memory_snapshot) (CO : simplex_check_memory_snapshot)
 Require s == S && c == C && inputs == N && pivot_limit == L && rows == M && 1 <= M && M <= 16 && 0 <= N && N <= 8 && Zlength(A) == M*9 && Forall(Z::le(-2147483647),A) && Forall(Z::ge(2147483647),A) && -2147483648 <= L && L < 0 &&
 simplex_check_old(S,M,N,Old) * simplex_check_frame(S,M,N,Old) * simplex_init_input(C,A,M,N) * simplex_check_input_frame(C,M,N,CO)
 Ensure __return == -1 && simplex_check_result(A,M,N,L,__return,simplex_check_initial_num(A,M,N),simplex_init_ones(400),simplex_init_basic(N,M),simplex_init_flags(N,M+N),simplex_init_values(A,M,N),simplex_init_ones(M+N)) && store(&(((struct SxState *)S)->rows), M) * store(&(((struct SxState *)S)->inputs), N) * store(&(((struct SxState *)S)->vars), M+N) * simplex_init_vars(S,N,M+N,M,M+N,simplex_init_rhs(A,M),1) * simplex_init_rows(S,A,N,M,M,M+N) * simplex_check_frame(S,M,N,Old) * simplex_init_input(C,A,M,N) * simplex_check_input_frame(C,M,N,CO)
*/
/*@ matrix_normal_budget
 With (A : list Z) M N S C L (Old : simplex_check_memory_snapshot) (CO : simplex_check_memory_snapshot)
 Require s == S && c == C && inputs == N && pivot_limit == L && rows == M && 1 <= M && M <= 16 && 0 <= N && N <= 8 && Zlength(A) == M*9 && Forall(Z::le(-2147483647),A) && Forall(Z::ge(2147483647),A) && 0 <= L && L <= 2147483647 &&
 simplex_check_old(S,M,N,Old) * simplex_check_frame(S,M,N,Old) * simplex_init_input(C,A,M,N) * simplex_check_input_frame(C,M,N,CO)
 Ensure exists ON OD OB OIB OVN OVD,
 (__return == -1 || __return == 0 || __return == 1) &&
 simplex_check_result(A,M,N,L,__return,ON,OD,OB,OIB,OVN,OVD) &&
 (__return == 0 => simplex_solve_witness(A,M,N,OVN,OVD)) &&
 (__return == 1 => simplex_solve_unsat(A,M,N)) &&
 (__return != -1 => (simplex_solve_normal(A,simplex_init_zeroes(M+N),simplex_init_flags(N,M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N),M,N,simplex_solve_pack(ON,OD,OB,OIB,OVN,OVD)) && simplex_solve_origin(A,simplex_init_zeroes(M+N),simplex_init_flags(N,M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N),M,N,simplex_solve_pack(ON,OD,OB,OIB,OVN,OVD)))) &&
 store(&(((struct SxState *)S)->rows),M) * store(&(((struct SxState *)S)->inputs),N) *
 store(&(((struct SxState *)S)->vars),M+N) *
 IntArray::full(((struct SxState *)S)->basic,M,OB) *
 IntArray::full(((struct SxState *)S)->is_basic,M+N,OIB) *
 simplex_pivot_memory(S,M,M+N,ON,OD) *
 simplex_solve_variables(S,M+N,simplex_init_zeroes(M+N),simplex_init_flags(N,M+N),OVN,OVD,simplex_init_zeroes(M+N),simplex_init_ones(M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N)) * simplex_check_frame(S,M,N,Old) * simplex_init_input(C,A,M,N) * simplex_check_input_frame(C,M,N,CO)
*/
;


/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_deduction.simplex_deduction_lib */
/*@ Extern Coq
 (simplex_deduction_ptrs : list Z -> (Z -> Z) -> Assertion)
 (simplex_deduction_ints : list Z -> (Z -> Z) -> Assertion)
 (simplex_deduction_copy : Z -> list Z -> Z -> Z -> Z -> Assertion)
 (simplex_deduction_copy_except : Z -> list Z -> Z -> Z -> Z -> Z -> Assertion)
 (simplex_deduction_coef_address : Z -> Z)
 (simplex_deduction_next_address : Z -> Z)
 (simplex_deduction_unknown : simplex_check_memory_snapshot)
 (In : {A} -> A -> list A -> Prop)
 (NoDup : {A} -> list A -> Prop)
*/



/*@ Extern Coq
 (simplex_deduction_ptrs_without : list Z -> (Z -> Z) -> Z -> Assertion)
 (simplex_deduction_ints_without : list Z -> (Z -> Z) -> Z -> Assertion)
 (simplex_deduction_workspace : Z -> list Z -> Z -> Z -> Z -> Z -> Assertion)
 (simplex_deduction_workspace_except : Z -> list Z -> Z -> Z -> Z -> Z -> Assertion)
*/
int simplex_deduction(struct SxState *s, const struct InequList *list,
 int inputs, int pivot_limit, int c[SX_ROWS][SX_INPUT_VARS + 1])
/*@ invalid_inputs With N L  Require inputs == N && pivot_limit == L && (N < 0 || N > 8) && emp  Ensure __return == -1 && emp  */
/*@ nullcoef_reject
 With (A P PS IS : list Z) (PV IV : Z -> Z) M N S L
  C
 Require c == C && s == S && inputs == N && pivot_limit == L && 0 <= N && N <= 8 && 0 <= M && M <= 16 && -2147483648 <= L && L <= 2147483647 && Zlength(A) == M*9 && Forall(Z::le(-2147483648),A) && Forall(Z::ge(2147483647),A) && Zlength(P) == M+1 && list == Znth(0,P,0) &&
 NoDup(PS) && NoDup(IS) &&
 (forall (i: Z), (0 <= i && i < M) =>
  (Znth(i,P,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P,0)),PS) &&
   In(simplex_deduction_next_address(Znth(i,P,0)),PS) &&
   PV(simplex_deduction_coef_address(Znth(i,P,0))) != 0 &&
   PV(simplex_deduction_next_address(Znth(i,P,0))) == Znth(i+1,P,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M && 0 <= h && h <= N) =>
  (In(PV(simplex_deduction_coef_address(Znth(i,P,0)))+h*sizeof(int),IS) &&
   IV(PV(simplex_deduction_coef_address(Znth(i,P,0)))+h*sizeof(int)) == Znth(i*9+h,A,0))) && M < 16 && Znth(M,P,0) != 0 && In(simplex_deduction_coef_address(Znth(M,P,0)),PS) && PV(simplex_deduction_coef_address(Znth(M,P,0))) == 0 &&
 simplex_deduction_ptrs(PS,PV) * simplex_deduction_ints(IS,IV) * simplex_deduction_workspace(C,A,M,N,0,0)
 Ensure __return == -1 && simplex_deduction_ptrs(PS,PV) * simplex_deduction_ints(IS,IV) * simplex_deduction_workspace(C,A,M,N,M,0)
*/
/*@ bounded_prefix_reject
 With (A P PS IS : list Z) (PV IV : Z -> Z) M N S L
  C
 Require c == C && s == S && inputs == N && pivot_limit == L && 0 <= N && N <= 8 && 0 <= M && M <= 16 && -2147483648 <= L && L <= 2147483647 && Zlength(A) == M*9 && Forall(Z::le(-2147483648),A) && Forall(Z::ge(2147483647),A) && Zlength(P) == M+1 && list == Znth(0,P,0) &&
 NoDup(PS) && NoDup(IS) &&
 (forall (i: Z), (0 <= i && i < M) =>
  (Znth(i,P,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P,0)),PS) &&
   In(simplex_deduction_next_address(Znth(i,P,0)),PS) &&
   PV(simplex_deduction_coef_address(Znth(i,P,0))) != 0 &&
   PV(simplex_deduction_next_address(Znth(i,P,0))) == Znth(i+1,P,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M && 0 <= h && h <= N) =>
  (In(PV(simplex_deduction_coef_address(Znth(i,P,0)))+h*sizeof(int),IS) &&
   IV(PV(simplex_deduction_coef_address(Znth(i,P,0)))+h*sizeof(int)) == Znth(i*9+h,A,0))) && M == 16 && Znth(M,P,0) != 0 &&
 simplex_deduction_ptrs(PS,PV) * simplex_deduction_ints(IS,IV) * simplex_deduction_workspace(C,A,M,N,0,0)
 Ensure __return == -1 && simplex_deduction_ptrs(PS,PV) * simplex_deduction_ints(IS,IV) * simplex_deduction_workspace(C,A,M,N,M,0)
*/
/*@ complete_min
 With (A P PS IS : list Z) (PV IV : Z -> Z) M N S L
  C
 Require c == C && s == S && inputs == N && pivot_limit == L && 0 <= N && N <= 8 && 0 <= M && M <= 16 && -2147483648 <= L && L <= 2147483647 && Zlength(A) == M*9 && Forall(Z::le(-2147483648),A) && Forall(Z::ge(2147483647),A) && Zlength(P) == M+1 && list == Znth(0,P,0) &&
 NoDup(PS) && NoDup(IS) &&
 (forall (i: Z), (0 <= i && i < M) =>
  (Znth(i,P,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P,0)),PS) &&
   In(simplex_deduction_next_address(Znth(i,P,0)),PS) &&
   PV(simplex_deduction_coef_address(Znth(i,P,0))) != 0 &&
   PV(simplex_deduction_next_address(Znth(i,P,0))) == Znth(i+1,P,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M && 0 <= h && h <= N) =>
  (In(PV(simplex_deduction_coef_address(Znth(i,P,0)))+h*sizeof(int),IS) &&
   IV(PV(simplex_deduction_coef_address(Znth(i,P,0)))+h*sizeof(int)) == Znth(i*9+h,A,0))) && Znth(M,P,0) == 0 && (exists (x: Z) (y: Z), 0 <= x && x < M && 0 <= y && y <= N && Znth(x*9+y,A,0) == -2147483648) &&
 simplex_deduction_ptrs(PS,PV) * simplex_deduction_ints(IS,IV) * simplex_deduction_workspace(C,A,M,N,0,0)
 Ensure __return == -1 && simplex_check_rejected_result(A,M,N,L,__return) && simplex_deduction_ptrs(PS,PV) * simplex_deduction_ints(IS,IV) * simplex_init_input(C,A,M,N)
*/
/*@ zero_negative
 With (A P PS IS : list Z) (PV IV : Z -> Z) M N S L (Old : simplex_check_memory_snapshot)
  C
 Require c == C && s == S && inputs == N && pivot_limit == L && 0 <= N && N <= 8 && 0 <= M && M <= 16 && -2147483648 <= L && L <= 2147483647 && Zlength(A) == M*9 && Forall(Z::le(-2147483648),A) && Forall(Z::ge(2147483647),A) && Zlength(P) == M+1 && list == Znth(0,P,0) &&
 NoDup(PS) && NoDup(IS) &&
 (forall (i: Z), (0 <= i && i < M) =>
  (Znth(i,P,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P,0)),PS) &&
   In(simplex_deduction_next_address(Znth(i,P,0)),PS) &&
   PV(simplex_deduction_coef_address(Znth(i,P,0))) != 0 &&
   PV(simplex_deduction_next_address(Znth(i,P,0))) == Znth(i+1,P,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M && 0 <= h && h <= N) =>
  (In(PV(simplex_deduction_coef_address(Znth(i,P,0)))+h*sizeof(int),IS) &&
   IV(PV(simplex_deduction_coef_address(Znth(i,P,0)))+h*sizeof(int)) == Znth(i*9+h,A,0))) && Znth(M,P,0) == 0 && Forall(Z::le(-2147483647),A) && M == 0 && L < 0 &&
 simplex_deduction_ptrs(PS,PV) * simplex_deduction_ints(IS,IV) * simplex_check_old(S,0,N,Old) * simplex_check_frame(S,0,N,Old) * simplex_deduction_workspace(C,A,M,N,0,0)
 Ensure __return == -1 && simplex_check_result(A,0,N,L,__return,simplex_check_initial_num(A,0,N),simplex_init_ones(400),simplex_init_basic(N,0),simplex_init_flags(N,M+N),simplex_init_values(A,0,N),simplex_init_ones(M+N)) && store(&(((struct SxState *)S)->rows), 0) * store(&(((struct SxState *)S)->inputs), N) * store(&(((struct SxState *)S)->vars), M+N) * simplex_init_vars(S,N,M+N,0,M+N,simplex_init_rhs(A,0),1) * simplex_init_rows(S,A,N,0,0,M+N) * simplex_check_frame(S,0,N,Old) * simplex_deduction_ptrs(PS,PV) * simplex_deduction_ints(IS,IV) * simplex_init_input(C,A,M,N)
*/
/*@ zero_normal
 With (A P PS IS : list Z) (PV IV : Z -> Z) M N S L (Old : simplex_check_memory_snapshot)
  C
 Require c == C && s == S && inputs == N && pivot_limit == L && 0 <= N && N <= 8 && 0 <= M && M <= 16 && -2147483648 <= L && L <= 2147483647 && Zlength(A) == M*9 && Forall(Z::le(-2147483648),A) && Forall(Z::ge(2147483647),A) && Zlength(P) == M+1 && list == Znth(0,P,0) &&
 NoDup(PS) && NoDup(IS) &&
 (forall (i: Z), (0 <= i && i < M) =>
  (Znth(i,P,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P,0)),PS) &&
   In(simplex_deduction_next_address(Znth(i,P,0)),PS) &&
   PV(simplex_deduction_coef_address(Znth(i,P,0))) != 0 &&
   PV(simplex_deduction_next_address(Znth(i,P,0))) == Znth(i+1,P,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M && 0 <= h && h <= N) =>
  (In(PV(simplex_deduction_coef_address(Znth(i,P,0)))+h*sizeof(int),IS) &&
   IV(PV(simplex_deduction_coef_address(Znth(i,P,0)))+h*sizeof(int)) == Znth(i*9+h,A,0))) && Znth(M,P,0) == 0 && Forall(Z::le(-2147483647),A) && M == 0 && 0 <= L &&
 simplex_deduction_ptrs(PS,PV) * simplex_deduction_ints(IS,IV) * simplex_check_old(S,0,N,Old) * simplex_check_frame(S,0,N,Old) * simplex_deduction_workspace(C,A,M,N,0,0)
 Ensure exists ON OD OB OIB OVN OVD,
 simplex_init_return(__return,0) &&
 (__return == -1 || __return == 0 || __return == 1) &&
 simplex_check_result(A,0,N,L,__return,ON,OD,OB,OIB,OVN,OVD) &&
 (__return == 0 => simplex_solve_witness(A,0,N,OVN,OVD)) &&
 (__return == 1 => simplex_solve_unsat(A,0,N)) &&
 (__return != -1 => (simplex_solve_normal(A,simplex_init_zeroes(M+N),simplex_init_flags(N,M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N),0,N,simplex_solve_pack(ON,OD,OB,OIB,OVN,OVD)) && simplex_solve_origin(A,simplex_init_zeroes(M+N),simplex_init_flags(N,M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N),0,N,simplex_solve_pack(ON,OD,OB,OIB,OVN,OVD)))) &&
 store(&(((struct SxState *)S)->rows),0) * store(&(((struct SxState *)S)->inputs),N) *
 store(&(((struct SxState *)S)->vars),M+N) *
 IntArray::full(((struct SxState *)S)->basic,0,OB) *
 IntArray::full(((struct SxState *)S)->is_basic,M+N,OIB) *
 simplex_pivot_memory(S,0,M+N,ON,OD) *
 simplex_solve_variables(S,M+N,simplex_init_zeroes(M+N),simplex_init_flags(N,M+N),OVN,OVD,simplex_init_zeroes(M+N),simplex_init_ones(M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N)) * simplex_check_frame(S,0,N,Old) * simplex_deduction_ptrs(PS,PV) * simplex_deduction_ints(IS,IV) * simplex_init_input(C,A,M,N)
*/
/*@ matrix_negative
 With (A P PS IS : list Z) (PV IV : Z -> Z) M N S L (Old : simplex_check_memory_snapshot)
  C (CO : simplex_check_memory_snapshot)
 Require c == C && s == S && inputs == N && pivot_limit == L && 0 <= N && N <= 8 && 0 <= M && M <= 16 && -2147483648 <= L && L <= 2147483647 && Zlength(A) == M*9 && Forall(Z::le(-2147483648),A) && Forall(Z::ge(2147483647),A) && Zlength(P) == M+1 && list == Znth(0,P,0) &&
 NoDup(PS) && NoDup(IS) &&
 (forall (i: Z), (0 <= i && i < M) =>
  (Znth(i,P,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P,0)),PS) &&
   In(simplex_deduction_next_address(Znth(i,P,0)),PS) &&
   PV(simplex_deduction_coef_address(Znth(i,P,0))) != 0 &&
   PV(simplex_deduction_next_address(Znth(i,P,0))) == Znth(i+1,P,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M && 0 <= h && h <= N) =>
  (In(PV(simplex_deduction_coef_address(Znth(i,P,0)))+h*sizeof(int),IS) &&
   IV(PV(simplex_deduction_coef_address(Znth(i,P,0)))+h*sizeof(int)) == Znth(i*9+h,A,0))) && Znth(M,P,0) == 0 && Forall(Z::le(-2147483647),A) && 1 <= M && L < 0 &&
 simplex_deduction_ptrs(PS,PV) * simplex_deduction_ints(IS,IV) * simplex_check_old(S,M,N,Old) * simplex_check_frame(S,M,N,Old) * simplex_deduction_workspace(C,A,M,N,0,0) * simplex_check_input_frame(C,M,N,CO)
 Ensure __return == -1 && simplex_check_result(A,M,N,L,__return,simplex_check_initial_num(A,M,N),simplex_init_ones(400),simplex_init_basic(N,M),simplex_init_flags(N,M+N),simplex_init_values(A,M,N),simplex_init_ones(M+N)) && store(&(((struct SxState *)S)->rows), M) * store(&(((struct SxState *)S)->inputs), N) * store(&(((struct SxState *)S)->vars), M+N) * simplex_init_vars(S,N,M+N,M,M+N,simplex_init_rhs(A,M),1) * simplex_init_rows(S,A,N,M,M,M+N) * simplex_check_frame(S,M,N,Old) * simplex_deduction_ptrs(PS,PV) * simplex_deduction_ints(IS,IV) * simplex_init_input(C,A,M,N) * simplex_check_input_frame(C,M,N,CO)
*/
/*@ matrix_normal
 With (A P PS IS : list Z) (PV IV : Z -> Z) M N S L (Old : simplex_check_memory_snapshot)
  C (CO : simplex_check_memory_snapshot)
 Require c == C && s == S && inputs == N && pivot_limit == L && 0 <= N && N <= 8 && 0 <= M && M <= 16 && -2147483648 <= L && L <= 2147483647 && Zlength(A) == M*9 && Forall(Z::le(-2147483648),A) && Forall(Z::ge(2147483647),A) && Zlength(P) == M+1 && list == Znth(0,P,0) &&
 NoDup(PS) && NoDup(IS) &&
 (forall (i: Z), (0 <= i && i < M) =>
  (Znth(i,P,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P,0)),PS) &&
   In(simplex_deduction_next_address(Znth(i,P,0)),PS) &&
   PV(simplex_deduction_coef_address(Znth(i,P,0))) != 0 &&
   PV(simplex_deduction_next_address(Znth(i,P,0))) == Znth(i+1,P,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M && 0 <= h && h <= N) =>
  (In(PV(simplex_deduction_coef_address(Znth(i,P,0)))+h*sizeof(int),IS) &&
   IV(PV(simplex_deduction_coef_address(Znth(i,P,0)))+h*sizeof(int)) == Znth(i*9+h,A,0))) && Znth(M,P,0) == 0 && Forall(Z::le(-2147483647),A) && 1 <= M && 0 <= L &&
 simplex_deduction_ptrs(PS,PV) * simplex_deduction_ints(IS,IV) * simplex_check_old(S,M,N,Old) * simplex_check_frame(S,M,N,Old) * simplex_deduction_workspace(C,A,M,N,0,0) * simplex_check_input_frame(C,M,N,CO)
 Ensure exists ON OD OB OIB OVN OVD,
 (__return == -1 || __return == 0 || __return == 1) &&
 simplex_check_result(A,M,N,L,__return,ON,OD,OB,OIB,OVN,OVD) &&
 (__return == 0 => simplex_solve_witness(A,M,N,OVN,OVD)) &&
 (__return == 1 => simplex_solve_unsat(A,M,N)) &&
 (__return != -1 => (simplex_solve_normal(A,simplex_init_zeroes(M+N),simplex_init_flags(N,M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N),M,N,simplex_solve_pack(ON,OD,OB,OIB,OVN,OVD)) && simplex_solve_origin(A,simplex_init_zeroes(M+N),simplex_init_flags(N,M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N),M,N,simplex_solve_pack(ON,OD,OB,OIB,OVN,OVD)))) &&
 store(&(((struct SxState *)S)->rows),M) * store(&(((struct SxState *)S)->inputs),N) *
 store(&(((struct SxState *)S)->vars),M+N) *
 IntArray::full(((struct SxState *)S)->basic,M,OB) *
 IntArray::full(((struct SxState *)S)->is_basic,M+N,OIB) *
 simplex_pivot_memory(S,M,M+N,ON,OD) *
 simplex_solve_variables(S,M+N,simplex_init_zeroes(M+N),simplex_init_flags(N,M+N),OVN,OVD,simplex_init_zeroes(M+N),simplex_init_ones(M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N)) * simplex_check_frame(S,M,N,Old) * simplex_deduction_ptrs(PS,PV) * simplex_deduction_ints(IS,IV) * simplex_init_input(C,A,M,N) * simplex_check_input_frame(C,M,N,CO)
*/
;
int simplex_deduction(struct SxState *s, const struct InequList *list, int inputs, int pivot_limit, int c[SX_ROWS][SX_INPUT_VARS + 1])
/*@ invalid_inputs */
/*@ nullcoef_reject */
/*@ bounded_prefix_reject */
/*@ complete_min */
/*@ zero_negative */
/*@ zero_normal */
/*@ matrix_negative */
/*@ matrix_normal */
{
 int rows = 0, j;
 const struct InequList *p = list;
 if (inputs < 0 || inputs > SX_INPUT_VARS) return SX_UNKNOWN;
/*@ Inv
invalid_inputs: Assert 0 == 1 && emp;
nullcoef_reject: Assert p != 0 && c == C_nullcoef_reject && s == S_nullcoef_reject && inputs == N_nullcoef_reject && pivot_limit == L_nullcoef_reject && 0 <= N_nullcoef_reject && N_nullcoef_reject <= 8 && 0 <= M_nullcoef_reject && M_nullcoef_reject <= 16 && -2147483648 <= L_nullcoef_reject && L_nullcoef_reject <= 2147483647 && Zlength(A_nullcoef_reject) == M_nullcoef_reject*9 && Forall(Z::le(-2147483648),A_nullcoef_reject) && Forall(Z::ge(2147483647),A_nullcoef_reject) && Zlength(P_nullcoef_reject) == M_nullcoef_reject+1 && list == Znth(0,P_nullcoef_reject,0) &&
 NoDup(PS_nullcoef_reject) && NoDup(IS_nullcoef_reject) &&
 (forall (i: Z), (0 <= i && i < M_nullcoef_reject) =>
  (Znth(i,P_nullcoef_reject,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)),PS_nullcoef_reject) &&
   In(simplex_deduction_next_address(Znth(i,P_nullcoef_reject,0)),PS_nullcoef_reject) &&
   PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0))) != 0 &&
   PV_nullcoef_reject(simplex_deduction_next_address(Znth(i,P_nullcoef_reject,0))) == Znth(i+1,P_nullcoef_reject,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_nullcoef_reject && 0 <= h && h <= N_nullcoef_reject) =>
  (In(PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)))+h*sizeof(int),IS_nullcoef_reject) &&
   IV_nullcoef_reject(PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)))+h*sizeof(int)) == Znth(i*9+h,A_nullcoef_reject,0))) && M_nullcoef_reject < 16 && Znth(M_nullcoef_reject,P_nullcoef_reject,0) != 0 && In(simplex_deduction_coef_address(Znth(M_nullcoef_reject,P_nullcoef_reject,0)),PS_nullcoef_reject) && PV_nullcoef_reject(simplex_deduction_coef_address(Znth(M_nullcoef_reject,P_nullcoef_reject,0))) == 0 &&
 0 <= rows && rows <= M_nullcoef_reject && p == Znth(rows,P_nullcoef_reject,0) && simplex_deduction_ptrs(PS_nullcoef_reject,PV_nullcoef_reject) * simplex_deduction_ints(IS_nullcoef_reject,IV_nullcoef_reject) * simplex_deduction_workspace(C_nullcoef_reject,A_nullcoef_reject,M_nullcoef_reject,N_nullcoef_reject,rows,0) * undef_data_at(&j);
bounded_prefix_reject: Assert p != 0 && c == C_bounded_prefix_reject && s == S_bounded_prefix_reject && inputs == N_bounded_prefix_reject && pivot_limit == L_bounded_prefix_reject && 0 <= N_bounded_prefix_reject && N_bounded_prefix_reject <= 8 && 0 <= M_bounded_prefix_reject && M_bounded_prefix_reject <= 16 && -2147483648 <= L_bounded_prefix_reject && L_bounded_prefix_reject <= 2147483647 && Zlength(A_bounded_prefix_reject) == M_bounded_prefix_reject*9 && Forall(Z::le(-2147483648),A_bounded_prefix_reject) && Forall(Z::ge(2147483647),A_bounded_prefix_reject) && Zlength(P_bounded_prefix_reject) == M_bounded_prefix_reject+1 && list == Znth(0,P_bounded_prefix_reject,0) &&
 NoDup(PS_bounded_prefix_reject) && NoDup(IS_bounded_prefix_reject) &&
 (forall (i: Z), (0 <= i && i < M_bounded_prefix_reject) =>
  (Znth(i,P_bounded_prefix_reject,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)),PS_bounded_prefix_reject) &&
   In(simplex_deduction_next_address(Znth(i,P_bounded_prefix_reject,0)),PS_bounded_prefix_reject) &&
   PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0))) != 0 &&
   PV_bounded_prefix_reject(simplex_deduction_next_address(Znth(i,P_bounded_prefix_reject,0))) == Znth(i+1,P_bounded_prefix_reject,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_bounded_prefix_reject && 0 <= h && h <= N_bounded_prefix_reject) =>
  (In(PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)))+h*sizeof(int),IS_bounded_prefix_reject) &&
   IV_bounded_prefix_reject(PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)))+h*sizeof(int)) == Znth(i*9+h,A_bounded_prefix_reject,0))) && M_bounded_prefix_reject == 16 && Znth(M_bounded_prefix_reject,P_bounded_prefix_reject,0) != 0 &&
 0 <= rows && rows <= M_bounded_prefix_reject && p == Znth(rows,P_bounded_prefix_reject,0) && simplex_deduction_ptrs(PS_bounded_prefix_reject,PV_bounded_prefix_reject) * simplex_deduction_ints(IS_bounded_prefix_reject,IV_bounded_prefix_reject) * simplex_deduction_workspace(C_bounded_prefix_reject,A_bounded_prefix_reject,M_bounded_prefix_reject,N_bounded_prefix_reject,rows,0) * undef_data_at(&j);
complete_min: Assert (p != 0 || rows == M_complete_min) && c == C_complete_min && s == S_complete_min && inputs == N_complete_min && pivot_limit == L_complete_min && 0 <= N_complete_min && N_complete_min <= 8 && 0 <= M_complete_min && M_complete_min <= 16 && -2147483648 <= L_complete_min && L_complete_min <= 2147483647 && Zlength(A_complete_min) == M_complete_min*9 && Forall(Z::le(-2147483648),A_complete_min) && Forall(Z::ge(2147483647),A_complete_min) && Zlength(P_complete_min) == M_complete_min+1 && list == Znth(0,P_complete_min,0) &&
 NoDup(PS_complete_min) && NoDup(IS_complete_min) &&
 (forall (i: Z), (0 <= i && i < M_complete_min) =>
  (Znth(i,P_complete_min,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_complete_min,0)),PS_complete_min) &&
   In(simplex_deduction_next_address(Znth(i,P_complete_min,0)),PS_complete_min) &&
   PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0))) != 0 &&
   PV_complete_min(simplex_deduction_next_address(Znth(i,P_complete_min,0))) == Znth(i+1,P_complete_min,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_complete_min && 0 <= h && h <= N_complete_min) =>
  (In(PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0)))+h*sizeof(int),IS_complete_min) &&
   IV_complete_min(PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0)))+h*sizeof(int)) == Znth(i*9+h,A_complete_min,0))) && Znth(M_complete_min,P_complete_min,0) == 0 && (exists (x: Z) (y: Z), 0 <= x && x < M_complete_min && 0 <= y && y <= N_complete_min && Znth(x*9+y,A_complete_min,0) == -2147483648) &&
 0 <= rows && rows <= M_complete_min && p == Znth(rows,P_complete_min,0) && simplex_deduction_ptrs(PS_complete_min,PV_complete_min) * simplex_deduction_ints(IS_complete_min,IV_complete_min) * ((p == 0 && simplex_init_input(C_complete_min,A_complete_min,M_complete_min,N_complete_min)) || (p != 0 && simplex_deduction_workspace(C_complete_min,A_complete_min,M_complete_min,N_complete_min,rows,0))) * undef_data_at(&j);
zero_negative: Assert (p != 0 || rows == M_zero_negative) && p == 0 && rows == 0 && c == C_zero_negative && s == S_zero_negative && inputs == N_zero_negative && pivot_limit == L_zero_negative && 0 <= N_zero_negative && N_zero_negative <= 8 && 0 <= M_zero_negative && M_zero_negative <= 16 && -2147483648 <= L_zero_negative && L_zero_negative <= 2147483647 && Zlength(A_zero_negative) == M_zero_negative*9 && Forall(Z::le(-2147483648),A_zero_negative) && Forall(Z::ge(2147483647),A_zero_negative) && Zlength(P_zero_negative) == M_zero_negative+1 && list == Znth(0,P_zero_negative,0) &&
 NoDup(PS_zero_negative) && NoDup(IS_zero_negative) &&
 (forall (i: Z), (0 <= i && i < M_zero_negative) =>
  (Znth(i,P_zero_negative,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)),PS_zero_negative) &&
   In(simplex_deduction_next_address(Znth(i,P_zero_negative,0)),PS_zero_negative) &&
   PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0))) != 0 &&
   PV_zero_negative(simplex_deduction_next_address(Znth(i,P_zero_negative,0))) == Znth(i+1,P_zero_negative,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_zero_negative && 0 <= h && h <= N_zero_negative) =>
  (In(PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)))+h*sizeof(int),IS_zero_negative) &&
   IV_zero_negative(PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)))+h*sizeof(int)) == Znth(i*9+h,A_zero_negative,0))) && Znth(M_zero_negative,P_zero_negative,0) == 0 && Forall(Z::le(-2147483647),A_zero_negative) && M_zero_negative == 0 && L_zero_negative < 0 &&
 0 <= rows && rows <= M_zero_negative && p == Znth(rows,P_zero_negative,0) && simplex_deduction_ptrs(PS_zero_negative,PV_zero_negative) * simplex_deduction_ints(IS_zero_negative,IV_zero_negative) * simplex_check_old(S_zero_negative,0,N_zero_negative,Old_zero_negative) * simplex_check_frame(S_zero_negative,0,N_zero_negative,Old_zero_negative) * ((p == 0 && simplex_init_input(C_zero_negative,A_zero_negative,M_zero_negative,N_zero_negative)) || (p != 0 && simplex_deduction_workspace(C_zero_negative,A_zero_negative,M_zero_negative,N_zero_negative,rows,0))) * undef_data_at(&j);
zero_normal: Assert (p != 0 || rows == M_zero_normal) && p == 0 && rows == 0 && c == C_zero_normal && s == S_zero_normal && inputs == N_zero_normal && pivot_limit == L_zero_normal && 0 <= N_zero_normal && N_zero_normal <= 8 && 0 <= M_zero_normal && M_zero_normal <= 16 && -2147483648 <= L_zero_normal && L_zero_normal <= 2147483647 && Zlength(A_zero_normal) == M_zero_normal*9 && Forall(Z::le(-2147483648),A_zero_normal) && Forall(Z::ge(2147483647),A_zero_normal) && Zlength(P_zero_normal) == M_zero_normal+1 && list == Znth(0,P_zero_normal,0) &&
 NoDup(PS_zero_normal) && NoDup(IS_zero_normal) &&
 (forall (i: Z), (0 <= i && i < M_zero_normal) =>
  (Znth(i,P_zero_normal,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)),PS_zero_normal) &&
   In(simplex_deduction_next_address(Znth(i,P_zero_normal,0)),PS_zero_normal) &&
   PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0))) != 0 &&
   PV_zero_normal(simplex_deduction_next_address(Znth(i,P_zero_normal,0))) == Znth(i+1,P_zero_normal,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_zero_normal && 0 <= h && h <= N_zero_normal) =>
  (In(PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)))+h*sizeof(int),IS_zero_normal) &&
   IV_zero_normal(PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)))+h*sizeof(int)) == Znth(i*9+h,A_zero_normal,0))) && Znth(M_zero_normal,P_zero_normal,0) == 0 && Forall(Z::le(-2147483647),A_zero_normal) && M_zero_normal == 0 && 0 <= L_zero_normal &&
 0 <= rows && rows <= M_zero_normal && p == Znth(rows,P_zero_normal,0) && simplex_deduction_ptrs(PS_zero_normal,PV_zero_normal) * simplex_deduction_ints(IS_zero_normal,IV_zero_normal) * simplex_check_old(S_zero_normal,0,N_zero_normal,Old_zero_normal) * simplex_check_frame(S_zero_normal,0,N_zero_normal,Old_zero_normal) * ((p == 0 && simplex_init_input(C_zero_normal,A_zero_normal,M_zero_normal,N_zero_normal)) || (p != 0 && simplex_deduction_workspace(C_zero_normal,A_zero_normal,M_zero_normal,N_zero_normal,rows,0))) * undef_data_at(&j);
matrix_negative: Assert (p != 0 || rows == M_matrix_negative) && c == C_matrix_negative && s == S_matrix_negative && inputs == N_matrix_negative && pivot_limit == L_matrix_negative && 0 <= N_matrix_negative && N_matrix_negative <= 8 && 0 <= M_matrix_negative && M_matrix_negative <= 16 && -2147483648 <= L_matrix_negative && L_matrix_negative <= 2147483647 && Zlength(A_matrix_negative) == M_matrix_negative*9 && Forall(Z::le(-2147483648),A_matrix_negative) && Forall(Z::ge(2147483647),A_matrix_negative) && Zlength(P_matrix_negative) == M_matrix_negative+1 && list == Znth(0,P_matrix_negative,0) &&
 NoDup(PS_matrix_negative) && NoDup(IS_matrix_negative) &&
 (forall (i: Z), (0 <= i && i < M_matrix_negative) =>
  (Znth(i,P_matrix_negative,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)),PS_matrix_negative) &&
   In(simplex_deduction_next_address(Znth(i,P_matrix_negative,0)),PS_matrix_negative) &&
   PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0))) != 0 &&
   PV_matrix_negative(simplex_deduction_next_address(Znth(i,P_matrix_negative,0))) == Znth(i+1,P_matrix_negative,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_matrix_negative && 0 <= h && h <= N_matrix_negative) =>
  (In(PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)))+h*sizeof(int),IS_matrix_negative) &&
   IV_matrix_negative(PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)))+h*sizeof(int)) == Znth(i*9+h,A_matrix_negative,0))) && Znth(M_matrix_negative,P_matrix_negative,0) == 0 && Forall(Z::le(-2147483647),A_matrix_negative) && 1 <= M_matrix_negative && L_matrix_negative < 0 &&
 0 <= rows && rows <= M_matrix_negative && p == Znth(rows,P_matrix_negative,0) && simplex_deduction_ptrs(PS_matrix_negative,PV_matrix_negative) * simplex_deduction_ints(IS_matrix_negative,IV_matrix_negative) * simplex_check_old(S_matrix_negative,M_matrix_negative,N_matrix_negative,Old_matrix_negative) * simplex_check_frame(S_matrix_negative,M_matrix_negative,N_matrix_negative,Old_matrix_negative) * ((p == 0 && simplex_init_input(C_matrix_negative,A_matrix_negative,M_matrix_negative,N_matrix_negative)) || (p != 0 && simplex_deduction_workspace(C_matrix_negative,A_matrix_negative,M_matrix_negative,N_matrix_negative,rows,0))) * simplex_check_input_frame(C_matrix_negative,M_matrix_negative,N_matrix_negative,CO_matrix_negative) * undef_data_at(&j);
matrix_normal: Assert (p != 0 || rows == M_matrix_normal) && c == C_matrix_normal && s == S_matrix_normal && inputs == N_matrix_normal && pivot_limit == L_matrix_normal && 0 <= N_matrix_normal && N_matrix_normal <= 8 && 0 <= M_matrix_normal && M_matrix_normal <= 16 && -2147483648 <= L_matrix_normal && L_matrix_normal <= 2147483647 && Zlength(A_matrix_normal) == M_matrix_normal*9 && Forall(Z::le(-2147483648),A_matrix_normal) && Forall(Z::ge(2147483647),A_matrix_normal) && Zlength(P_matrix_normal) == M_matrix_normal+1 && list == Znth(0,P_matrix_normal,0) &&
 NoDup(PS_matrix_normal) && NoDup(IS_matrix_normal) &&
 (forall (i: Z), (0 <= i && i < M_matrix_normal) =>
  (Znth(i,P_matrix_normal,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)),PS_matrix_normal) &&
   In(simplex_deduction_next_address(Znth(i,P_matrix_normal,0)),PS_matrix_normal) &&
   PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0))) != 0 &&
   PV_matrix_normal(simplex_deduction_next_address(Znth(i,P_matrix_normal,0))) == Znth(i+1,P_matrix_normal,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_matrix_normal && 0 <= h && h <= N_matrix_normal) =>
  (In(PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)))+h*sizeof(int),IS_matrix_normal) &&
   IV_matrix_normal(PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)))+h*sizeof(int)) == Znth(i*9+h,A_matrix_normal,0))) && Znth(M_matrix_normal,P_matrix_normal,0) == 0 && Forall(Z::le(-2147483647),A_matrix_normal) && 1 <= M_matrix_normal && 0 <= L_matrix_normal &&
 0 <= rows && rows <= M_matrix_normal && p == Znth(rows,P_matrix_normal,0) && simplex_deduction_ptrs(PS_matrix_normal,PV_matrix_normal) * simplex_deduction_ints(IS_matrix_normal,IV_matrix_normal) * simplex_check_old(S_matrix_normal,M_matrix_normal,N_matrix_normal,Old_matrix_normal) * simplex_check_frame(S_matrix_normal,M_matrix_normal,N_matrix_normal,Old_matrix_normal) * ((p == 0 && simplex_init_input(C_matrix_normal,A_matrix_normal,M_matrix_normal,N_matrix_normal)) || (p != 0 && simplex_deduction_workspace(C_matrix_normal,A_matrix_normal,M_matrix_normal,N_matrix_normal,rows,0))) * simplex_check_input_frame(C_matrix_normal,M_matrix_normal,N_matrix_normal,CO_matrix_normal) * undef_data_at(&j) */
 while (p != 0) {
/*@ Assert 0 == 1 && emp $ invalid_inputs */
/*@ Assert c == C_nullcoef_reject && s == S_nullcoef_reject && inputs == N_nullcoef_reject && pivot_limit == L_nullcoef_reject && 0 <= N_nullcoef_reject && N_nullcoef_reject <= 8 && 0 <= M_nullcoef_reject && M_nullcoef_reject <= 16 && -2147483648 <= L_nullcoef_reject && L_nullcoef_reject <= 2147483647 && Zlength(A_nullcoef_reject) == M_nullcoef_reject*9 && Forall(Z::le(-2147483648),A_nullcoef_reject) && Forall(Z::ge(2147483647),A_nullcoef_reject) && Zlength(P_nullcoef_reject) == M_nullcoef_reject+1 && list == Znth(0,P_nullcoef_reject,0) &&
 NoDup(PS_nullcoef_reject) && NoDup(IS_nullcoef_reject) &&
 (forall (i: Z), (0 <= i && i < M_nullcoef_reject) =>
  (Znth(i,P_nullcoef_reject,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)),PS_nullcoef_reject) &&
   In(simplex_deduction_next_address(Znth(i,P_nullcoef_reject,0)),PS_nullcoef_reject) &&
   PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0))) != 0 &&
   PV_nullcoef_reject(simplex_deduction_next_address(Znth(i,P_nullcoef_reject,0))) == Znth(i+1,P_nullcoef_reject,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_nullcoef_reject && 0 <= h && h <= N_nullcoef_reject) =>
  (In(PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)))+h*sizeof(int),IS_nullcoef_reject) &&
   IV_nullcoef_reject(PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)))+h*sizeof(int)) == Znth(i*9+h,A_nullcoef_reject,0))) && M_nullcoef_reject < 16 && Znth(M_nullcoef_reject,P_nullcoef_reject,0) != 0 && In(simplex_deduction_coef_address(Znth(M_nullcoef_reject,P_nullcoef_reject,0)),PS_nullcoef_reject) && PV_nullcoef_reject(simplex_deduction_coef_address(Znth(M_nullcoef_reject,P_nullcoef_reject,0))) == 0 &&
 0 <= rows && rows <= M_nullcoef_reject && p == Znth(rows,P_nullcoef_reject,0) && p != 0 && ((rows >= 16 && simplex_deduction_ptrs(PS_nullcoef_reject,PV_nullcoef_reject) * simplex_deduction_ints(IS_nullcoef_reject,IV_nullcoef_reject) * simplex_deduction_workspace(C_nullcoef_reject,A_nullcoef_reject,M_nullcoef_reject,N_nullcoef_reject,rows,0) * undef_data_at(&j)) || (rows < 16 && data_at(&(p->coef), int *, PV_nullcoef_reject(simplex_deduction_coef_address(p))) * simplex_deduction_ptrs_without(PS_nullcoef_reject,PV_nullcoef_reject,&(p->coef)) * simplex_deduction_ints(IS_nullcoef_reject,IV_nullcoef_reject) * simplex_deduction_workspace(C_nullcoef_reject,A_nullcoef_reject,M_nullcoef_reject,N_nullcoef_reject,rows,0) * undef_data_at(&j))) $ nullcoef_reject */
/*@ Assert c == C_bounded_prefix_reject && s == S_bounded_prefix_reject && inputs == N_bounded_prefix_reject && pivot_limit == L_bounded_prefix_reject && 0 <= N_bounded_prefix_reject && N_bounded_prefix_reject <= 8 && 0 <= M_bounded_prefix_reject && M_bounded_prefix_reject <= 16 && -2147483648 <= L_bounded_prefix_reject && L_bounded_prefix_reject <= 2147483647 && Zlength(A_bounded_prefix_reject) == M_bounded_prefix_reject*9 && Forall(Z::le(-2147483648),A_bounded_prefix_reject) && Forall(Z::ge(2147483647),A_bounded_prefix_reject) && Zlength(P_bounded_prefix_reject) == M_bounded_prefix_reject+1 && list == Znth(0,P_bounded_prefix_reject,0) &&
 NoDup(PS_bounded_prefix_reject) && NoDup(IS_bounded_prefix_reject) &&
 (forall (i: Z), (0 <= i && i < M_bounded_prefix_reject) =>
  (Znth(i,P_bounded_prefix_reject,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)),PS_bounded_prefix_reject) &&
   In(simplex_deduction_next_address(Znth(i,P_bounded_prefix_reject,0)),PS_bounded_prefix_reject) &&
   PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0))) != 0 &&
   PV_bounded_prefix_reject(simplex_deduction_next_address(Znth(i,P_bounded_prefix_reject,0))) == Znth(i+1,P_bounded_prefix_reject,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_bounded_prefix_reject && 0 <= h && h <= N_bounded_prefix_reject) =>
  (In(PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)))+h*sizeof(int),IS_bounded_prefix_reject) &&
   IV_bounded_prefix_reject(PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)))+h*sizeof(int)) == Znth(i*9+h,A_bounded_prefix_reject,0))) && M_bounded_prefix_reject == 16 && Znth(M_bounded_prefix_reject,P_bounded_prefix_reject,0) != 0 &&
 0 <= rows && rows <= M_bounded_prefix_reject && p == Znth(rows,P_bounded_prefix_reject,0) && p != 0 && ((rows >= 16 && simplex_deduction_ptrs(PS_bounded_prefix_reject,PV_bounded_prefix_reject) * simplex_deduction_ints(IS_bounded_prefix_reject,IV_bounded_prefix_reject) * simplex_deduction_workspace(C_bounded_prefix_reject,A_bounded_prefix_reject,M_bounded_prefix_reject,N_bounded_prefix_reject,rows,0) * undef_data_at(&j)) || (rows < 16 && data_at(&(p->coef), int *, PV_bounded_prefix_reject(simplex_deduction_coef_address(p))) * simplex_deduction_ptrs_without(PS_bounded_prefix_reject,PV_bounded_prefix_reject,&(p->coef)) * simplex_deduction_ints(IS_bounded_prefix_reject,IV_bounded_prefix_reject) * simplex_deduction_workspace(C_bounded_prefix_reject,A_bounded_prefix_reject,M_bounded_prefix_reject,N_bounded_prefix_reject,rows,0) * undef_data_at(&j))) $ bounded_prefix_reject */
/*@ Assert c == C_complete_min && s == S_complete_min && inputs == N_complete_min && pivot_limit == L_complete_min && 0 <= N_complete_min && N_complete_min <= 8 && 0 <= M_complete_min && M_complete_min <= 16 && -2147483648 <= L_complete_min && L_complete_min <= 2147483647 && Zlength(A_complete_min) == M_complete_min*9 && Forall(Z::le(-2147483648),A_complete_min) && Forall(Z::ge(2147483647),A_complete_min) && Zlength(P_complete_min) == M_complete_min+1 && list == Znth(0,P_complete_min,0) &&
 NoDup(PS_complete_min) && NoDup(IS_complete_min) &&
 (forall (i: Z), (0 <= i && i < M_complete_min) =>
  (Znth(i,P_complete_min,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_complete_min,0)),PS_complete_min) &&
   In(simplex_deduction_next_address(Znth(i,P_complete_min,0)),PS_complete_min) &&
   PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0))) != 0 &&
   PV_complete_min(simplex_deduction_next_address(Znth(i,P_complete_min,0))) == Znth(i+1,P_complete_min,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_complete_min && 0 <= h && h <= N_complete_min) =>
  (In(PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0)))+h*sizeof(int),IS_complete_min) &&
   IV_complete_min(PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0)))+h*sizeof(int)) == Znth(i*9+h,A_complete_min,0))) && Znth(M_complete_min,P_complete_min,0) == 0 && (exists (x: Z) (y: Z), 0 <= x && x < M_complete_min && 0 <= y && y <= N_complete_min && Znth(x*9+y,A_complete_min,0) == -2147483648) &&
 0 <= rows && rows <= M_complete_min && p == Znth(rows,P_complete_min,0) && p != 0 && ((rows >= 16 && simplex_deduction_ptrs(PS_complete_min,PV_complete_min) * simplex_deduction_ints(IS_complete_min,IV_complete_min) * simplex_deduction_workspace(C_complete_min,A_complete_min,M_complete_min,N_complete_min,rows,0) * undef_data_at(&j)) || (rows < 16 && data_at(&(p->coef), int *, PV_complete_min(simplex_deduction_coef_address(p))) * simplex_deduction_ptrs_without(PS_complete_min,PV_complete_min,&(p->coef)) * simplex_deduction_ints(IS_complete_min,IV_complete_min) * simplex_deduction_workspace(C_complete_min,A_complete_min,M_complete_min,N_complete_min,rows,0) * undef_data_at(&j))) $ complete_min */
/*@ Assert c == C_zero_negative && s == S_zero_negative && inputs == N_zero_negative && pivot_limit == L_zero_negative && 0 <= N_zero_negative && N_zero_negative <= 8 && 0 <= M_zero_negative && M_zero_negative <= 16 && -2147483648 <= L_zero_negative && L_zero_negative <= 2147483647 && Zlength(A_zero_negative) == M_zero_negative*9 && Forall(Z::le(-2147483648),A_zero_negative) && Forall(Z::ge(2147483647),A_zero_negative) && Zlength(P_zero_negative) == M_zero_negative+1 && list == Znth(0,P_zero_negative,0) &&
 NoDup(PS_zero_negative) && NoDup(IS_zero_negative) &&
 (forall (i: Z), (0 <= i && i < M_zero_negative) =>
  (Znth(i,P_zero_negative,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)),PS_zero_negative) &&
   In(simplex_deduction_next_address(Znth(i,P_zero_negative,0)),PS_zero_negative) &&
   PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0))) != 0 &&
   PV_zero_negative(simplex_deduction_next_address(Znth(i,P_zero_negative,0))) == Znth(i+1,P_zero_negative,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_zero_negative && 0 <= h && h <= N_zero_negative) =>
  (In(PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)))+h*sizeof(int),IS_zero_negative) &&
   IV_zero_negative(PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)))+h*sizeof(int)) == Znth(i*9+h,A_zero_negative,0))) && Znth(M_zero_negative,P_zero_negative,0) == 0 && Forall(Z::le(-2147483647),A_zero_negative) && M_zero_negative == 0 && L_zero_negative < 0 &&
 0 <= rows && rows <= M_zero_negative && p == Znth(rows,P_zero_negative,0) && p != 0 && ((rows >= 16 && simplex_deduction_ptrs(PS_zero_negative,PV_zero_negative) * simplex_deduction_ints(IS_zero_negative,IV_zero_negative) * simplex_deduction_workspace(C_zero_negative,A_zero_negative,M_zero_negative,N_zero_negative,rows,0) * simplex_check_old(S_zero_negative,0,N_zero_negative,Old_zero_negative) * simplex_check_frame(S_zero_negative,0,N_zero_negative,Old_zero_negative) * undef_data_at(&j)) || (rows < 16 && data_at(&(p->coef), int *, PV_zero_negative(simplex_deduction_coef_address(p))) * simplex_deduction_ptrs_without(PS_zero_negative,PV_zero_negative,&(p->coef)) * simplex_deduction_ints(IS_zero_negative,IV_zero_negative) * simplex_deduction_workspace(C_zero_negative,A_zero_negative,M_zero_negative,N_zero_negative,rows,0) * simplex_check_old(S_zero_negative,0,N_zero_negative,Old_zero_negative) * simplex_check_frame(S_zero_negative,0,N_zero_negative,Old_zero_negative) * undef_data_at(&j))) $ zero_negative */
/*@ Assert c == C_zero_normal && s == S_zero_normal && inputs == N_zero_normal && pivot_limit == L_zero_normal && 0 <= N_zero_normal && N_zero_normal <= 8 && 0 <= M_zero_normal && M_zero_normal <= 16 && -2147483648 <= L_zero_normal && L_zero_normal <= 2147483647 && Zlength(A_zero_normal) == M_zero_normal*9 && Forall(Z::le(-2147483648),A_zero_normal) && Forall(Z::ge(2147483647),A_zero_normal) && Zlength(P_zero_normal) == M_zero_normal+1 && list == Znth(0,P_zero_normal,0) &&
 NoDup(PS_zero_normal) && NoDup(IS_zero_normal) &&
 (forall (i: Z), (0 <= i && i < M_zero_normal) =>
  (Znth(i,P_zero_normal,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)),PS_zero_normal) &&
   In(simplex_deduction_next_address(Znth(i,P_zero_normal,0)),PS_zero_normal) &&
   PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0))) != 0 &&
   PV_zero_normal(simplex_deduction_next_address(Znth(i,P_zero_normal,0))) == Znth(i+1,P_zero_normal,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_zero_normal && 0 <= h && h <= N_zero_normal) =>
  (In(PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)))+h*sizeof(int),IS_zero_normal) &&
   IV_zero_normal(PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)))+h*sizeof(int)) == Znth(i*9+h,A_zero_normal,0))) && Znth(M_zero_normal,P_zero_normal,0) == 0 && Forall(Z::le(-2147483647),A_zero_normal) && M_zero_normal == 0 && 0 <= L_zero_normal &&
 0 <= rows && rows <= M_zero_normal && p == Znth(rows,P_zero_normal,0) && p != 0 && ((rows >= 16 && simplex_deduction_ptrs(PS_zero_normal,PV_zero_normal) * simplex_deduction_ints(IS_zero_normal,IV_zero_normal) * simplex_deduction_workspace(C_zero_normal,A_zero_normal,M_zero_normal,N_zero_normal,rows,0) * simplex_check_old(S_zero_normal,0,N_zero_normal,Old_zero_normal) * simplex_check_frame(S_zero_normal,0,N_zero_normal,Old_zero_normal) * undef_data_at(&j)) || (rows < 16 && data_at(&(p->coef), int *, PV_zero_normal(simplex_deduction_coef_address(p))) * simplex_deduction_ptrs_without(PS_zero_normal,PV_zero_normal,&(p->coef)) * simplex_deduction_ints(IS_zero_normal,IV_zero_normal) * simplex_deduction_workspace(C_zero_normal,A_zero_normal,M_zero_normal,N_zero_normal,rows,0) * simplex_check_old(S_zero_normal,0,N_zero_normal,Old_zero_normal) * simplex_check_frame(S_zero_normal,0,N_zero_normal,Old_zero_normal) * undef_data_at(&j))) $ zero_normal */
/*@ Assert c == C_matrix_negative && s == S_matrix_negative && inputs == N_matrix_negative && pivot_limit == L_matrix_negative && 0 <= N_matrix_negative && N_matrix_negative <= 8 && 0 <= M_matrix_negative && M_matrix_negative <= 16 && -2147483648 <= L_matrix_negative && L_matrix_negative <= 2147483647 && Zlength(A_matrix_negative) == M_matrix_negative*9 && Forall(Z::le(-2147483648),A_matrix_negative) && Forall(Z::ge(2147483647),A_matrix_negative) && Zlength(P_matrix_negative) == M_matrix_negative+1 && list == Znth(0,P_matrix_negative,0) &&
 NoDup(PS_matrix_negative) && NoDup(IS_matrix_negative) &&
 (forall (i: Z), (0 <= i && i < M_matrix_negative) =>
  (Znth(i,P_matrix_negative,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)),PS_matrix_negative) &&
   In(simplex_deduction_next_address(Znth(i,P_matrix_negative,0)),PS_matrix_negative) &&
   PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0))) != 0 &&
   PV_matrix_negative(simplex_deduction_next_address(Znth(i,P_matrix_negative,0))) == Znth(i+1,P_matrix_negative,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_matrix_negative && 0 <= h && h <= N_matrix_negative) =>
  (In(PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)))+h*sizeof(int),IS_matrix_negative) &&
   IV_matrix_negative(PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)))+h*sizeof(int)) == Znth(i*9+h,A_matrix_negative,0))) && Znth(M_matrix_negative,P_matrix_negative,0) == 0 && Forall(Z::le(-2147483647),A_matrix_negative) && 1 <= M_matrix_negative && L_matrix_negative < 0 &&
 0 <= rows && rows <= M_matrix_negative && p == Znth(rows,P_matrix_negative,0) && p != 0 && ((rows >= 16 && simplex_deduction_ptrs(PS_matrix_negative,PV_matrix_negative) * simplex_deduction_ints(IS_matrix_negative,IV_matrix_negative) * simplex_deduction_workspace(C_matrix_negative,A_matrix_negative,M_matrix_negative,N_matrix_negative,rows,0) * simplex_check_input_frame(C_matrix_negative,M_matrix_negative,N_matrix_negative,CO_matrix_negative) * simplex_check_old(S_matrix_negative,M_matrix_negative,N_matrix_negative,Old_matrix_negative) * simplex_check_frame(S_matrix_negative,M_matrix_negative,N_matrix_negative,Old_matrix_negative) * undef_data_at(&j)) || (rows < 16 && data_at(&(p->coef), int *, PV_matrix_negative(simplex_deduction_coef_address(p))) * simplex_deduction_ptrs_without(PS_matrix_negative,PV_matrix_negative,&(p->coef)) * simplex_deduction_ints(IS_matrix_negative,IV_matrix_negative) * simplex_deduction_workspace(C_matrix_negative,A_matrix_negative,M_matrix_negative,N_matrix_negative,rows,0) * simplex_check_input_frame(C_matrix_negative,M_matrix_negative,N_matrix_negative,CO_matrix_negative) * simplex_check_old(S_matrix_negative,M_matrix_negative,N_matrix_negative,Old_matrix_negative) * simplex_check_frame(S_matrix_negative,M_matrix_negative,N_matrix_negative,Old_matrix_negative) * undef_data_at(&j))) $ matrix_negative */
/*@ Assert c == C_matrix_normal && s == S_matrix_normal && inputs == N_matrix_normal && pivot_limit == L_matrix_normal && 0 <= N_matrix_normal && N_matrix_normal <= 8 && 0 <= M_matrix_normal && M_matrix_normal <= 16 && -2147483648 <= L_matrix_normal && L_matrix_normal <= 2147483647 && Zlength(A_matrix_normal) == M_matrix_normal*9 && Forall(Z::le(-2147483648),A_matrix_normal) && Forall(Z::ge(2147483647),A_matrix_normal) && Zlength(P_matrix_normal) == M_matrix_normal+1 && list == Znth(0,P_matrix_normal,0) &&
 NoDup(PS_matrix_normal) && NoDup(IS_matrix_normal) &&
 (forall (i: Z), (0 <= i && i < M_matrix_normal) =>
  (Znth(i,P_matrix_normal,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)),PS_matrix_normal) &&
   In(simplex_deduction_next_address(Znth(i,P_matrix_normal,0)),PS_matrix_normal) &&
   PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0))) != 0 &&
   PV_matrix_normal(simplex_deduction_next_address(Znth(i,P_matrix_normal,0))) == Znth(i+1,P_matrix_normal,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_matrix_normal && 0 <= h && h <= N_matrix_normal) =>
  (In(PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)))+h*sizeof(int),IS_matrix_normal) &&
   IV_matrix_normal(PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)))+h*sizeof(int)) == Znth(i*9+h,A_matrix_normal,0))) && Znth(M_matrix_normal,P_matrix_normal,0) == 0 && Forall(Z::le(-2147483647),A_matrix_normal) && 1 <= M_matrix_normal && 0 <= L_matrix_normal &&
 0 <= rows && rows <= M_matrix_normal && p == Znth(rows,P_matrix_normal,0) && p != 0 && ((rows >= 16 && simplex_deduction_ptrs(PS_matrix_normal,PV_matrix_normal) * simplex_deduction_ints(IS_matrix_normal,IV_matrix_normal) * simplex_deduction_workspace(C_matrix_normal,A_matrix_normal,M_matrix_normal,N_matrix_normal,rows,0) * simplex_check_input_frame(C_matrix_normal,M_matrix_normal,N_matrix_normal,CO_matrix_normal) * simplex_check_old(S_matrix_normal,M_matrix_normal,N_matrix_normal,Old_matrix_normal) * simplex_check_frame(S_matrix_normal,M_matrix_normal,N_matrix_normal,Old_matrix_normal) * undef_data_at(&j)) || (rows < 16 && data_at(&(p->coef), int *, PV_matrix_normal(simplex_deduction_coef_address(p))) * simplex_deduction_ptrs_without(PS_matrix_normal,PV_matrix_normal,&(p->coef)) * simplex_deduction_ints(IS_matrix_normal,IV_matrix_normal) * simplex_deduction_workspace(C_matrix_normal,A_matrix_normal,M_matrix_normal,N_matrix_normal,rows,0) * simplex_check_input_frame(C_matrix_normal,M_matrix_normal,N_matrix_normal,CO_matrix_normal) * simplex_check_old(S_matrix_normal,M_matrix_normal,N_matrix_normal,Old_matrix_normal) * simplex_check_frame(S_matrix_normal,M_matrix_normal,N_matrix_normal,Old_matrix_normal) * undef_data_at(&j))) $ matrix_normal */
 if (rows >= SX_ROWS || p->coef == 0) return SX_UNKNOWN;
/*@ Inv
invalid_inputs: Assert 0 == 1 && emp;
nullcoef_reject: Assert c == C_nullcoef_reject && s == S_nullcoef_reject && inputs == N_nullcoef_reject && pivot_limit == L_nullcoef_reject && 0 <= N_nullcoef_reject && N_nullcoef_reject <= 8 && 0 <= M_nullcoef_reject && M_nullcoef_reject <= 16 && -2147483648 <= L_nullcoef_reject && L_nullcoef_reject <= 2147483647 && Zlength(A_nullcoef_reject) == M_nullcoef_reject*9 && Forall(Z::le(-2147483648),A_nullcoef_reject) && Forall(Z::ge(2147483647),A_nullcoef_reject) && Zlength(P_nullcoef_reject) == M_nullcoef_reject+1 && list == Znth(0,P_nullcoef_reject,0) &&
 NoDup(PS_nullcoef_reject) && NoDup(IS_nullcoef_reject) &&
 (forall (i: Z), (0 <= i && i < M_nullcoef_reject) =>
  (Znth(i,P_nullcoef_reject,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)),PS_nullcoef_reject) &&
   In(simplex_deduction_next_address(Znth(i,P_nullcoef_reject,0)),PS_nullcoef_reject) &&
   PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0))) != 0 &&
   PV_nullcoef_reject(simplex_deduction_next_address(Znth(i,P_nullcoef_reject,0))) == Znth(i+1,P_nullcoef_reject,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_nullcoef_reject && 0 <= h && h <= N_nullcoef_reject) =>
  (In(PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)))+h*sizeof(int),IS_nullcoef_reject) &&
   IV_nullcoef_reject(PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)))+h*sizeof(int)) == Znth(i*9+h,A_nullcoef_reject,0))) && M_nullcoef_reject < 16 && Znth(M_nullcoef_reject,P_nullcoef_reject,0) != 0 && In(simplex_deduction_coef_address(Znth(M_nullcoef_reject,P_nullcoef_reject,0)),PS_nullcoef_reject) && PV_nullcoef_reject(simplex_deduction_coef_address(Znth(M_nullcoef_reject,P_nullcoef_reject,0))) == 0 &&
 0 <= rows && rows < M_nullcoef_reject && p == Znth(rows,P_nullcoef_reject,0) && 0 <= j && j <= N_nullcoef_reject+1 && simplex_deduction_ptrs(PS_nullcoef_reject,PV_nullcoef_reject) * simplex_deduction_ints(IS_nullcoef_reject,IV_nullcoef_reject) * simplex_deduction_workspace(C_nullcoef_reject,A_nullcoef_reject,M_nullcoef_reject,N_nullcoef_reject,rows,j);
bounded_prefix_reject: Assert c == C_bounded_prefix_reject && s == S_bounded_prefix_reject && inputs == N_bounded_prefix_reject && pivot_limit == L_bounded_prefix_reject && 0 <= N_bounded_prefix_reject && N_bounded_prefix_reject <= 8 && 0 <= M_bounded_prefix_reject && M_bounded_prefix_reject <= 16 && -2147483648 <= L_bounded_prefix_reject && L_bounded_prefix_reject <= 2147483647 && Zlength(A_bounded_prefix_reject) == M_bounded_prefix_reject*9 && Forall(Z::le(-2147483648),A_bounded_prefix_reject) && Forall(Z::ge(2147483647),A_bounded_prefix_reject) && Zlength(P_bounded_prefix_reject) == M_bounded_prefix_reject+1 && list == Znth(0,P_bounded_prefix_reject,0) &&
 NoDup(PS_bounded_prefix_reject) && NoDup(IS_bounded_prefix_reject) &&
 (forall (i: Z), (0 <= i && i < M_bounded_prefix_reject) =>
  (Znth(i,P_bounded_prefix_reject,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)),PS_bounded_prefix_reject) &&
   In(simplex_deduction_next_address(Znth(i,P_bounded_prefix_reject,0)),PS_bounded_prefix_reject) &&
   PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0))) != 0 &&
   PV_bounded_prefix_reject(simplex_deduction_next_address(Znth(i,P_bounded_prefix_reject,0))) == Znth(i+1,P_bounded_prefix_reject,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_bounded_prefix_reject && 0 <= h && h <= N_bounded_prefix_reject) =>
  (In(PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)))+h*sizeof(int),IS_bounded_prefix_reject) &&
   IV_bounded_prefix_reject(PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)))+h*sizeof(int)) == Znth(i*9+h,A_bounded_prefix_reject,0))) && M_bounded_prefix_reject == 16 && Znth(M_bounded_prefix_reject,P_bounded_prefix_reject,0) != 0 &&
 0 <= rows && rows < M_bounded_prefix_reject && p == Znth(rows,P_bounded_prefix_reject,0) && 0 <= j && j <= N_bounded_prefix_reject+1 && simplex_deduction_ptrs(PS_bounded_prefix_reject,PV_bounded_prefix_reject) * simplex_deduction_ints(IS_bounded_prefix_reject,IV_bounded_prefix_reject) * simplex_deduction_workspace(C_bounded_prefix_reject,A_bounded_prefix_reject,M_bounded_prefix_reject,N_bounded_prefix_reject,rows,j);
complete_min: Assert c == C_complete_min && s == S_complete_min && inputs == N_complete_min && pivot_limit == L_complete_min && 0 <= N_complete_min && N_complete_min <= 8 && 0 <= M_complete_min && M_complete_min <= 16 && -2147483648 <= L_complete_min && L_complete_min <= 2147483647 && Zlength(A_complete_min) == M_complete_min*9 && Forall(Z::le(-2147483648),A_complete_min) && Forall(Z::ge(2147483647),A_complete_min) && Zlength(P_complete_min) == M_complete_min+1 && list == Znth(0,P_complete_min,0) &&
 NoDup(PS_complete_min) && NoDup(IS_complete_min) &&
 (forall (i: Z), (0 <= i && i < M_complete_min) =>
  (Znth(i,P_complete_min,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_complete_min,0)),PS_complete_min) &&
   In(simplex_deduction_next_address(Znth(i,P_complete_min,0)),PS_complete_min) &&
   PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0))) != 0 &&
   PV_complete_min(simplex_deduction_next_address(Znth(i,P_complete_min,0))) == Znth(i+1,P_complete_min,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_complete_min && 0 <= h && h <= N_complete_min) =>
  (In(PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0)))+h*sizeof(int),IS_complete_min) &&
   IV_complete_min(PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0)))+h*sizeof(int)) == Znth(i*9+h,A_complete_min,0))) && Znth(M_complete_min,P_complete_min,0) == 0 && (exists (x: Z) (y: Z), 0 <= x && x < M_complete_min && 0 <= y && y <= N_complete_min && Znth(x*9+y,A_complete_min,0) == -2147483648) &&
 0 <= rows && rows < M_complete_min && p == Znth(rows,P_complete_min,0) && 0 <= j && j <= N_complete_min+1 && simplex_deduction_ptrs(PS_complete_min,PV_complete_min) * simplex_deduction_ints(IS_complete_min,IV_complete_min) * simplex_deduction_workspace(C_complete_min,A_complete_min,M_complete_min,N_complete_min,rows,j);
zero_negative: Assert p == 0 && rows == 0 && c == C_zero_negative && s == S_zero_negative && inputs == N_zero_negative && pivot_limit == L_zero_negative && 0 <= N_zero_negative && N_zero_negative <= 8 && 0 <= M_zero_negative && M_zero_negative <= 16 && -2147483648 <= L_zero_negative && L_zero_negative <= 2147483647 && Zlength(A_zero_negative) == M_zero_negative*9 && Forall(Z::le(-2147483648),A_zero_negative) && Forall(Z::ge(2147483647),A_zero_negative) && Zlength(P_zero_negative) == M_zero_negative+1 && list == Znth(0,P_zero_negative,0) &&
 NoDup(PS_zero_negative) && NoDup(IS_zero_negative) &&
 (forall (i: Z), (0 <= i && i < M_zero_negative) =>
  (Znth(i,P_zero_negative,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)),PS_zero_negative) &&
   In(simplex_deduction_next_address(Znth(i,P_zero_negative,0)),PS_zero_negative) &&
   PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0))) != 0 &&
   PV_zero_negative(simplex_deduction_next_address(Znth(i,P_zero_negative,0))) == Znth(i+1,P_zero_negative,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_zero_negative && 0 <= h && h <= N_zero_negative) =>
  (In(PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)))+h*sizeof(int),IS_zero_negative) &&
   IV_zero_negative(PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)))+h*sizeof(int)) == Znth(i*9+h,A_zero_negative,0))) && Znth(M_zero_negative,P_zero_negative,0) == 0 && Forall(Z::le(-2147483647),A_zero_negative) && M_zero_negative == 0 && L_zero_negative < 0 &&
 0 <= rows && rows < M_zero_negative && p == Znth(rows,P_zero_negative,0) && 0 <= j && j <= N_zero_negative+1 && simplex_deduction_ptrs(PS_zero_negative,PV_zero_negative) * simplex_deduction_ints(IS_zero_negative,IV_zero_negative) * simplex_check_old(S_zero_negative,0,N_zero_negative,Old_zero_negative) * simplex_check_frame(S_zero_negative,0,N_zero_negative,Old_zero_negative) * simplex_deduction_workspace(C_zero_negative,A_zero_negative,M_zero_negative,N_zero_negative,rows,j);
zero_normal: Assert p == 0 && rows == 0 && c == C_zero_normal && s == S_zero_normal && inputs == N_zero_normal && pivot_limit == L_zero_normal && 0 <= N_zero_normal && N_zero_normal <= 8 && 0 <= M_zero_normal && M_zero_normal <= 16 && -2147483648 <= L_zero_normal && L_zero_normal <= 2147483647 && Zlength(A_zero_normal) == M_zero_normal*9 && Forall(Z::le(-2147483648),A_zero_normal) && Forall(Z::ge(2147483647),A_zero_normal) && Zlength(P_zero_normal) == M_zero_normal+1 && list == Znth(0,P_zero_normal,0) &&
 NoDup(PS_zero_normal) && NoDup(IS_zero_normal) &&
 (forall (i: Z), (0 <= i && i < M_zero_normal) =>
  (Znth(i,P_zero_normal,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)),PS_zero_normal) &&
   In(simplex_deduction_next_address(Znth(i,P_zero_normal,0)),PS_zero_normal) &&
   PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0))) != 0 &&
   PV_zero_normal(simplex_deduction_next_address(Znth(i,P_zero_normal,0))) == Znth(i+1,P_zero_normal,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_zero_normal && 0 <= h && h <= N_zero_normal) =>
  (In(PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)))+h*sizeof(int),IS_zero_normal) &&
   IV_zero_normal(PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)))+h*sizeof(int)) == Znth(i*9+h,A_zero_normal,0))) && Znth(M_zero_normal,P_zero_normal,0) == 0 && Forall(Z::le(-2147483647),A_zero_normal) && M_zero_normal == 0 && 0 <= L_zero_normal &&
 0 <= rows && rows < M_zero_normal && p == Znth(rows,P_zero_normal,0) && 0 <= j && j <= N_zero_normal+1 && simplex_deduction_ptrs(PS_zero_normal,PV_zero_normal) * simplex_deduction_ints(IS_zero_normal,IV_zero_normal) * simplex_check_old(S_zero_normal,0,N_zero_normal,Old_zero_normal) * simplex_check_frame(S_zero_normal,0,N_zero_normal,Old_zero_normal) * simplex_deduction_workspace(C_zero_normal,A_zero_normal,M_zero_normal,N_zero_normal,rows,j);
matrix_negative: Assert c == C_matrix_negative && s == S_matrix_negative && inputs == N_matrix_negative && pivot_limit == L_matrix_negative && 0 <= N_matrix_negative && N_matrix_negative <= 8 && 0 <= M_matrix_negative && M_matrix_negative <= 16 && -2147483648 <= L_matrix_negative && L_matrix_negative <= 2147483647 && Zlength(A_matrix_negative) == M_matrix_negative*9 && Forall(Z::le(-2147483648),A_matrix_negative) && Forall(Z::ge(2147483647),A_matrix_negative) && Zlength(P_matrix_negative) == M_matrix_negative+1 && list == Znth(0,P_matrix_negative,0) &&
 NoDup(PS_matrix_negative) && NoDup(IS_matrix_negative) &&
 (forall (i: Z), (0 <= i && i < M_matrix_negative) =>
  (Znth(i,P_matrix_negative,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)),PS_matrix_negative) &&
   In(simplex_deduction_next_address(Znth(i,P_matrix_negative,0)),PS_matrix_negative) &&
   PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0))) != 0 &&
   PV_matrix_negative(simplex_deduction_next_address(Znth(i,P_matrix_negative,0))) == Znth(i+1,P_matrix_negative,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_matrix_negative && 0 <= h && h <= N_matrix_negative) =>
  (In(PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)))+h*sizeof(int),IS_matrix_negative) &&
   IV_matrix_negative(PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)))+h*sizeof(int)) == Znth(i*9+h,A_matrix_negative,0))) && Znth(M_matrix_negative,P_matrix_negative,0) == 0 && Forall(Z::le(-2147483647),A_matrix_negative) && 1 <= M_matrix_negative && L_matrix_negative < 0 &&
 0 <= rows && rows < M_matrix_negative && p == Znth(rows,P_matrix_negative,0) && 0 <= j && j <= N_matrix_negative+1 && simplex_deduction_ptrs(PS_matrix_negative,PV_matrix_negative) * simplex_deduction_ints(IS_matrix_negative,IV_matrix_negative) * simplex_check_old(S_matrix_negative,M_matrix_negative,N_matrix_negative,Old_matrix_negative) * simplex_check_frame(S_matrix_negative,M_matrix_negative,N_matrix_negative,Old_matrix_negative) * simplex_deduction_workspace(C_matrix_negative,A_matrix_negative,M_matrix_negative,N_matrix_negative,rows,j) * simplex_check_input_frame(C_matrix_negative,M_matrix_negative,N_matrix_negative,CO_matrix_negative);
matrix_normal: Assert c == C_matrix_normal && s == S_matrix_normal && inputs == N_matrix_normal && pivot_limit == L_matrix_normal && 0 <= N_matrix_normal && N_matrix_normal <= 8 && 0 <= M_matrix_normal && M_matrix_normal <= 16 && -2147483648 <= L_matrix_normal && L_matrix_normal <= 2147483647 && Zlength(A_matrix_normal) == M_matrix_normal*9 && Forall(Z::le(-2147483648),A_matrix_normal) && Forall(Z::ge(2147483647),A_matrix_normal) && Zlength(P_matrix_normal) == M_matrix_normal+1 && list == Znth(0,P_matrix_normal,0) &&
 NoDup(PS_matrix_normal) && NoDup(IS_matrix_normal) &&
 (forall (i: Z), (0 <= i && i < M_matrix_normal) =>
  (Znth(i,P_matrix_normal,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)),PS_matrix_normal) &&
   In(simplex_deduction_next_address(Znth(i,P_matrix_normal,0)),PS_matrix_normal) &&
   PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0))) != 0 &&
   PV_matrix_normal(simplex_deduction_next_address(Znth(i,P_matrix_normal,0))) == Znth(i+1,P_matrix_normal,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_matrix_normal && 0 <= h && h <= N_matrix_normal) =>
  (In(PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)))+h*sizeof(int),IS_matrix_normal) &&
   IV_matrix_normal(PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)))+h*sizeof(int)) == Znth(i*9+h,A_matrix_normal,0))) && Znth(M_matrix_normal,P_matrix_normal,0) == 0 && Forall(Z::le(-2147483647),A_matrix_normal) && 1 <= M_matrix_normal && 0 <= L_matrix_normal &&
 0 <= rows && rows < M_matrix_normal && p == Znth(rows,P_matrix_normal,0) && 0 <= j && j <= N_matrix_normal+1 && simplex_deduction_ptrs(PS_matrix_normal,PV_matrix_normal) * simplex_deduction_ints(IS_matrix_normal,IV_matrix_normal) * simplex_check_old(S_matrix_normal,M_matrix_normal,N_matrix_normal,Old_matrix_normal) * simplex_check_frame(S_matrix_normal,M_matrix_normal,N_matrix_normal,Old_matrix_normal) * simplex_deduction_workspace(C_matrix_normal,A_matrix_normal,M_matrix_normal,N_matrix_normal,rows,j) * simplex_check_input_frame(C_matrix_normal,M_matrix_normal,N_matrix_normal,CO_matrix_normal) */
 for (j = 0; j <= inputs; j++)
/*@ Assert c == C_nullcoef_reject && s == S_nullcoef_reject && inputs == N_nullcoef_reject && pivot_limit == L_nullcoef_reject && 0 <= N_nullcoef_reject && N_nullcoef_reject <= 8 && 0 <= M_nullcoef_reject && M_nullcoef_reject <= 16 && -2147483648 <= L_nullcoef_reject && L_nullcoef_reject <= 2147483647 && Zlength(A_nullcoef_reject) == M_nullcoef_reject*9 && Forall(Z::le(-2147483648),A_nullcoef_reject) && Forall(Z::ge(2147483647),A_nullcoef_reject) && Zlength(P_nullcoef_reject) == M_nullcoef_reject+1 && list == Znth(0,P_nullcoef_reject,0) &&
 NoDup(PS_nullcoef_reject) && NoDup(IS_nullcoef_reject) &&
 (forall (i: Z), (0 <= i && i < M_nullcoef_reject) =>
  (Znth(i,P_nullcoef_reject,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)),PS_nullcoef_reject) &&
   In(simplex_deduction_next_address(Znth(i,P_nullcoef_reject,0)),PS_nullcoef_reject) &&
   PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0))) != 0 &&
   PV_nullcoef_reject(simplex_deduction_next_address(Znth(i,P_nullcoef_reject,0))) == Znth(i+1,P_nullcoef_reject,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_nullcoef_reject && 0 <= h && h <= N_nullcoef_reject) =>
  (In(PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)))+h*sizeof(int),IS_nullcoef_reject) &&
   IV_nullcoef_reject(PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)))+h*sizeof(int)) == Znth(i*9+h,A_nullcoef_reject,0))) && M_nullcoef_reject < 16 && Znth(M_nullcoef_reject,P_nullcoef_reject,0) != 0 && In(simplex_deduction_coef_address(Znth(M_nullcoef_reject,P_nullcoef_reject,0)),PS_nullcoef_reject) && PV_nullcoef_reject(simplex_deduction_coef_address(Znth(M_nullcoef_reject,P_nullcoef_reject,0))) == 0 &&
 0 <= rows && rows < M_nullcoef_reject && p == Znth(rows,P_nullcoef_reject,0) && 0 <= j && j <= N_nullcoef_reject && IV_nullcoef_reject(PV_nullcoef_reject(simplex_deduction_coef_address(p))+j*sizeof(int)) == Znth(rows*9+j,A_nullcoef_reject,0) && data_at(&(p->coef), int *, PV_nullcoef_reject(simplex_deduction_coef_address(p))) * simplex_deduction_ptrs_without(PS_nullcoef_reject,PV_nullcoef_reject,&(p->coef)) * data_at(pointer_offset(PV_nullcoef_reject(simplex_deduction_coef_address(p)),j,int), int, IV_nullcoef_reject(PV_nullcoef_reject(simplex_deduction_coef_address(p))+j*sizeof(int))) * simplex_deduction_ints_without(IS_nullcoef_reject,IV_nullcoef_reject,PV_nullcoef_reject(simplex_deduction_coef_address(p))+j*sizeof(int)) * simplex_deduction_workspace_except(C_nullcoef_reject,A_nullcoef_reject,M_nullcoef_reject,N_nullcoef_reject,rows,j) * undef_data_at(pointer_offset(pointer_offset(C_nullcoef_reject,rows,int[9]),j,int), int) $ nullcoef_reject */
/*@ Assert c == C_bounded_prefix_reject && s == S_bounded_prefix_reject && inputs == N_bounded_prefix_reject && pivot_limit == L_bounded_prefix_reject && 0 <= N_bounded_prefix_reject && N_bounded_prefix_reject <= 8 && 0 <= M_bounded_prefix_reject && M_bounded_prefix_reject <= 16 && -2147483648 <= L_bounded_prefix_reject && L_bounded_prefix_reject <= 2147483647 && Zlength(A_bounded_prefix_reject) == M_bounded_prefix_reject*9 && Forall(Z::le(-2147483648),A_bounded_prefix_reject) && Forall(Z::ge(2147483647),A_bounded_prefix_reject) && Zlength(P_bounded_prefix_reject) == M_bounded_prefix_reject+1 && list == Znth(0,P_bounded_prefix_reject,0) &&
 NoDup(PS_bounded_prefix_reject) && NoDup(IS_bounded_prefix_reject) &&
 (forall (i: Z), (0 <= i && i < M_bounded_prefix_reject) =>
  (Znth(i,P_bounded_prefix_reject,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)),PS_bounded_prefix_reject) &&
   In(simplex_deduction_next_address(Znth(i,P_bounded_prefix_reject,0)),PS_bounded_prefix_reject) &&
   PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0))) != 0 &&
   PV_bounded_prefix_reject(simplex_deduction_next_address(Znth(i,P_bounded_prefix_reject,0))) == Znth(i+1,P_bounded_prefix_reject,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_bounded_prefix_reject && 0 <= h && h <= N_bounded_prefix_reject) =>
  (In(PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)))+h*sizeof(int),IS_bounded_prefix_reject) &&
   IV_bounded_prefix_reject(PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)))+h*sizeof(int)) == Znth(i*9+h,A_bounded_prefix_reject,0))) && M_bounded_prefix_reject == 16 && Znth(M_bounded_prefix_reject,P_bounded_prefix_reject,0) != 0 &&
 0 <= rows && rows < M_bounded_prefix_reject && p == Znth(rows,P_bounded_prefix_reject,0) && 0 <= j && j <= N_bounded_prefix_reject && IV_bounded_prefix_reject(PV_bounded_prefix_reject(simplex_deduction_coef_address(p))+j*sizeof(int)) == Znth(rows*9+j,A_bounded_prefix_reject,0) && data_at(&(p->coef), int *, PV_bounded_prefix_reject(simplex_deduction_coef_address(p))) * simplex_deduction_ptrs_without(PS_bounded_prefix_reject,PV_bounded_prefix_reject,&(p->coef)) * data_at(pointer_offset(PV_bounded_prefix_reject(simplex_deduction_coef_address(p)),j,int), int, IV_bounded_prefix_reject(PV_bounded_prefix_reject(simplex_deduction_coef_address(p))+j*sizeof(int))) * simplex_deduction_ints_without(IS_bounded_prefix_reject,IV_bounded_prefix_reject,PV_bounded_prefix_reject(simplex_deduction_coef_address(p))+j*sizeof(int)) * simplex_deduction_workspace_except(C_bounded_prefix_reject,A_bounded_prefix_reject,M_bounded_prefix_reject,N_bounded_prefix_reject,rows,j) * undef_data_at(pointer_offset(pointer_offset(C_bounded_prefix_reject,rows,int[9]),j,int), int) $ bounded_prefix_reject */
/*@ Assert c == C_complete_min && s == S_complete_min && inputs == N_complete_min && pivot_limit == L_complete_min && 0 <= N_complete_min && N_complete_min <= 8 && 0 <= M_complete_min && M_complete_min <= 16 && -2147483648 <= L_complete_min && L_complete_min <= 2147483647 && Zlength(A_complete_min) == M_complete_min*9 && Forall(Z::le(-2147483648),A_complete_min) && Forall(Z::ge(2147483647),A_complete_min) && Zlength(P_complete_min) == M_complete_min+1 && list == Znth(0,P_complete_min,0) &&
 NoDup(PS_complete_min) && NoDup(IS_complete_min) &&
 (forall (i: Z), (0 <= i && i < M_complete_min) =>
  (Znth(i,P_complete_min,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_complete_min,0)),PS_complete_min) &&
   In(simplex_deduction_next_address(Znth(i,P_complete_min,0)),PS_complete_min) &&
   PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0))) != 0 &&
   PV_complete_min(simplex_deduction_next_address(Znth(i,P_complete_min,0))) == Znth(i+1,P_complete_min,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_complete_min && 0 <= h && h <= N_complete_min) =>
  (In(PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0)))+h*sizeof(int),IS_complete_min) &&
   IV_complete_min(PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0)))+h*sizeof(int)) == Znth(i*9+h,A_complete_min,0))) && Znth(M_complete_min,P_complete_min,0) == 0 && (exists (x: Z) (y: Z), 0 <= x && x < M_complete_min && 0 <= y && y <= N_complete_min && Znth(x*9+y,A_complete_min,0) == -2147483648) &&
 0 <= rows && rows < M_complete_min && p == Znth(rows,P_complete_min,0) && 0 <= j && j <= N_complete_min && IV_complete_min(PV_complete_min(simplex_deduction_coef_address(p))+j*sizeof(int)) == Znth(rows*9+j,A_complete_min,0) && data_at(&(p->coef), int *, PV_complete_min(simplex_deduction_coef_address(p))) * simplex_deduction_ptrs_without(PS_complete_min,PV_complete_min,&(p->coef)) * data_at(pointer_offset(PV_complete_min(simplex_deduction_coef_address(p)),j,int), int, IV_complete_min(PV_complete_min(simplex_deduction_coef_address(p))+j*sizeof(int))) * simplex_deduction_ints_without(IS_complete_min,IV_complete_min,PV_complete_min(simplex_deduction_coef_address(p))+j*sizeof(int)) * simplex_deduction_workspace_except(C_complete_min,A_complete_min,M_complete_min,N_complete_min,rows,j) * undef_data_at(pointer_offset(pointer_offset(C_complete_min,rows,int[9]),j,int), int) $ complete_min */
/*@ Assert c == C_zero_negative && s == S_zero_negative && inputs == N_zero_negative && pivot_limit == L_zero_negative && 0 <= N_zero_negative && N_zero_negative <= 8 && 0 <= M_zero_negative && M_zero_negative <= 16 && -2147483648 <= L_zero_negative && L_zero_negative <= 2147483647 && Zlength(A_zero_negative) == M_zero_negative*9 && Forall(Z::le(-2147483648),A_zero_negative) && Forall(Z::ge(2147483647),A_zero_negative) && Zlength(P_zero_negative) == M_zero_negative+1 && list == Znth(0,P_zero_negative,0) &&
 NoDup(PS_zero_negative) && NoDup(IS_zero_negative) &&
 (forall (i: Z), (0 <= i && i < M_zero_negative) =>
  (Znth(i,P_zero_negative,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)),PS_zero_negative) &&
   In(simplex_deduction_next_address(Znth(i,P_zero_negative,0)),PS_zero_negative) &&
   PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0))) != 0 &&
   PV_zero_negative(simplex_deduction_next_address(Znth(i,P_zero_negative,0))) == Znth(i+1,P_zero_negative,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_zero_negative && 0 <= h && h <= N_zero_negative) =>
  (In(PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)))+h*sizeof(int),IS_zero_negative) &&
   IV_zero_negative(PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)))+h*sizeof(int)) == Znth(i*9+h,A_zero_negative,0))) && Znth(M_zero_negative,P_zero_negative,0) == 0 && Forall(Z::le(-2147483647),A_zero_negative) && M_zero_negative == 0 && L_zero_negative < 0 &&
 0 <= rows && rows < M_zero_negative && p == Znth(rows,P_zero_negative,0) && 0 <= j && j <= N_zero_negative && IV_zero_negative(PV_zero_negative(simplex_deduction_coef_address(p))+j*sizeof(int)) == Znth(rows*9+j,A_zero_negative,0) && data_at(&(p->coef), int *, PV_zero_negative(simplex_deduction_coef_address(p))) * simplex_deduction_ptrs_without(PS_zero_negative,PV_zero_negative,&(p->coef)) * data_at(pointer_offset(PV_zero_negative(simplex_deduction_coef_address(p)),j,int), int, IV_zero_negative(PV_zero_negative(simplex_deduction_coef_address(p))+j*sizeof(int))) * simplex_deduction_ints_without(IS_zero_negative,IV_zero_negative,PV_zero_negative(simplex_deduction_coef_address(p))+j*sizeof(int)) * simplex_deduction_workspace_except(C_zero_negative,A_zero_negative,M_zero_negative,N_zero_negative,rows,j) * undef_data_at(pointer_offset(pointer_offset(C_zero_negative,rows,int[9]),j,int), int) * simplex_check_old(S_zero_negative,0,N_zero_negative,Old_zero_negative) * simplex_check_frame(S_zero_negative,0,N_zero_negative,Old_zero_negative) $ zero_negative */
/*@ Assert c == C_zero_normal && s == S_zero_normal && inputs == N_zero_normal && pivot_limit == L_zero_normal && 0 <= N_zero_normal && N_zero_normal <= 8 && 0 <= M_zero_normal && M_zero_normal <= 16 && -2147483648 <= L_zero_normal && L_zero_normal <= 2147483647 && Zlength(A_zero_normal) == M_zero_normal*9 && Forall(Z::le(-2147483648),A_zero_normal) && Forall(Z::ge(2147483647),A_zero_normal) && Zlength(P_zero_normal) == M_zero_normal+1 && list == Znth(0,P_zero_normal,0) &&
 NoDup(PS_zero_normal) && NoDup(IS_zero_normal) &&
 (forall (i: Z), (0 <= i && i < M_zero_normal) =>
  (Znth(i,P_zero_normal,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)),PS_zero_normal) &&
   In(simplex_deduction_next_address(Znth(i,P_zero_normal,0)),PS_zero_normal) &&
   PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0))) != 0 &&
   PV_zero_normal(simplex_deduction_next_address(Znth(i,P_zero_normal,0))) == Znth(i+1,P_zero_normal,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_zero_normal && 0 <= h && h <= N_zero_normal) =>
  (In(PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)))+h*sizeof(int),IS_zero_normal) &&
   IV_zero_normal(PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)))+h*sizeof(int)) == Znth(i*9+h,A_zero_normal,0))) && Znth(M_zero_normal,P_zero_normal,0) == 0 && Forall(Z::le(-2147483647),A_zero_normal) && M_zero_normal == 0 && 0 <= L_zero_normal &&
 0 <= rows && rows < M_zero_normal && p == Znth(rows,P_zero_normal,0) && 0 <= j && j <= N_zero_normal && IV_zero_normal(PV_zero_normal(simplex_deduction_coef_address(p))+j*sizeof(int)) == Znth(rows*9+j,A_zero_normal,0) && data_at(&(p->coef), int *, PV_zero_normal(simplex_deduction_coef_address(p))) * simplex_deduction_ptrs_without(PS_zero_normal,PV_zero_normal,&(p->coef)) * data_at(pointer_offset(PV_zero_normal(simplex_deduction_coef_address(p)),j,int), int, IV_zero_normal(PV_zero_normal(simplex_deduction_coef_address(p))+j*sizeof(int))) * simplex_deduction_ints_without(IS_zero_normal,IV_zero_normal,PV_zero_normal(simplex_deduction_coef_address(p))+j*sizeof(int)) * simplex_deduction_workspace_except(C_zero_normal,A_zero_normal,M_zero_normal,N_zero_normal,rows,j) * undef_data_at(pointer_offset(pointer_offset(C_zero_normal,rows,int[9]),j,int), int) * simplex_check_old(S_zero_normal,0,N_zero_normal,Old_zero_normal) * simplex_check_frame(S_zero_normal,0,N_zero_normal,Old_zero_normal) $ zero_normal */
/*@ Assert c == C_matrix_negative && s == S_matrix_negative && inputs == N_matrix_negative && pivot_limit == L_matrix_negative && 0 <= N_matrix_negative && N_matrix_negative <= 8 && 0 <= M_matrix_negative && M_matrix_negative <= 16 && -2147483648 <= L_matrix_negative && L_matrix_negative <= 2147483647 && Zlength(A_matrix_negative) == M_matrix_negative*9 && Forall(Z::le(-2147483648),A_matrix_negative) && Forall(Z::ge(2147483647),A_matrix_negative) && Zlength(P_matrix_negative) == M_matrix_negative+1 && list == Znth(0,P_matrix_negative,0) &&
 NoDup(PS_matrix_negative) && NoDup(IS_matrix_negative) &&
 (forall (i: Z), (0 <= i && i < M_matrix_negative) =>
  (Znth(i,P_matrix_negative,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)),PS_matrix_negative) &&
   In(simplex_deduction_next_address(Znth(i,P_matrix_negative,0)),PS_matrix_negative) &&
   PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0))) != 0 &&
   PV_matrix_negative(simplex_deduction_next_address(Znth(i,P_matrix_negative,0))) == Znth(i+1,P_matrix_negative,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_matrix_negative && 0 <= h && h <= N_matrix_negative) =>
  (In(PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)))+h*sizeof(int),IS_matrix_negative) &&
   IV_matrix_negative(PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)))+h*sizeof(int)) == Znth(i*9+h,A_matrix_negative,0))) && Znth(M_matrix_negative,P_matrix_negative,0) == 0 && Forall(Z::le(-2147483647),A_matrix_negative) && 1 <= M_matrix_negative && L_matrix_negative < 0 &&
 0 <= rows && rows < M_matrix_negative && p == Znth(rows,P_matrix_negative,0) && 0 <= j && j <= N_matrix_negative && IV_matrix_negative(PV_matrix_negative(simplex_deduction_coef_address(p))+j*sizeof(int)) == Znth(rows*9+j,A_matrix_negative,0) && data_at(&(p->coef), int *, PV_matrix_negative(simplex_deduction_coef_address(p))) * simplex_deduction_ptrs_without(PS_matrix_negative,PV_matrix_negative,&(p->coef)) * data_at(pointer_offset(PV_matrix_negative(simplex_deduction_coef_address(p)),j,int), int, IV_matrix_negative(PV_matrix_negative(simplex_deduction_coef_address(p))+j*sizeof(int))) * simplex_deduction_ints_without(IS_matrix_negative,IV_matrix_negative,PV_matrix_negative(simplex_deduction_coef_address(p))+j*sizeof(int)) * simplex_deduction_workspace_except(C_matrix_negative,A_matrix_negative,M_matrix_negative,N_matrix_negative,rows,j) * undef_data_at(pointer_offset(pointer_offset(C_matrix_negative,rows,int[9]),j,int), int) * simplex_check_old(S_matrix_negative,M_matrix_negative,N_matrix_negative,Old_matrix_negative) * simplex_check_frame(S_matrix_negative,M_matrix_negative,N_matrix_negative,Old_matrix_negative) * simplex_check_input_frame(C_matrix_negative,M_matrix_negative,N_matrix_negative,CO_matrix_negative) $ matrix_negative */
/*@ Assert c == C_matrix_normal && s == S_matrix_normal && inputs == N_matrix_normal && pivot_limit == L_matrix_normal && 0 <= N_matrix_normal && N_matrix_normal <= 8 && 0 <= M_matrix_normal && M_matrix_normal <= 16 && -2147483648 <= L_matrix_normal && L_matrix_normal <= 2147483647 && Zlength(A_matrix_normal) == M_matrix_normal*9 && Forall(Z::le(-2147483648),A_matrix_normal) && Forall(Z::ge(2147483647),A_matrix_normal) && Zlength(P_matrix_normal) == M_matrix_normal+1 && list == Znth(0,P_matrix_normal,0) &&
 NoDup(PS_matrix_normal) && NoDup(IS_matrix_normal) &&
 (forall (i: Z), (0 <= i && i < M_matrix_normal) =>
  (Znth(i,P_matrix_normal,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)),PS_matrix_normal) &&
   In(simplex_deduction_next_address(Znth(i,P_matrix_normal,0)),PS_matrix_normal) &&
   PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0))) != 0 &&
   PV_matrix_normal(simplex_deduction_next_address(Znth(i,P_matrix_normal,0))) == Znth(i+1,P_matrix_normal,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_matrix_normal && 0 <= h && h <= N_matrix_normal) =>
  (In(PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)))+h*sizeof(int),IS_matrix_normal) &&
   IV_matrix_normal(PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)))+h*sizeof(int)) == Znth(i*9+h,A_matrix_normal,0))) && Znth(M_matrix_normal,P_matrix_normal,0) == 0 && Forall(Z::le(-2147483647),A_matrix_normal) && 1 <= M_matrix_normal && 0 <= L_matrix_normal &&
 0 <= rows && rows < M_matrix_normal && p == Znth(rows,P_matrix_normal,0) && 0 <= j && j <= N_matrix_normal && IV_matrix_normal(PV_matrix_normal(simplex_deduction_coef_address(p))+j*sizeof(int)) == Znth(rows*9+j,A_matrix_normal,0) && data_at(&(p->coef), int *, PV_matrix_normal(simplex_deduction_coef_address(p))) * simplex_deduction_ptrs_without(PS_matrix_normal,PV_matrix_normal,&(p->coef)) * data_at(pointer_offset(PV_matrix_normal(simplex_deduction_coef_address(p)),j,int), int, IV_matrix_normal(PV_matrix_normal(simplex_deduction_coef_address(p))+j*sizeof(int))) * simplex_deduction_ints_without(IS_matrix_normal,IV_matrix_normal,PV_matrix_normal(simplex_deduction_coef_address(p))+j*sizeof(int)) * simplex_deduction_workspace_except(C_matrix_normal,A_matrix_normal,M_matrix_normal,N_matrix_normal,rows,j) * undef_data_at(pointer_offset(pointer_offset(C_matrix_normal,rows,int[9]),j,int), int) * simplex_check_old(S_matrix_normal,M_matrix_normal,N_matrix_normal,Old_matrix_normal) * simplex_check_frame(S_matrix_normal,M_matrix_normal,N_matrix_normal,Old_matrix_normal) * simplex_check_input_frame(C_matrix_normal,M_matrix_normal,N_matrix_normal,CO_matrix_normal) $ matrix_normal */
 c[rows][j] = p->coef[j];
 rows++;
/*@ Assert c == C_nullcoef_reject && s == S_nullcoef_reject && inputs == N_nullcoef_reject && pivot_limit == L_nullcoef_reject && 0 <= N_nullcoef_reject && N_nullcoef_reject <= 8 && 0 <= M_nullcoef_reject && M_nullcoef_reject <= 16 && -2147483648 <= L_nullcoef_reject && L_nullcoef_reject <= 2147483647 && Zlength(A_nullcoef_reject) == M_nullcoef_reject*9 && Forall(Z::le(-2147483648),A_nullcoef_reject) && Forall(Z::ge(2147483647),A_nullcoef_reject) && Zlength(P_nullcoef_reject) == M_nullcoef_reject+1 && list == Znth(0,P_nullcoef_reject,0) &&
 NoDup(PS_nullcoef_reject) && NoDup(IS_nullcoef_reject) &&
 (forall (i: Z), (0 <= i && i < M_nullcoef_reject) =>
  (Znth(i,P_nullcoef_reject,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)),PS_nullcoef_reject) &&
   In(simplex_deduction_next_address(Znth(i,P_nullcoef_reject,0)),PS_nullcoef_reject) &&
   PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0))) != 0 &&
   PV_nullcoef_reject(simplex_deduction_next_address(Znth(i,P_nullcoef_reject,0))) == Znth(i+1,P_nullcoef_reject,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_nullcoef_reject && 0 <= h && h <= N_nullcoef_reject) =>
  (In(PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)))+h*sizeof(int),IS_nullcoef_reject) &&
   IV_nullcoef_reject(PV_nullcoef_reject(simplex_deduction_coef_address(Znth(i,P_nullcoef_reject,0)))+h*sizeof(int)) == Znth(i*9+h,A_nullcoef_reject,0))) && M_nullcoef_reject < 16 && Znth(M_nullcoef_reject,P_nullcoef_reject,0) != 0 && In(simplex_deduction_coef_address(Znth(M_nullcoef_reject,P_nullcoef_reject,0)),PS_nullcoef_reject) && PV_nullcoef_reject(simplex_deduction_coef_address(Znth(M_nullcoef_reject,P_nullcoef_reject,0))) == 0 &&
 1 <= rows && rows <= M_nullcoef_reject && p == Znth(rows-1,P_nullcoef_reject,0) && data_at(&(p->next), struct InequList *, Znth(rows,P_nullcoef_reject,0)) * simplex_deduction_ptrs_without(PS_nullcoef_reject,PV_nullcoef_reject,&(p->next)) * simplex_deduction_ints(IS_nullcoef_reject,IV_nullcoef_reject) * simplex_deduction_workspace(C_nullcoef_reject,A_nullcoef_reject,M_nullcoef_reject,N_nullcoef_reject,rows,0) * data_at(&j, int, N_nullcoef_reject+1) $ nullcoef_reject */
/*@ Assert c == C_bounded_prefix_reject && s == S_bounded_prefix_reject && inputs == N_bounded_prefix_reject && pivot_limit == L_bounded_prefix_reject && 0 <= N_bounded_prefix_reject && N_bounded_prefix_reject <= 8 && 0 <= M_bounded_prefix_reject && M_bounded_prefix_reject <= 16 && -2147483648 <= L_bounded_prefix_reject && L_bounded_prefix_reject <= 2147483647 && Zlength(A_bounded_prefix_reject) == M_bounded_prefix_reject*9 && Forall(Z::le(-2147483648),A_bounded_prefix_reject) && Forall(Z::ge(2147483647),A_bounded_prefix_reject) && Zlength(P_bounded_prefix_reject) == M_bounded_prefix_reject+1 && list == Znth(0,P_bounded_prefix_reject,0) &&
 NoDup(PS_bounded_prefix_reject) && NoDup(IS_bounded_prefix_reject) &&
 (forall (i: Z), (0 <= i && i < M_bounded_prefix_reject) =>
  (Znth(i,P_bounded_prefix_reject,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)),PS_bounded_prefix_reject) &&
   In(simplex_deduction_next_address(Znth(i,P_bounded_prefix_reject,0)),PS_bounded_prefix_reject) &&
   PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0))) != 0 &&
   PV_bounded_prefix_reject(simplex_deduction_next_address(Znth(i,P_bounded_prefix_reject,0))) == Znth(i+1,P_bounded_prefix_reject,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_bounded_prefix_reject && 0 <= h && h <= N_bounded_prefix_reject) =>
  (In(PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)))+h*sizeof(int),IS_bounded_prefix_reject) &&
   IV_bounded_prefix_reject(PV_bounded_prefix_reject(simplex_deduction_coef_address(Znth(i,P_bounded_prefix_reject,0)))+h*sizeof(int)) == Znth(i*9+h,A_bounded_prefix_reject,0))) && M_bounded_prefix_reject == 16 && Znth(M_bounded_prefix_reject,P_bounded_prefix_reject,0) != 0 &&
 1 <= rows && rows <= M_bounded_prefix_reject && p == Znth(rows-1,P_bounded_prefix_reject,0) && data_at(&(p->next), struct InequList *, Znth(rows,P_bounded_prefix_reject,0)) * simplex_deduction_ptrs_without(PS_bounded_prefix_reject,PV_bounded_prefix_reject,&(p->next)) * simplex_deduction_ints(IS_bounded_prefix_reject,IV_bounded_prefix_reject) * simplex_deduction_workspace(C_bounded_prefix_reject,A_bounded_prefix_reject,M_bounded_prefix_reject,N_bounded_prefix_reject,rows,0) * data_at(&j, int, N_bounded_prefix_reject+1) $ bounded_prefix_reject */
/*@ Assert c == C_complete_min && s == S_complete_min && inputs == N_complete_min && pivot_limit == L_complete_min && 0 <= N_complete_min && N_complete_min <= 8 && 0 <= M_complete_min && M_complete_min <= 16 && -2147483648 <= L_complete_min && L_complete_min <= 2147483647 && Zlength(A_complete_min) == M_complete_min*9 && Forall(Z::le(-2147483648),A_complete_min) && Forall(Z::ge(2147483647),A_complete_min) && Zlength(P_complete_min) == M_complete_min+1 && list == Znth(0,P_complete_min,0) &&
 NoDup(PS_complete_min) && NoDup(IS_complete_min) &&
 (forall (i: Z), (0 <= i && i < M_complete_min) =>
  (Znth(i,P_complete_min,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_complete_min,0)),PS_complete_min) &&
   In(simplex_deduction_next_address(Znth(i,P_complete_min,0)),PS_complete_min) &&
   PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0))) != 0 &&
   PV_complete_min(simplex_deduction_next_address(Znth(i,P_complete_min,0))) == Znth(i+1,P_complete_min,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_complete_min && 0 <= h && h <= N_complete_min) =>
  (In(PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0)))+h*sizeof(int),IS_complete_min) &&
   IV_complete_min(PV_complete_min(simplex_deduction_coef_address(Znth(i,P_complete_min,0)))+h*sizeof(int)) == Znth(i*9+h,A_complete_min,0))) && Znth(M_complete_min,P_complete_min,0) == 0 && (exists (x: Z) (y: Z), 0 <= x && x < M_complete_min && 0 <= y && y <= N_complete_min && Znth(x*9+y,A_complete_min,0) == -2147483648) &&
 1 <= rows && rows <= M_complete_min && p == Znth(rows-1,P_complete_min,0) && data_at(&(p->next), struct InequList *, Znth(rows,P_complete_min,0)) * simplex_deduction_ptrs_without(PS_complete_min,PV_complete_min,&(p->next)) * simplex_deduction_ints(IS_complete_min,IV_complete_min) * simplex_deduction_workspace(C_complete_min,A_complete_min,M_complete_min,N_complete_min,rows,0) * data_at(&j, int, N_complete_min+1) $ complete_min */
/*@ Assert c == C_zero_negative && s == S_zero_negative && inputs == N_zero_negative && pivot_limit == L_zero_negative && 0 <= N_zero_negative && N_zero_negative <= 8 && 0 <= M_zero_negative && M_zero_negative <= 16 && -2147483648 <= L_zero_negative && L_zero_negative <= 2147483647 && Zlength(A_zero_negative) == M_zero_negative*9 && Forall(Z::le(-2147483648),A_zero_negative) && Forall(Z::ge(2147483647),A_zero_negative) && Zlength(P_zero_negative) == M_zero_negative+1 && list == Znth(0,P_zero_negative,0) &&
 NoDup(PS_zero_negative) && NoDup(IS_zero_negative) &&
 (forall (i: Z), (0 <= i && i < M_zero_negative) =>
  (Znth(i,P_zero_negative,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)),PS_zero_negative) &&
   In(simplex_deduction_next_address(Znth(i,P_zero_negative,0)),PS_zero_negative) &&
   PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0))) != 0 &&
   PV_zero_negative(simplex_deduction_next_address(Znth(i,P_zero_negative,0))) == Znth(i+1,P_zero_negative,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_zero_negative && 0 <= h && h <= N_zero_negative) =>
  (In(PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)))+h*sizeof(int),IS_zero_negative) &&
   IV_zero_negative(PV_zero_negative(simplex_deduction_coef_address(Znth(i,P_zero_negative,0)))+h*sizeof(int)) == Znth(i*9+h,A_zero_negative,0))) && Znth(M_zero_negative,P_zero_negative,0) == 0 && Forall(Z::le(-2147483647),A_zero_negative) && M_zero_negative == 0 && L_zero_negative < 0 &&
 1 <= rows && rows <= M_zero_negative && p == Znth(rows-1,P_zero_negative,0) && data_at(&(p->next), struct InequList *, Znth(rows,P_zero_negative,0)) * simplex_deduction_ptrs_without(PS_zero_negative,PV_zero_negative,&(p->next)) * simplex_deduction_ints(IS_zero_negative,IV_zero_negative) * simplex_deduction_workspace(C_zero_negative,A_zero_negative,M_zero_negative,N_zero_negative,rows,0) * simplex_check_old(S_zero_negative,0,N_zero_negative,Old_zero_negative) * simplex_check_frame(S_zero_negative,0,N_zero_negative,Old_zero_negative) * data_at(&j, int, N_zero_negative+1) $ zero_negative */
/*@ Assert c == C_zero_normal && s == S_zero_normal && inputs == N_zero_normal && pivot_limit == L_zero_normal && 0 <= N_zero_normal && N_zero_normal <= 8 && 0 <= M_zero_normal && M_zero_normal <= 16 && -2147483648 <= L_zero_normal && L_zero_normal <= 2147483647 && Zlength(A_zero_normal) == M_zero_normal*9 && Forall(Z::le(-2147483648),A_zero_normal) && Forall(Z::ge(2147483647),A_zero_normal) && Zlength(P_zero_normal) == M_zero_normal+1 && list == Znth(0,P_zero_normal,0) &&
 NoDup(PS_zero_normal) && NoDup(IS_zero_normal) &&
 (forall (i: Z), (0 <= i && i < M_zero_normal) =>
  (Znth(i,P_zero_normal,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)),PS_zero_normal) &&
   In(simplex_deduction_next_address(Znth(i,P_zero_normal,0)),PS_zero_normal) &&
   PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0))) != 0 &&
   PV_zero_normal(simplex_deduction_next_address(Znth(i,P_zero_normal,0))) == Znth(i+1,P_zero_normal,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_zero_normal && 0 <= h && h <= N_zero_normal) =>
  (In(PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)))+h*sizeof(int),IS_zero_normal) &&
   IV_zero_normal(PV_zero_normal(simplex_deduction_coef_address(Znth(i,P_zero_normal,0)))+h*sizeof(int)) == Znth(i*9+h,A_zero_normal,0))) && Znth(M_zero_normal,P_zero_normal,0) == 0 && Forall(Z::le(-2147483647),A_zero_normal) && M_zero_normal == 0 && 0 <= L_zero_normal &&
 1 <= rows && rows <= M_zero_normal && p == Znth(rows-1,P_zero_normal,0) && data_at(&(p->next), struct InequList *, Znth(rows,P_zero_normal,0)) * simplex_deduction_ptrs_without(PS_zero_normal,PV_zero_normal,&(p->next)) * simplex_deduction_ints(IS_zero_normal,IV_zero_normal) * simplex_deduction_workspace(C_zero_normal,A_zero_normal,M_zero_normal,N_zero_normal,rows,0) * simplex_check_old(S_zero_normal,0,N_zero_normal,Old_zero_normal) * simplex_check_frame(S_zero_normal,0,N_zero_normal,Old_zero_normal) * data_at(&j, int, N_zero_normal+1) $ zero_normal */
/*@ Assert c == C_matrix_negative && s == S_matrix_negative && inputs == N_matrix_negative && pivot_limit == L_matrix_negative && 0 <= N_matrix_negative && N_matrix_negative <= 8 && 0 <= M_matrix_negative && M_matrix_negative <= 16 && -2147483648 <= L_matrix_negative && L_matrix_negative <= 2147483647 && Zlength(A_matrix_negative) == M_matrix_negative*9 && Forall(Z::le(-2147483648),A_matrix_negative) && Forall(Z::ge(2147483647),A_matrix_negative) && Zlength(P_matrix_negative) == M_matrix_negative+1 && list == Znth(0,P_matrix_negative,0) &&
 NoDup(PS_matrix_negative) && NoDup(IS_matrix_negative) &&
 (forall (i: Z), (0 <= i && i < M_matrix_negative) =>
  (Znth(i,P_matrix_negative,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)),PS_matrix_negative) &&
   In(simplex_deduction_next_address(Znth(i,P_matrix_negative,0)),PS_matrix_negative) &&
   PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0))) != 0 &&
   PV_matrix_negative(simplex_deduction_next_address(Znth(i,P_matrix_negative,0))) == Znth(i+1,P_matrix_negative,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_matrix_negative && 0 <= h && h <= N_matrix_negative) =>
  (In(PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)))+h*sizeof(int),IS_matrix_negative) &&
   IV_matrix_negative(PV_matrix_negative(simplex_deduction_coef_address(Znth(i,P_matrix_negative,0)))+h*sizeof(int)) == Znth(i*9+h,A_matrix_negative,0))) && Znth(M_matrix_negative,P_matrix_negative,0) == 0 && Forall(Z::le(-2147483647),A_matrix_negative) && 1 <= M_matrix_negative && L_matrix_negative < 0 &&
 1 <= rows && rows <= M_matrix_negative && p == Znth(rows-1,P_matrix_negative,0) && data_at(&(p->next), struct InequList *, Znth(rows,P_matrix_negative,0)) * simplex_deduction_ptrs_without(PS_matrix_negative,PV_matrix_negative,&(p->next)) * simplex_deduction_ints(IS_matrix_negative,IV_matrix_negative) * simplex_deduction_workspace(C_matrix_negative,A_matrix_negative,M_matrix_negative,N_matrix_negative,rows,0) * simplex_check_old(S_matrix_negative,M_matrix_negative,N_matrix_negative,Old_matrix_negative) * simplex_check_frame(S_matrix_negative,M_matrix_negative,N_matrix_negative,Old_matrix_negative) * simplex_check_input_frame(C_matrix_negative,M_matrix_negative,N_matrix_negative,CO_matrix_negative) * data_at(&j, int, N_matrix_negative+1) $ matrix_negative */
/*@ Assert c == C_matrix_normal && s == S_matrix_normal && inputs == N_matrix_normal && pivot_limit == L_matrix_normal && 0 <= N_matrix_normal && N_matrix_normal <= 8 && 0 <= M_matrix_normal && M_matrix_normal <= 16 && -2147483648 <= L_matrix_normal && L_matrix_normal <= 2147483647 && Zlength(A_matrix_normal) == M_matrix_normal*9 && Forall(Z::le(-2147483648),A_matrix_normal) && Forall(Z::ge(2147483647),A_matrix_normal) && Zlength(P_matrix_normal) == M_matrix_normal+1 && list == Znth(0,P_matrix_normal,0) &&
 NoDup(PS_matrix_normal) && NoDup(IS_matrix_normal) &&
 (forall (i: Z), (0 <= i && i < M_matrix_normal) =>
  (Znth(i,P_matrix_normal,0) != 0 &&
   In(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)),PS_matrix_normal) &&
   In(simplex_deduction_next_address(Znth(i,P_matrix_normal,0)),PS_matrix_normal) &&
   PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0))) != 0 &&
   PV_matrix_normal(simplex_deduction_next_address(Znth(i,P_matrix_normal,0))) == Znth(i+1,P_matrix_normal,0))) &&
 (forall (i: Z) (h: Z), (0 <= i && i < M_matrix_normal && 0 <= h && h <= N_matrix_normal) =>
  (In(PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)))+h*sizeof(int),IS_matrix_normal) &&
   IV_matrix_normal(PV_matrix_normal(simplex_deduction_coef_address(Znth(i,P_matrix_normal,0)))+h*sizeof(int)) == Znth(i*9+h,A_matrix_normal,0))) && Znth(M_matrix_normal,P_matrix_normal,0) == 0 && Forall(Z::le(-2147483647),A_matrix_normal) && 1 <= M_matrix_normal && 0 <= L_matrix_normal &&
 1 <= rows && rows <= M_matrix_normal && p == Znth(rows-1,P_matrix_normal,0) && data_at(&(p->next), struct InequList *, Znth(rows,P_matrix_normal,0)) * simplex_deduction_ptrs_without(PS_matrix_normal,PV_matrix_normal,&(p->next)) * simplex_deduction_ints(IS_matrix_normal,IV_matrix_normal) * simplex_deduction_workspace(C_matrix_normal,A_matrix_normal,M_matrix_normal,N_matrix_normal,rows,0) * simplex_check_old(S_matrix_normal,M_matrix_normal,N_matrix_normal,Old_matrix_normal) * simplex_check_frame(S_matrix_normal,M_matrix_normal,N_matrix_normal,Old_matrix_normal) * simplex_check_input_frame(C_matrix_normal,M_matrix_normal,N_matrix_normal,CO_matrix_normal) * data_at(&j, int, N_matrix_normal+1) $ matrix_normal */
 p = p->next;
 }
 return sx_check(s, rows, inputs, c, pivot_limit)
    /*@ where (check_invalid_dimensions) M = rows, N = 9, S = s, C = c, L = pivot_limit $ invalid_inputs
        where (check_invalid_dimensions) M = rows, N = 9, S = s, C = c, L = pivot_limit $ nullcoef_reject
        where (check_invalid_dimensions) M = rows, N = 9, S = s, C = c, L = pivot_limit $ bounded_prefix_reject
        where (check_rejected_coefficient) A = A_complete_min, M = M_complete_min, N = N_complete_min, S = S_complete_min, C = c, L = L_complete_min $ complete_min
        where (zero_negative_budget) N = N_zero_negative, S = S_zero_negative, C = c, L = L_zero_negative, Old = Old_zero_negative $ zero_negative
        where (zero_normal_budget) N = N_zero_normal, S = S_zero_normal, C = c, L = L_zero_normal, Old = Old_zero_normal $ zero_normal
        where (matrix_negative_budget) A = A_matrix_negative, M = M_matrix_negative, N = N_matrix_negative, S = S_matrix_negative, C = c, L = L_matrix_negative, Old = Old_matrix_negative, CO = CO_matrix_negative $ matrix_negative
        where (matrix_normal_budget) A = A_matrix_normal, M = M_matrix_normal, N = N_matrix_normal, S = S_matrix_normal, C = c, L = L_matrix_normal, Old = Old_matrix_normal, CO = CO_matrix_normal $ matrix_normal */;
}
