/* Proved caller-workspace interface. Run simplex_deduction-20261105153243.
 * final-check passed; original local-workspace legacy function is not covered.
 * Extracted verbatim declaration/spec; this review file is not a new proof. */
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
