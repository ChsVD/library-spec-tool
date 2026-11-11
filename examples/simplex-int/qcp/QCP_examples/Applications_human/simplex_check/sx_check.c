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
int sx_initialize(struct SxState *s, int rows, int inputs, const int c[SX_ROWS][SX_INPUT_VARS + 1])
/*@ invalid_dimensions
 With (A : list Z) M N S C
 Require s == S && c == C && rows == M && inputs == N && (rows < 0 || rows > 16 || inputs < 0 || inputs > 8) && emp
 Ensure simplex_init_return(__return, 0) && emp
*/
/*@ rejected_coefficient
 With (A : list Z) M N S C
 Require s == S && rows == M && inputs == N && c == C && 0 <= M && M <= 16 && 0 <= N && N <= 8 && Zlength(A) == M*9 && Forall(Z::le(-2147483648), A) && Forall(Z::ge(2147483647), A) &&
 (exists (x: Z) (y: Z), 0 <= x && x < M && 0 <= y && y <= N && Znth(x*9+y, A, 0) == -2147483648) && simplex_init_input(C, A, M, N)
 Ensure simplex_init_return(__return, 0) && simplex_init_input(C, A, M, N)
*/
/*@ initialized_matrix_non_alias
 With (A : list Z) M N S C
 Require s == S && c == C && rows == M && inputs == N && 1 <= M && M <= 16 && 0 <= N && N <= 8 && Zlength(A) == M*9 && Forall(Z::le(-2147483647), A) && Forall(Z::ge(2147483647), A) &&
 simplex_init_input(C, A, M, N) * undef_data_at(&(((struct SxState *)S)->rows)) * undef_data_at(&(((struct SxState *)S)->inputs)) * undef_data_at(&(((struct SxState *)S)->vars)) * simplex_init_vars(S, N, 0, 0, M+N, A, 0) * simplex_init_rows(S, A, N, 0, M, M+N)
 Ensure simplex_init_return(__return, 1) && simplex_init_input(C, A, M, N) * store(&(((struct SxState *)S)->rows), M) * store(&(((struct SxState *)S)->inputs), N) * store(&(((struct SxState *)S)->vars), M+N) * simplex_init_vars(S, N, M+N, M, M+N, simplex_init_rhs(A, M), 1) * simplex_init_rows(S, A, N, M, M, M+N)
*/
/*@ zero_rows
 With N S C
 Require c == C && s == S && rows == 0 && inputs == N && 0 <= N && N <= 8 && undef_data_at(&(((struct SxState *)S)->rows)) * undef_data_at(&(((struct SxState *)S)->inputs)) * undef_data_at(&(((struct SxState *)S)->vars)) * simplex_init_vars(S, N, 0, 0, 0+N, nil, 0) * simplex_init_rows(S, nil, N, 0, 0, 0+N)
 Ensure simplex_init_return(__return, 1) && store(&(((struct SxState *)S)->rows), 0) * store(&(((struct SxState *)S)->inputs), N) * store(&(((struct SxState *)S)->vars), 0+N) * simplex_init_vars(S, N, 0+N, 0, 0+N, simplex_init_rhs(nil, 0), 1) * simplex_init_rows(S, nil, N, 0, 0, 0+N)
*/
;
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
int sx_initialize(struct SxState *s, int rows, int inputs,
                  const int c[SX_ROWS][SX_INPUT_VARS + 1])
/*@ check_init_invalid <= invalid_dimensions
 With M N S C
 Require s == S && c == C && rows == M && inputs == N &&
 simplex_check_invalid_dimensions(M,N) && emp
 Ensure simplex_init_return(__return,0) && emp
*/;

int sx_initialize(struct SxState *s, int rows, int inputs,
                  const int c[SX_ROWS][SX_INPUT_VARS + 1])
/*@ check_init_zero <= zero_rows
 With N S C (Old : simplex_check_memory_snapshot)
 Require s == S && c == C && rows == 0 && inputs == N && 0 <= N && N <= 8 &&
 simplex_check_old(S,0,N,Old) * simplex_check_frame(S,0,N,Old)
 Ensure simplex_init_return(__return,1) && store(&(((struct SxState *)S)->rows),0) * store(&(((struct SxState *)S)->inputs),N) * store(&(((struct SxState *)S)->vars),0+N) * simplex_init_vars(S,N,0+N,0,0+N,simplex_init_rhs(nil,0),1) * simplex_init_rows(S,nil,N,0,0,0+N) * simplex_check_frame(S,0,N,Old)
*/;
/*@ Extern Coq (simplex_check_invalid_dimensions : Z -> Z -> Prop) */
int sx_initialize(struct SxState *s, int rows, int inputs,
                  const int c[SX_ROWS][SX_INPUT_VARS + 1])
/*@ check_init_matrix <= initialized_matrix_non_alias
 With (A : list Z) M N S C (Old CO : simplex_check_memory_snapshot)
 Require s == S && c == C && rows == M && inputs == N &&
 1 <= M && M <= 16 && 0 <= N && N <= 8 && Zlength(A) == M*9 &&
 Forall(Z::le(-2147483647),A) && Forall(Z::ge(2147483647),A) &&
 simplex_check_old(S,M,N,Old) * simplex_check_frame(S,M,N,Old) *
 simplex_init_input(C,A,M,N) * simplex_check_input_frame(C,M,N,CO)
 Ensure simplex_init_return(__return,1) && store(&(((struct SxState *)S)->rows),M) * store(&(((struct SxState *)S)->inputs),N) * store(&(((struct SxState *)S)->vars),M+N) * simplex_init_vars(S,N,M+N,M,M+N,simplex_init_rhs(A,M),1) * simplex_init_rows(S,A,N,M,M,M+N) *
 simplex_check_frame(S,M,N,Old) * simplex_init_input(C,A,M,N) * simplex_check_input_frame(C,M,N,CO)
*/;
int sx_solve(struct SxState *s, int pivot_limit)
/*@ check_solve_initialized <= normal_state
 With S L M N (A : list Z)
 Require s == S && pivot_limit == L && 0 <= L && L <= 2147483647 &&
 0 <= M && M <= 16 && 0 <= N && N <= 8 &&
 (forall (i: Z) (j: Z), (0 <= i && i < M && 0 <= j && j <= N) =>
 (-2147483647 <= Znth(i*9+j,A,0) && Znth(i*9+j,A,0) <= 2147483647)) &&
 store(&(((struct SxState *)S)->rows),M) * store(&(((struct SxState *)S)->inputs),N) * store(&(((struct SxState *)S)->vars),M+N) * simplex_init_vars(S,N,M+N,M,M+N,simplex_init_rhs(A,M),1) * simplex_init_rows(S,A,N,M,M,M+N)
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
 simplex_solve_variables(S,M+N,simplex_init_zeroes(M+N),simplex_init_flags(N,M+N),OVN,OVD,simplex_init_zeroes(M+N),simplex_init_ones(M+N),simplex_init_zeroes(M+N),simplex_init_ones(M+N))
*/;

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
{
    if (!sx_initialize(s, rows, inputs, c)
      /*@ where (check_init_invalid) M = M_check_invalid_dimensions, N = N_check_invalid_dimensions, S = S_check_invalid_dimensions, C = C_check_invalid_dimensions $ check_invalid_dimensions
          where (rejected_coefficient) A = A_check_rejected_coefficient, M = M_check_rejected_coefficient, N = N_check_rejected_coefficient, S = S_check_rejected_coefficient, C = C_check_rejected_coefficient $ check_rejected_coefficient
          where (check_init_zero) N = N_zero_negative_budget, S = S_zero_negative_budget, C = C_zero_negative_budget, Old = Old_zero_negative_budget $ zero_negative_budget
          where (check_init_zero) N = N_zero_normal_budget, S = S_zero_normal_budget, C = C_zero_normal_budget, Old = Old_zero_normal_budget $ zero_normal_budget
          where (check_init_matrix) A = A_matrix_negative_budget, M = M_matrix_negative_budget, N = N_matrix_negative_budget, S = S_matrix_negative_budget, C = C_matrix_negative_budget, Old = Old_matrix_negative_budget, CO = CO_matrix_negative_budget $ matrix_negative_budget
          where (check_init_matrix) A = A_matrix_normal_budget, M = M_matrix_normal_budget, N = N_matrix_normal_budget, S = S_matrix_normal_budget, C = C_matrix_normal_budget, Old = Old_matrix_normal_budget, CO = CO_matrix_normal_budget $ matrix_normal_budget */) return SX_UNKNOWN;
    return sx_solve(s, pivot_limit)
      /*@ where (negative_budget) L = L_check_invalid_dimensions $ check_invalid_dimensions
          where (negative_budget) L = L_check_rejected_coefficient $ check_rejected_coefficient
          where (negative_budget) L = L_zero_negative_budget $ zero_negative_budget
          where (check_solve_initialized) S = S_zero_normal_budget, L = L_zero_normal_budget, M = 0, N = N_zero_normal_budget, A = nil{Z} $ zero_normal_budget
          where (negative_budget) L = L_matrix_negative_budget $ matrix_negative_budget
          where (check_solve_initialized) S = S_matrix_normal_budget, L = L_matrix_normal_budget, M = M_matrix_normal_budget, N = N_matrix_normal_budget, A = A_matrix_normal_budget $ matrix_normal_budget */;
}
