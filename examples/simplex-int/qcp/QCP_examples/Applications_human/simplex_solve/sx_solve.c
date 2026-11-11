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



/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_find_violation_preserve.simplex_find_violation_preserve_lib */
/*@ Extern Coq
 (simplex_find_violation_spec : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_scan_prefix : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_scan_read_memory : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Assertion)
 (simplex_scan_read_except : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Assertion)
 (In : {A} -> A -> list A -> Prop)
*/

int sx_find_violation(struct SxState *s, int *row, int *direction)
/*@ framed_search
 With (BAS : list Z) (HL : list Z) (HU : list Z) (VN : list Z) (VD : list Z) (LN : list Z) (LD : list Z) (UN : list Z) (UD : list Z) M V S P Q
 Require s == S && row == P && direction == Q &&
 0 <= M && M <= 16 && 0 <= V && V <= 24 &&
 (forall j, (0 <= j && j < M) => (0 <= Znth(j, BAS, 0) && Znth(j, BAS, 0) < V)) &&
 (forall j, (In(j, BAS) && (Znth(j, HL, 0) != 0 || Znth(j, HU, 0) != 0)) =>
    (-2147483648 <= Znth(j, VN, 0) && Znth(j, VN, 0) <= 2147483647 && 1 <= Znth(j, VD, 0) && Znth(j, VD, 0) <= 2147483647)) &&
 (forall j, (In(j, BAS) && Znth(j, HL, 0) != 0) =>
    (-2147483648 <= Znth(j, LN, 0) && Znth(j, LN, 0) <= 2147483647 && 1 <= Znth(j, LD, 0) && Znth(j, LD, 0) <= 2147483647)) &&
 (forall j, (In(j, BAS) && Znth(j, HU, 0) != 0) =>
    (-2147483648 <= Znth(j, UN, 0) && Znth(j, UN, 0) <= 2147483647 && 1 <= Znth(j, UD, 0) && Znth(j, UD, 0) <= 2147483647)) &&
 store(&(s->rows), M) * store(&(s->vars), V) *
 IntArray::full(s->basic, M, BAS) * simplex_scan_read_memory(s, BAS, HL, HU, VN, VD, LN, LD, UN, UD) *
 undef_data_at(row) * undef_data_at(direction)
 Ensure exists R D, simplex_find_violation_spec(BAS, HL, HU, VN, VD, LN, LD, UN, UD, V, M, __return, R, D) &&
 store(&(((struct SxState *)S)->rows), M) * store(&(((struct SxState *)S)->vars), V) *
 IntArray::full(((struct SxState *)S)->basic, M, BAS) * simplex_scan_read_memory(((struct SxState *)S), BAS, HL, HU, VN, VD, LN, LD, UN, UD) *
 data_at(((int *)P), int, R) * data_at(((int *)Q), int, D)
*/
;

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_find_entering_preserve.simplex_find_entering_preserve_lib */
/*@ Extern Coq
 (Forall : {A} -> (A -> Prop) -> list A -> Prop)
 (Z::le : Z -> Z -> Prop)
 (Z::ge : Z -> Z -> Prop)
 (Zrange : Z -> Z -> list Z)
 (simplex_find_entering_spec : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_enter_skipped : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
 (simplex_scan_read_memory : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Assertion)
 (simplex_scan_read_except : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Assertion)
 (simplex_enter_num_memory : Z -> Z -> Z -> list Z -> Assertion)
 (simplex_enter_num_except : Z -> Z -> Z -> list Z -> Z -> Assertion)
*/
int sx_find_entering(struct SxState *s, int row, int direction, int *entering)
/*@ framed_search
    With V S R D O (IB CN HL HU VN VD LN LD UN UD : list Z)
    Require s == S && row == R && direction == D && entering == O && 0 <= V && V <= 24 && (V == 0 || (0 <= row && row < 16)) &&
      -2147483648 <= row && row <= 2147483647 &&
      -2147483648 <= direction && direction <= 2147483647 &&
      Zlength(CN) == V && Zlength(VN) == V && Zlength(VD) == V &&
      Forall(Z::le(-2147483647), CN) && Forall(Z::ge(2147483647), CN) &&
      Forall(Z::le(-2147483647), VN) && Forall(Z::ge(2147483647), VN) &&
      Forall(Z::le(1), VD) && Forall(Z::ge(2147483647), VD) &&
      (forall (i: Z), (0 <= i && i < V && Znth(i, HL, 0) != 0) =>
        (-2147483647 <= Znth(i, LN, 0) && Znth(i, LN, 0) <= 2147483647 &&
         1 <= Znth(i, LD, 0) && Znth(i, LD, 0) <= 2147483647)) &&
      (forall (i: Z), (0 <= i && i < V && Znth(i, HU, 0) != 0) =>
        (-2147483647 <= Znth(i, UN, 0) && Znth(i, UN, 0) <= 2147483647 &&
         1 <= Znth(i, UD, 0) && Znth(i, UD, 0) <= 2147483647)) &&
      store(&(s->vars), V) * IntArray::full(s->is_basic, V, IB) *
      simplex_scan_read_memory(s, Zrange(0, V), HL, HU, VN, VD, LN, LD, UN, UD) *
      simplex_enter_num_memory(s, row, V, CN) * undef_data_at(entering)
    Ensure exists e, simplex_find_entering_spec(IB, CN, HL, HU, VN, VD, LN, LD, UN, UD,
        D, V, __return, e) && store(&(((struct SxState *)S)->vars), V) *
      IntArray::full(((struct SxState *)S)->is_basic, V, IB) *
      simplex_scan_read_memory(((struct SxState *)S), Zrange(0, V), HL, HU, VN, VD, LN, LD, UN, UD) *
      simplex_enter_num_memory(((struct SxState *)S), R, V, CN) * data_at(((int *)O), int, e)
*/
;

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_pivot.simplex_pivot_lib */
/*@ Extern Coq
 (Zgcd : Z -> Z -> Z) (Zabs : Z -> Z)
 (In : {A} -> A -> list A -> Prop) (NoDup : {A} -> list A -> Prop)
 (simplex_pivot_slots : Z -> Z -> list Z)
 (simplex_pivot_closed : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_pivot_equiv : list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_pivot_result : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
 (simplex_pivot_row_progress : list Z -> list Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
 (simplex_pivot_rows_progress : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
 (simplex_pivot_columns_progress : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
 (simplex_pivot_memory : Z -> Z -> Z -> list Z -> list Z -> Assertion)
 (simplex_pivot_except : Z -> Z -> Z -> list Z -> list Z -> Z -> Z -> Assertion)
 (simplex_pivot_ready_zero : list Z -> list Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
 (simplex_pivot_factor : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_pivot_other_ready : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
 (simplex_pivot_flags_except : Z -> Z -> list Z -> Z -> Z -> Assertion)
 (simplex_pivot_basis : list Z -> Z -> Z -> Z -> list Z)
 (simplex_pivot_marks : list Z -> Z -> Z -> Z -> list Z)
*/
int sx_pivot(struct SxState *s, int row, int entering)

/*@ tableau_pivot
 With (S M V R E : Z) (N D B IB : list Z)
 Require s == S && row == R && entering == E && 1 <= M && M <= 16 && 1 <= V && V <= 24 &&
 0 <= R && R < M && 0 <= E && E < V && Zlength(N) == 400 && Zlength(D) == 400 &&
 NoDup(B) && (forall (k: Z), (0 <= k && k < M) => (0 <= Znth(k,B,0) && Znth(k,B,0) < V && Znth(Znth(k,B,0),IB,0) == 1)) &&
 (forall (k: Z), (0 <= k && k < V) => (0 <= Znth(k,IB,0) && Znth(k,IB,0) <= 1 && (Znth(k,IB,0) != 0 => In(k,B)))) && Znth(E,IB,0) == 0 &&
 (forall (i: Z) (k: Z), (0 <= i && i < M && 0 <= k && k < M) => Znth(16+i*24+Znth(k,B,0),N,0) == 0) &&
 (forall (k: Z), In(k, simplex_pivot_slots(M, V)) => (-2147483647 <= Znth(k, N, 0) && Znth(k, N, 0) <= 2147483647 && 1 <= Znth(k, D, 1) && Znth(k, D, 1) <= 2147483647 && Zgcd(Zabs(Znth(k, N, 0)), Znth(k, D, 1)) == 1)) &&
 store(&(s->rows),M) * store(&(s->vars),V) * IntArray::full(s->basic,M,B) * IntArray::full(s->is_basic,V,IB) * simplex_pivot_memory(s,M,V,N,D)
 Ensure exists ON OD, (__return == 0 || __return == 1) &&
 simplex_pivot_result(N,D,M,V,R,E,Znth(R,B,0),__return,ON,OD) &&
 (__return == 1 => (simplex_pivot_closed(N,D,ON,OD,M,V,R,E,Znth(R,B,0)) && simplex_pivot_equiv(N,D,ON,OD,B,M,V,R,E))) &&
 (forall (k: Z), In(k,simplex_pivot_slots(M,V)) => (-2147483647 <= Znth(k,ON,0) && Znth(k,ON,0) <= 2147483647 && 1 <= Znth(k,OD,1) && Znth(k,OD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,ON,0)),Znth(k,OD,1)) == 1)) &&
 store(&(((struct SxState *)S)->rows),M) * store(&(((struct SxState *)S)->vars),V) *
 IntArray::full(((struct SxState *)S)->basic,M,simplex_pivot_basis(B,R,E,__return)) *
 IntArray::full(((struct SxState *)S)->is_basic,V,simplex_pivot_marks(IB,Znth(R,B,0),E,__return)) * simplex_pivot_memory(S,M,V,ON,OD)
*/
;

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_recompute.simplex_recompute_lib */
/*@ Extern Coq
 (Forall : {A} -> (A -> Prop) -> list A -> Prop)
 (Z::le : Z -> Z -> Prop) (Z::ge : Z -> Z -> Prop)
 (simplex_recompute_prefix : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
 (simplex_recompute_sum : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_recompute_values : Z -> Z -> list Z -> list Z -> Assertion)
 (simplex_recompute_rhs : Z -> Z -> list Z -> list Z -> Assertion)
 (simplex_recompute_matrix : Z -> Z -> Z -> list Z -> list Z -> Assertion)
 (simplex_recompute_values_except : Z -> Z -> list Z -> list Z -> Z -> Assertion)
 (simplex_recompute_rhs_except : Z -> Z -> list Z -> list Z -> Z -> Assertion)
 (simplex_recompute_matrix_except : Z -> Z -> Z -> list Z -> list Z -> Z -> Z -> Assertion)
*/
int sx_recompute(struct SxState *s)
/*@ recompute
 With (S R V : Z) (IB AN AD RN RD B VN VD : list Z)
 Require s == S && 0 <= R && R <= 16 && 0 <= V && V <= 24 &&
 Zlength(AN) == R*24 && Zlength(AD) == R*24 && Zlength(RN) == R && Zlength(RD) == R &&
 (forall (k: Z), (0 <= k && k < R) => (0 <= Znth(k, B, 0) && Znth(k, B, 0) < V)) &&
Forall(Z::le(-2147483647), AN) && Forall(Z::ge(2147483647), AN) && Forall(Z::le(1), AD) && Forall(Z::ge(2147483647), AD) &&
Forall(Z::le(-2147483647), RN) && Forall(Z::ge(2147483647), RN) && Forall(Z::le(1), RD) && Forall(Z::ge(2147483647), RD) &&
Forall(Z::le(-2147483647), VN) && Forall(Z::ge(2147483647), VN) && Forall(Z::le(1), VD) && Forall(Z::ge(2147483647), VD) &&

 Zlength(VN) == V && Zlength(VD) == V &&
 store(&(s->rows), R) * store(&(s->vars), V) * IntArray::full(s->basic, R, B) * IntArray::full(s->is_basic, V, IB) * simplex_recompute_rhs(s, R, RN, RD) * simplex_recompute_matrix(s, R, V, AN, AD) * simplex_recompute_values(s, V, VN, VD)
 Ensure exists ON OD,
 Forall(Z::le(-2147483647), ON) && Forall(Z::ge(2147483647), ON) && Forall(Z::le(1), OD) && Forall(Z::ge(2147483647), OD) &&
 Zlength(ON) == V && Zlength(OD) == V && simplex_recompute_prefix(IB, AN, AD, RN, RD, B, VN, VD, R, V, __return, ON, OD) &&
 store(&(((struct SxState *)S)->rows), R) * store(&(((struct SxState *)S)->vars), V) *
 IntArray::full(((struct SxState *)S)->basic, R, B) * IntArray::full(((struct SxState *)S)->is_basic, V, IB) *
 simplex_recompute_rhs(S, R, RN, RD) * simplex_recompute_matrix(S, R, V, AN, AD) * simplex_recompute_values(S, V, ON, OD)
*/
;

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_solve.simplex_solve_lib */
/*@ Extern Coq (simplex_solve_snapshot :: *) */
/*@ Extern Coq
 (simplex_solve_pack : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> simplex_solve_snapshot)
 (simplex_solve_normal : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> simplex_solve_snapshot -> Prop)
 (simplex_solve_origin : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> simplex_solve_snapshot -> Prop)
 (simplex_solve_result : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
 (simplex_solve_progress : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
 (simplex_solve_witness : list Z -> Z -> Z -> list Z -> list Z -> Prop)
 (simplex_solve_unsat : list Z -> Z -> Z -> Prop)
 (simplex_solve_variables : Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Assertion)
 (simplex_solve_row : list Z -> Z -> Z -> list Z)
 (simplex_solve_matrix : Z -> list Z -> Z -> Z -> list Z)
 (simplex_solve_rhs : list Z -> Z -> list Z)
 (simplex_solve_read_rest : Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Assertion)
 (simplex_solve_enter_rest : Z -> Z -> Z -> list Z -> list Z -> Z -> Assertion)
 (simplex_solve_bound_memory : Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Assertion)
 (simplex_solve_bound_except : Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Assertion)
 (simplex_solve_repair : list Z -> list Z -> list Z -> Z -> Z -> list Z)
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
{
    int count = 0, row, direction, entering, leaving;
    if (pivot_limit < 0) return SX_UNKNOWN;
    /* Each completed iteration restores normality at the same source A;
       the exact prefix has completed precisely count pivots. */
    /*@ Inv Assert exists CN CD CB CIB CVN CVD,
 s == S_normal_state && s == s@pre && pivot_limit == L_normal_state && pivot_limit == pivot_limit@pre &&
 0 <= M_normal_state && M_normal_state <= 16 && 0 <= I_normal_state && I_normal_state <= 8 &&
 V_normal_state == M_normal_state+I_normal_state && 0 <= V_normal_state && V_normal_state <= 24 &&
 0 <= L_normal_state && L_normal_state <= 2147483647 && 0 <= count && count <= L_normal_state &&
 simplex_solve_normal(A_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,I_normal_state,simplex_solve_pack(CN,CD,CB,CIB,CVN,CVD)) &&
 simplex_solve_origin(A_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,I_normal_state,simplex_solve_pack(CN,CD,CB,CIB,CVN,CVD)) &&
 simplex_solve_progress(HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,V_normal_state,L_normal_state,count,N_normal_state,D_normal_state,B_normal_state,IB_normal_state,VN_normal_state,VD_normal_state,CN,CD,CB,CIB,CVN,CVD) &&  store(&(s->rows),M_normal_state) * store(&(s->vars),V_normal_state) * store(&(s->inputs),I_normal_state) *  IntArray::full(s->basic,M_normal_state,CB) * IntArray::full(s->is_basic,V_normal_state,CIB) * simplex_pivot_memory(s,M_normal_state,V_normal_state,CN,CD) * simplex_solve_variables(s,V_normal_state,HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state) * undef_data_at(&row) * undef_data_at(&direction) * undef_data_at(&entering) * undef_data_at(&leaving) */
    for (;;) {
/*@ Assert exists CN CD CB CIB CVN CVD,
 s == S_normal_state && s == s@pre && pivot_limit == L_normal_state && pivot_limit == pivot_limit@pre &&
 0 <= M_normal_state && M_normal_state <= 16 && 0 <= I_normal_state && I_normal_state <= 8 &&
 V_normal_state == M_normal_state+I_normal_state && 0 <= V_normal_state && V_normal_state <= 24 &&
 0 <= L_normal_state && L_normal_state <= 2147483647 && 0 <= count && count <= L_normal_state &&
 simplex_solve_normal(A_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,I_normal_state,simplex_solve_pack(CN,CD,CB,CIB,CVN,CVD)) &&
 simplex_solve_origin(A_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,I_normal_state,simplex_solve_pack(CN,CD,CB,CIB,CVN,CVD)) &&
 simplex_solve_progress(HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,V_normal_state,L_normal_state,count,N_normal_state,D_normal_state,B_normal_state,IB_normal_state,VN_normal_state,VD_normal_state,CN,CD,CB,CIB,CVN,CVD) &&  store(&(s->rows),M_normal_state) * store(&(s->vars),V_normal_state) * store(&(s->inputs),I_normal_state) *  IntArray::full(s->basic,M_normal_state,CB) * IntArray::full(s->is_basic,V_normal_state,CIB) * simplex_pivot_memory(s,M_normal_state,V_normal_state,CN,CD) * simplex_scan_read_memory(s,CB,HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state) * simplex_solve_read_rest(s,V_normal_state,CB,HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state) * undef_data_at(&row) * undef_data_at(&direction) * undef_data_at(&entering) * undef_data_at(&leaving) */
        if (!sx_find_violation(s, &row, &direction)
          /*@ where (framed_search) $ normal_state */)
            return SX_UNKNOWN;
/*@ Assert exists CN CD CB CIB CVN CVD,
 s == S_normal_state && s == s@pre && pivot_limit == L_normal_state && pivot_limit == pivot_limit@pre &&
 0 <= M_normal_state && M_normal_state <= 16 && 0 <= I_normal_state && I_normal_state <= 8 &&
 V_normal_state == M_normal_state+I_normal_state && 0 <= V_normal_state && V_normal_state <= 24 &&
 0 <= L_normal_state && L_normal_state <= 2147483647 && 0 <= count && count <= L_normal_state &&
 simplex_solve_normal(A_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,I_normal_state,simplex_solve_pack(CN,CD,CB,CIB,CVN,CVD)) &&
 simplex_solve_origin(A_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,I_normal_state,simplex_solve_pack(CN,CD,CB,CIB,CVN,CVD)) &&
 simplex_solve_progress(HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,V_normal_state,L_normal_state,count,N_normal_state,D_normal_state,B_normal_state,IB_normal_state,VN_normal_state,VD_normal_state,CN,CD,CB,CIB,CVN,CVD) && simplex_find_violation_spec(CB,HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,V_normal_state,M_normal_state,1,row,direction) &&  store(&(s->rows),M_normal_state) * store(&(s->vars),V_normal_state) * store(&(s->inputs),I_normal_state) *  IntArray::full(s->basic,M_normal_state,CB) * IntArray::full(s->is_basic,V_normal_state,CIB) * simplex_pivot_memory(s,M_normal_state,V_normal_state,CN,CD) * simplex_solve_variables(s,V_normal_state,HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state) * undef_data_at(&entering) * undef_data_at(&leaving) */
        if (row < 0) return SX_FEASIBLE;
/*@ Assert exists CN CD CB CIB CVN CVD,
 s == S_normal_state && s == s@pre && pivot_limit == L_normal_state && pivot_limit == pivot_limit@pre &&
 0 <= M_normal_state && M_normal_state <= 16 && 0 <= I_normal_state && I_normal_state <= 8 &&
 V_normal_state == M_normal_state+I_normal_state && 0 <= V_normal_state && V_normal_state <= 24 &&
 0 <= L_normal_state && L_normal_state <= 2147483647 && 0 <= count && count <= L_normal_state &&
 simplex_solve_normal(A_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,I_normal_state,simplex_solve_pack(CN,CD,CB,CIB,CVN,CVD)) &&
 simplex_solve_origin(A_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,I_normal_state,simplex_solve_pack(CN,CD,CB,CIB,CVN,CVD)) &&
 simplex_solve_progress(HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,V_normal_state,L_normal_state,count,N_normal_state,D_normal_state,B_normal_state,IB_normal_state,VN_normal_state,VD_normal_state,CN,CD,CB,CIB,CVN,CVD) && simplex_find_violation_spec(CB,HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,V_normal_state,M_normal_state,1,row,direction) && 0 <= row && row < M_normal_state && (direction == 1 || direction == -1) &&  store(&(s->rows),M_normal_state) * store(&(s->vars),V_normal_state) * store(&(s->inputs),I_normal_state) *  IntArray::full(s->basic,M_normal_state,CB) * IntArray::full(s->is_basic,V_normal_state,CIB) * simplex_scan_read_memory(s,Zrange(0,V_normal_state),HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state) * simplex_solve_read_rest(s,V_normal_state,Zrange(0,V_normal_state),HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state) * simplex_enter_num_memory(s,row,V_normal_state,simplex_solve_row(CN,row,V_normal_state)) * simplex_solve_enter_rest(s,M_normal_state,V_normal_state,CN,CD,row) * undef_data_at(&entering) * undef_data_at(&leaving) */
        if (!sx_find_entering(s, row, direction, &entering)
          /*@ where (framed_search) $ normal_state */)
            return SX_UNKNOWN;
/*@ Assert exists CN CD CB CIB CVN CVD,
 s == S_normal_state && s == s@pre && pivot_limit == L_normal_state && pivot_limit == pivot_limit@pre &&
 0 <= M_normal_state && M_normal_state <= 16 && 0 <= I_normal_state && I_normal_state <= 8 &&
 V_normal_state == M_normal_state+I_normal_state && 0 <= V_normal_state && V_normal_state <= 24 &&
 0 <= L_normal_state && L_normal_state <= 2147483647 && 0 <= count && count <= L_normal_state &&
 simplex_solve_normal(A_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,I_normal_state,simplex_solve_pack(CN,CD,CB,CIB,CVN,CVD)) &&
 simplex_solve_origin(A_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,I_normal_state,simplex_solve_pack(CN,CD,CB,CIB,CVN,CVD)) &&
 simplex_solve_progress(HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,V_normal_state,L_normal_state,count,N_normal_state,D_normal_state,B_normal_state,IB_normal_state,VN_normal_state,VD_normal_state,CN,CD,CB,CIB,CVN,CVD) && simplex_find_violation_spec(CB,HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,V_normal_state,M_normal_state,1,row,direction) && simplex_find_entering_spec(CIB,simplex_solve_row(CN,row,V_normal_state),HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,direction,V_normal_state,1,entering) && 0 <= row && row < M_normal_state && (direction == 1 || direction == -1) &&  store(&(s->rows),M_normal_state) * store(&(s->vars),V_normal_state) * store(&(s->inputs),I_normal_state) *  IntArray::full(s->basic,M_normal_state,CB) * IntArray::full(s->is_basic,V_normal_state,CIB) * simplex_pivot_memory(s,M_normal_state,V_normal_state,CN,CD) * simplex_solve_variables(s,V_normal_state,HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state) * undef_data_at(&leaving) */
        if (entering < 0) return SX_UNSAT;
        if (count >= pivot_limit) return SX_UNKNOWN;
        leaving = s->basic[row];
        if (!sx_pivot(s, row, entering)
          /*@ where (tableau_pivot) $ normal_state */)
            return SX_UNKNOWN;
/*@ Assert exists CN CD CB CIB CVN CVD PN PD,
 s == S_normal_state && s == s@pre && pivot_limit == L_normal_state && pivot_limit == pivot_limit@pre &&
 0 <= M_normal_state && M_normal_state <= 16 && 0 <= I_normal_state && I_normal_state <= 8 &&
 V_normal_state == M_normal_state+I_normal_state && 0 <= V_normal_state && V_normal_state <= 24 &&
 0 <= L_normal_state && L_normal_state <= 2147483647 && 0 <= count && count <= L_normal_state &&
 simplex_solve_normal(A_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,I_normal_state,simplex_solve_pack(CN,CD,CB,CIB,CVN,CVD)) &&
 simplex_solve_origin(A_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,I_normal_state,simplex_solve_pack(CN,CD,CB,CIB,CVN,CVD)) &&
 simplex_solve_progress(HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,V_normal_state,L_normal_state,count,N_normal_state,D_normal_state,B_normal_state,IB_normal_state,VN_normal_state,VD_normal_state,CN,CD,CB,CIB,CVN,CVD) && 0 <= row && row < M_normal_state && 0 <= entering && entering < V_normal_state && 0 <= leaving && leaving < V_normal_state && leaving == Znth(row,CB,0) && count < L_normal_state && simplex_find_violation_spec(CB,HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,V_normal_state,M_normal_state,1,row,direction) && simplex_find_entering_spec(CIB,simplex_solve_row(CN,row,V_normal_state),HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,direction,V_normal_state,1,entering) && simplex_pivot_result(CN,CD,M_normal_state,V_normal_state,row,entering,leaving,1,PN,PD) && simplex_pivot_closed(CN,CD,PN,PD,M_normal_state,V_normal_state,row,entering,leaving) && simplex_pivot_equiv(CN,CD,PN,PD,CB,M_normal_state,V_normal_state,row,entering) &&
 Zlength(PN) == 400 && Zlength(PD) == 400 &&
 (forall (k: Z), In(k,simplex_pivot_slots(M_normal_state,V_normal_state)) =>
  (-2147483647 <= Znth(k,PN,0) && Znth(k,PN,0) <= 2147483647 && 1 <= Znth(k,PD,1) && Znth(k,PD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,PN,0)),Znth(k,PD,1)) == 1)) &&  store(&(s->rows),M_normal_state) * store(&(s->vars),V_normal_state) * store(&(s->inputs),I_normal_state) * IntArray::full(s->basic,M_normal_state,simplex_pivot_basis(CB,row,entering,1)) * IntArray::full(s->is_basic,V_normal_state,simplex_pivot_marks(CIB,leaving,entering,1)) * simplex_pivot_memory(s,M_normal_state,V_normal_state,PN,PD) * simplex_recompute_values_except(s,V_normal_state,CVN,CVD,leaving) * simplex_solve_bound_except(s,V_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,leaving) *  store(&(s->value[leaving].num),Znth(leaving,CVN,0)) * store(&(s->value[leaving].den),Znth(leaving,CVD,0)) *
 store(&(s->lower[leaving].num),Znth(leaving,LN_normal_state,0)) * store(&(s->lower[leaving].den),Znth(leaving,LD_normal_state,0)) *
 store(&(s->upper[leaving].num),Znth(leaving,UN_normal_state,0)) * store(&(s->upper[leaving].den),Znth(leaving,UD_normal_state,0)) *
 store(&(s->has_lower[leaving]),Znth(leaving,HL_normal_state,0)) * store(&(s->has_upper[leaving]),Znth(leaving,HU_normal_state,0)) */
        if (direction > 0) s->value[leaving] = s->lower[leaving];
        else s->value[leaving] = s->upper[leaving];
/*@ Assert exists CN CD CB CIB CVN CVD PN PD,
 s == S_normal_state && s == s@pre && pivot_limit == L_normal_state && pivot_limit == pivot_limit@pre &&
 0 <= M_normal_state && M_normal_state <= 16 && 0 <= I_normal_state && I_normal_state <= 8 &&
 V_normal_state == M_normal_state+I_normal_state && 0 <= V_normal_state && V_normal_state <= 24 &&
 0 <= L_normal_state && L_normal_state <= 2147483647 && 0 <= count && count <= L_normal_state &&
 simplex_solve_normal(A_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,I_normal_state,simplex_solve_pack(CN,CD,CB,CIB,CVN,CVD)) &&
 simplex_solve_origin(A_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,I_normal_state,simplex_solve_pack(CN,CD,CB,CIB,CVN,CVD)) &&
 simplex_solve_progress(HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,M_normal_state,V_normal_state,L_normal_state,count,N_normal_state,D_normal_state,B_normal_state,IB_normal_state,VN_normal_state,VD_normal_state,CN,CD,CB,CIB,CVN,CVD) && 0 <= row && row < M_normal_state && 0 <= entering && entering < V_normal_state && 0 <= leaving && leaving < V_normal_state && leaving == Znth(row,CB,0) && count < L_normal_state && simplex_find_violation_spec(CB,HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,V_normal_state,M_normal_state,1,row,direction) && simplex_find_entering_spec(CIB,simplex_solve_row(CN,row,V_normal_state),HL_normal_state,HU_normal_state,CVN,CVD,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state,direction,V_normal_state,1,entering) && simplex_pivot_result(CN,CD,M_normal_state,V_normal_state,row,entering,leaving,1,PN,PD) && simplex_pivot_closed(CN,CD,PN,PD,M_normal_state,V_normal_state,row,entering,leaving) && simplex_pivot_equiv(CN,CD,PN,PD,CB,M_normal_state,V_normal_state,row,entering) &&
 Zlength(PN) == 400 && Zlength(PD) == 400 &&
 (forall (k: Z), In(k,simplex_pivot_slots(M_normal_state,V_normal_state)) =>
  (-2147483647 <= Znth(k,PN,0) && Znth(k,PN,0) <= 2147483647 && 1 <= Znth(k,PD,1) && Znth(k,PD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,PN,0)),Znth(k,PD,1)) == 1)) &&  store(&(s->rows),M_normal_state) * store(&(s->vars),V_normal_state) * store(&(s->inputs),I_normal_state) * IntArray::full(s->basic,M_normal_state,simplex_pivot_basis(CB,row,entering,1)) * IntArray::full(s->is_basic,V_normal_state,simplex_pivot_marks(CIB,leaving,entering,1)) * simplex_recompute_rhs(s,M_normal_state,simplex_solve_rhs(PN,M_normal_state),simplex_solve_rhs(PD,M_normal_state)) * simplex_recompute_matrix(s,M_normal_state,V_normal_state,simplex_solve_matrix(0,PN,M_normal_state,V_normal_state),simplex_solve_matrix(1,PD,M_normal_state,V_normal_state)) * simplex_recompute_values(s,V_normal_state,simplex_solve_repair(LN_normal_state,UN_normal_state,CVN,leaving,direction),simplex_solve_repair(LD_normal_state,UD_normal_state,CVD,leaving,direction)) * simplex_solve_bound_memory(s,V_normal_state,HL_normal_state,HU_normal_state,LN_normal_state,LD_normal_state,UN_normal_state,UD_normal_state) */
        if (!sx_recompute(s) /*@ where (recompute) $ normal_state */) return SX_UNKNOWN;
        count++;
    }
}