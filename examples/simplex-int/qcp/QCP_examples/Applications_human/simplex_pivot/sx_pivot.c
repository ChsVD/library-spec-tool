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



/*@ Extern Coq (Zgcd : Z -> Z -> Z) (Zabs : Z -> Z) */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_rat_div.simplex_rat_div_lib */
/*@ Extern Coq
      (simplex_rat_div_flag : Z -> Z -> Z -> Z -> Z)
      (simplex_rat_div_result : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/

static int rat_div(const struct SxRat *x, const struct SxRat *y,
                   struct SxRat *out)
  /*@ r_eq_x
      With A B C E
      Require out == x &&
              -2147483647 <= A && A <= 2147483647 &&
              -2147483647 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= E && E <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), E)
      Ensure __return == simplex_rat_div_flag(A, B, C, E) &&
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_div_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && A * E * Q == P * (B * C) &&
                (A != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && store(&(x->num), A) * store(&(x->den), B)))
  */
  /*@ out_undef
      With A B C E
      Require -2147483647 <= A && A <= 2147483647 &&
              -2147483647 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= E && E <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), E) *
              undef_data_at(&(out->num)) * undef_data_at(&(out->den))
      Ensure __return == simplex_rat_div_flag(A, B, C, E) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_div_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && A * E * Q == P * (B * C) &&
                (A != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && undef_data_at(&(out->num)) * undef_data_at(&(out->den))))
  */
  /*@ out_known
      With A B C E oldn oldd
      Require -2147483647 <= A && A <= 2147483647 &&
              -2147483647 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= E && E <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), E) *
              store(&(out->num), oldn) * store(&(out->den), oldd)
      Ensure __return == simplex_rat_div_flag(A, B, C, E) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_div_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && A * E * Q == P * (B * C) &&
                (A != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && store(&(out->num), oldn) * store(&(out->den), oldd)))
  */
;

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_rat_mul.simplex_rat_mul_lib */
/*@ Extern Coq
      (simplex_rat_mul_flag : Z -> Z -> Z -> Z -> Z)
      (simplex_rat_mul_result : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/

static int rat_mul(const struct SxRat *x, const struct SxRat *y,
                   struct SxRat *out)
  /*@ out_undef
      With A B C D
      Require -2147483648 <= A && A <= 2147483647 &&
              -2147483648 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= D && D <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), D) *
              undef_data_at(&(out->num)) * undef_data_at(&(out->den))
      Ensure __return == simplex_rat_mul_flag(A, B, C, D) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), D) *
             ((__return == 1 && exists P Q,
                simplex_rat_mul_result(A, B, C, D, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && A * C * Q == P * (B * D) &&
                (A * C != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && undef_data_at(&(out->num)) * undef_data_at(&(out->den))))
  */
  /*@ out_known
      With A B C D oldn oldd
      Require -2147483648 <= A && A <= 2147483647 &&
              -2147483648 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= D && D <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), D) *
              store(&(out->num), oldn) * store(&(out->den), oldd)
      Ensure __return == simplex_rat_mul_flag(A, B, C, D) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), D) *
             ((__return == 1 && exists P Q,
                simplex_rat_mul_result(A, B, C, D, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && A * C * Q == P * (B * D) &&
                (A * C != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && store(&(out->num), oldn) * store(&(out->den), oldd)))
  */
;

/* 接口片段；SxRat、Zabs、Zgcd的共享声明见simplex_function_contracts.c。 */
/* ========================================================================
 * 08. rat_add — 受检有理数加法，输出可原地覆盖x
 * 来源：qcp/QCP_examples/Applications_human/simplex_rat_add/rat_add.c
 * 通用库：qcp/Rocq/examples/Applications_human/simplex_rat_add/simplex_rat_add_lib.v
 * 验证运行：simplex_rat_add-20261102024202，final-check done。
 * 分子[-INT_MAX,INT_MAX]，分母[1,INT_MAX]；输入无需预先约分，允许零。
 * r_eq_x：out=x且y分离；out_undef/out_known：三个对象分离。
 * flag依序检查A*E、C*B、A*E+C*B和B*E，发生在约分前。
 * 成功：N=A*E+C*B、D=B*E、g=gcd(abs(N),D)，输出(N quot g,D quot g)。
 * 输出唯一、互素、正分母且范围合法；N=0时为(0,1)。
 * 失败保持原地/已知输出旧值，未知输出归还undef权限；y始终保持。
 * checked_add(out_undef)、checked_mul(out_undef)和rat_reduce已在三个分支实际使用。
 * 不覆盖out=y、x=y、三者同址、部分重叠、混合字段初始化模式或INT_MIN分子。
 * 未做rat_add上层调用专项测试；不声称未知字节/初始化标签保持或整链终止性。
 * ======================================================================== */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_rat_add.simplex_rat_add_lib */
/*@ Extern Coq
      (simplex_rat_add_flag : Z -> Z -> Z -> Z -> Z)
      (simplex_rat_add_result : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/

static int rat_add(const struct SxRat *x, const struct SxRat *y,
                   struct SxRat *out)
  /*@ r_eq_x
      With A B C E
      Require out == x &&
              -2147483647 <= A && A <= 2147483647 &&
              -2147483647 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= E && E <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), E)
      Ensure __return == simplex_rat_add_flag(A, B, C, E) &&
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_add_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && (A * E + C * B) * Q == P * (B * E) &&
                (A * E + C * B != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && store(&(x->num), A) * store(&(x->den), B)))
  */
  /*@ out_undef
      With A B C E
      Require -2147483647 <= A && A <= 2147483647 &&
              -2147483647 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= E && E <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), E) *
              undef_data_at(&(out->num)) * undef_data_at(&(out->den))
      Ensure __return == simplex_rat_add_flag(A, B, C, E) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_add_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && (A * E + C * B) * Q == P * (B * E) &&
                (A * E + C * B != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && undef_data_at(&(out->num)) * undef_data_at(&(out->den))))
  */
  /*@ out_known
      With A B C E oldn oldd
      Require -2147483647 <= A && A <= 2147483647 &&
              -2147483647 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= E && E <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), E) *
              store(&(out->num), oldn) * store(&(out->den), oldd)
      Ensure __return == simplex_rat_add_flag(A, B, C, E) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_add_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && (A * E + C * B) * Q == P * (B * E) &&
                (A * E + C * B != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && store(&(out->num), oldn) * store(&(out->den), oldd)))
  */
;

/* 接口片段：共享SxRat声明见simplex_function_contracts.c。 */
/* ========================================================================
 * 09. rat_zero — 将有理数对象置为规范零(0,1)
 * 来源：qcp/QCP_examples/Applications_human/simplex_rat_zero/rat_zero.c
 * 验证运行：simplex_rat_zero-20261102032152，final-check done。
 * out_undef：两个字段可写但值未知；out_known：两个字段已初始化、旧值任意。
 * 不读取旧值，不要求原分母为正或原有理数合法；输出精确为num=0、den=1。
 * 无新增通用定义/引理，无实质FME引理复用；属于无需此类引理的底层赋值函数。
 * 两分支共6条QCP auto义务，0条manual；auto按实验约定由QCP负责。
 * 未单独验证外部caller调用、混合初始化字段接口或非法指针入口。
 * ======================================================================== */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_rat_zero.simplex_rat_zero_lib */

static void rat_zero(struct SxRat *r)
  /*@ out_undef
      Require undef_data_at(&(r->num)) * undef_data_at(&(r->den))
      Ensure store(&(r->num), 0) * store(&(r->den), 1)
  */
  /*@ out_known
      With oldn oldd
      Require store(&(r->num), oldn) * store(&(r->den), oldd)
      Ensure store(&(r->num), 0) * store(&(r->den), 1)
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
{
    int i, j, leaving = s->basic[row];
    struct SxRat pivot, factor, term, one;

/*@ Assert s == S_tableau_pivot && row == R_tableau_pivot && entering == E_tableau_pivot && 1 <= M_tableau_pivot && M_tableau_pivot <= 16 && 1 <= V_tableau_pivot && V_tableau_pivot <= 24 &&
 0 <= R_tableau_pivot && R_tableau_pivot < M_tableau_pivot && 0 <= E_tableau_pivot && E_tableau_pivot < V_tableau_pivot && Zlength(N_tableau_pivot) == 400 && Zlength(D_tableau_pivot) == 400 &&
 NoDup(B_tableau_pivot) && (forall (k: Z), (0 <= k && k < M_tableau_pivot) => (0 <= Znth(k,B_tableau_pivot,0) && Znth(k,B_tableau_pivot,0) < V_tableau_pivot && Znth(Znth(k,B_tableau_pivot,0),IB_tableau_pivot,0) == 1)) &&
 (forall (k: Z), (0 <= k && k < V_tableau_pivot) => (0 <= Znth(k,IB_tableau_pivot,0) && Znth(k,IB_tableau_pivot,0) <= 1 && (Znth(k,IB_tableau_pivot,0) != 0 => In(k,B_tableau_pivot)))) && Znth(E_tableau_pivot,IB_tableau_pivot,0) == 0 &&
 (forall (i: Z) (k: Z), (0 <= i && i < M_tableau_pivot && 0 <= k && k < M_tableau_pivot) => Znth(16+i*24+Znth(k,B_tableau_pivot,0),N_tableau_pivot,0) == 0) &&
 (forall (k: Z), In(k, simplex_pivot_slots(M_tableau_pivot, V_tableau_pivot)) => (-2147483647 <= Znth(k, N_tableau_pivot, 0) && Znth(k, N_tableau_pivot, 0) <= 2147483647 && 1 <= Znth(k, D_tableau_pivot, 1) && Znth(k, D_tableau_pivot, 1) <= 2147483647 && Zgcd(Zabs(Znth(k, N_tableau_pivot, 0)), Znth(k, D_tableau_pivot, 1)) == 1)) && s == S_tableau_pivot && row == R_tableau_pivot && entering == E_tableau_pivot && leaving == Znth(R_tableau_pivot,B_tableau_pivot,0) &&
 0 <= row && row < M_tableau_pivot && 0 <= entering && entering < V_tableau_pivot &&
 -2147483647 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) <= 2147483647 &&
 1 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) <= 2147483647 &&
 store(&(s->rows),M_tableau_pivot) * store(&(s->vars),V_tableau_pivot) * IntArray::full(s->basic,M_tableau_pivot,B_tableau_pivot) * IntArray::full(s->is_basic,V_tableau_pivot,IB_tableau_pivot) *
 simplex_pivot_except(s,M_tableau_pivot,V_tableau_pivot,N_tableau_pivot,D_tableau_pivot,16+row*24+entering,16+row*24+entering) *
 store(&(s->a[row][entering].num),Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0)) * store(&(s->a[row][entering].den),Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1)) *
 undef_data_at(&i) * undef_data_at(&j) * undef_data_at(&(pivot.num)) * undef_data_at(&(pivot.den)) * undef_data_at(&(factor.num)) * undef_data_at(&(factor.den)) * undef_data_at(&(term.num)) * undef_data_at(&(term.den)) * undef_data_at(&(one.num)) * undef_data_at(&(one.den)) */
    pivot = s->a[row][entering];
    one.num = 1; one.den = 1;

/*@ Assert exists CN CD, s == S_tableau_pivot && row == R_tableau_pivot && entering == E_tableau_pivot && 1 <= M_tableau_pivot && M_tableau_pivot <= 16 && 1 <= V_tableau_pivot && V_tableau_pivot <= 24 &&
 0 <= R_tableau_pivot && R_tableau_pivot < M_tableau_pivot && 0 <= E_tableau_pivot && E_tableau_pivot < V_tableau_pivot && Zlength(N_tableau_pivot) == 400 && Zlength(D_tableau_pivot) == 400 &&
 NoDup(B_tableau_pivot) && (forall (k: Z), (0 <= k && k < M_tableau_pivot) => (0 <= Znth(k,B_tableau_pivot,0) && Znth(k,B_tableau_pivot,0) < V_tableau_pivot && Znth(Znth(k,B_tableau_pivot,0),IB_tableau_pivot,0) == 1)) &&
 (forall (k: Z), (0 <= k && k < V_tableau_pivot) => (0 <= Znth(k,IB_tableau_pivot,0) && Znth(k,IB_tableau_pivot,0) <= 1 && (Znth(k,IB_tableau_pivot,0) != 0 => In(k,B_tableau_pivot)))) && Znth(E_tableau_pivot,IB_tableau_pivot,0) == 0 &&
 (forall (i: Z) (k: Z), (0 <= i && i < M_tableau_pivot && 0 <= k && k < M_tableau_pivot) => Znth(16+i*24+Znth(k,B_tableau_pivot,0),N_tableau_pivot,0) == 0) &&
 (forall (k: Z), In(k, simplex_pivot_slots(M_tableau_pivot, V_tableau_pivot)) => (-2147483647 <= Znth(k, N_tableau_pivot, 0) && Znth(k, N_tableau_pivot, 0) <= 2147483647 && 1 <= Znth(k, D_tableau_pivot, 1) && Znth(k, D_tableau_pivot, 1) <= 2147483647 && Zgcd(Zabs(Znth(k, N_tableau_pivot, 0)), Znth(k, D_tableau_pivot, 1)) == 1)) && leaving == Znth(R_tableau_pivot,B_tableau_pivot,0) && 0 <= leaving && leaving < V_tableau_pivot && leaving != E_tableau_pivot &&
 Zlength(CN) == 400 && Zlength(CD) == 400 && (forall (k: Z), In(k,simplex_pivot_slots(M_tableau_pivot,V_tableau_pivot)) => (-2147483647 <= Znth(k,CN,0) && Znth(k,CN,0) <= 2147483647 && 1 <= Znth(k,CD,1) && Znth(k,CD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,CN,0)),Znth(k,CD,1)) == 1)) && CN == N_tableau_pivot && CD == D_tableau_pivot && 1 == 1 && -2147483647 <= Znth(R_tableau_pivot,CN,0) && Znth(R_tableau_pivot,CN,0) <= 2147483647 && 1 <= Znth(R_tableau_pivot,CD,1) && Znth(R_tableau_pivot,CD,1) <= 2147483647 && -2147483647 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) <= 2147483647 &&
store(&(s->rows),M_tableau_pivot) * store(&(s->vars),V_tableau_pivot) * IntArray::full(s->basic,M_tableau_pivot,B_tableau_pivot) * IntArray::full(s->is_basic,V_tableau_pivot,IB_tableau_pivot) * simplex_pivot_except(s,M_tableau_pivot,V_tableau_pivot,CN,CD,R_tableau_pivot,R_tableau_pivot) * store(&(s->rhs[row].num),Znth(R_tableau_pivot,CN,0)) * store(&(s->rhs[row].den),Znth(R_tableau_pivot,CD,1)) * store(&(pivot.num),Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0)) * store(&(pivot.den),Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1)) * store(&(one.num),1) * store(&(one.den),1) * undef_data_at(&(term.num)) * undef_data_at(&(term.den)) * undef_data_at(&(factor.num)) * undef_data_at(&(factor.den)) * undef_data_at(&i) * undef_data_at(&j) */
    if (!rat_div(&s->rhs[row], &pivot, &s->rhs[row]) /*@ where (r_eq_x) */) return 0;
    s->rhs[row].num = -s->rhs[row].num;

/*@ Inv Assert exists CN CD, s == S_tableau_pivot && row == R_tableau_pivot && entering == E_tableau_pivot && 1 <= M_tableau_pivot && M_tableau_pivot <= 16 && 1 <= V_tableau_pivot && V_tableau_pivot <= 24 &&
 0 <= R_tableau_pivot && R_tableau_pivot < M_tableau_pivot && 0 <= E_tableau_pivot && E_tableau_pivot < V_tableau_pivot && Zlength(N_tableau_pivot) == 400 && Zlength(D_tableau_pivot) == 400 &&
 NoDup(B_tableau_pivot) && (forall (k: Z), (0 <= k && k < M_tableau_pivot) => (0 <= Znth(k,B_tableau_pivot,0) && Znth(k,B_tableau_pivot,0) < V_tableau_pivot && Znth(Znth(k,B_tableau_pivot,0),IB_tableau_pivot,0) == 1)) &&
 (forall (k: Z), (0 <= k && k < V_tableau_pivot) => (0 <= Znth(k,IB_tableau_pivot,0) && Znth(k,IB_tableau_pivot,0) <= 1 && (Znth(k,IB_tableau_pivot,0) != 0 => In(k,B_tableau_pivot)))) && Znth(E_tableau_pivot,IB_tableau_pivot,0) == 0 &&
 (forall (i: Z) (k: Z), (0 <= i && i < M_tableau_pivot && 0 <= k && k < M_tableau_pivot) => Znth(16+i*24+Znth(k,B_tableau_pivot,0),N_tableau_pivot,0) == 0) &&
 (forall (k: Z), In(k, simplex_pivot_slots(M_tableau_pivot, V_tableau_pivot)) => (-2147483647 <= Znth(k, N_tableau_pivot, 0) && Znth(k, N_tableau_pivot, 0) <= 2147483647 && 1 <= Znth(k, D_tableau_pivot, 1) && Znth(k, D_tableau_pivot, 1) <= 2147483647 && Zgcd(Zabs(Znth(k, N_tableau_pivot, 0)), Znth(k, D_tableau_pivot, 1)) == 1)) && leaving == Znth(R_tableau_pivot,B_tableau_pivot,0) && 0 <= leaving && leaving < V_tableau_pivot && leaving != E_tableau_pivot &&
 Zlength(CN) == 400 && Zlength(CD) == 400 && (forall (k: Z), In(k,simplex_pivot_slots(M_tableau_pivot,V_tableau_pivot)) => (-2147483647 <= Znth(k,CN,0) && Znth(k,CN,0) <= 2147483647 && 1 <= Znth(k,CD,1) && Znth(k,CD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,CN,0)),Znth(k,CD,1)) == 1)) && simplex_pivot_row_progress(N_tableau_pivot,D_tableau_pivot,R_tableau_pivot,E_tableau_pivot,j,CN,CD) && 0 <= j && j <= V_tableau_pivot && -2147483647 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) <= 2147483647 &&
store(&(s->rows),M_tableau_pivot) * store(&(s->vars),V_tableau_pivot) * IntArray::full(s->basic,M_tableau_pivot,B_tableau_pivot) * IntArray::full(s->is_basic,V_tableau_pivot,IB_tableau_pivot) * simplex_pivot_memory(s,M_tableau_pivot,V_tableau_pivot,CN,CD) * store(&(pivot.num),Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0)) * store(&(pivot.den),Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1)) * store(&(one.num),1) * store(&(one.den),1) * undef_data_at(&(term.num)) * undef_data_at(&(term.den)) * undef_data_at(&(factor.num)) * undef_data_at(&(factor.den)) * undef_data_at(&i) */
    for (j = 0; j < s->vars; j++) {

/*@ Assert exists CN CD, s == S_tableau_pivot && row == R_tableau_pivot && entering == E_tableau_pivot && 1 <= M_tableau_pivot && M_tableau_pivot <= 16 && 1 <= V_tableau_pivot && V_tableau_pivot <= 24 &&
 0 <= R_tableau_pivot && R_tableau_pivot < M_tableau_pivot && 0 <= E_tableau_pivot && E_tableau_pivot < V_tableau_pivot && Zlength(N_tableau_pivot) == 400 && Zlength(D_tableau_pivot) == 400 &&
 NoDup(B_tableau_pivot) && (forall (k: Z), (0 <= k && k < M_tableau_pivot) => (0 <= Znth(k,B_tableau_pivot,0) && Znth(k,B_tableau_pivot,0) < V_tableau_pivot && Znth(Znth(k,B_tableau_pivot,0),IB_tableau_pivot,0) == 1)) &&
 (forall (k: Z), (0 <= k && k < V_tableau_pivot) => (0 <= Znth(k,IB_tableau_pivot,0) && Znth(k,IB_tableau_pivot,0) <= 1 && (Znth(k,IB_tableau_pivot,0) != 0 => In(k,B_tableau_pivot)))) && Znth(E_tableau_pivot,IB_tableau_pivot,0) == 0 &&
 (forall (i: Z) (k: Z), (0 <= i && i < M_tableau_pivot && 0 <= k && k < M_tableau_pivot) => Znth(16+i*24+Znth(k,B_tableau_pivot,0),N_tableau_pivot,0) == 0) &&
 (forall (k: Z), In(k, simplex_pivot_slots(M_tableau_pivot, V_tableau_pivot)) => (-2147483647 <= Znth(k, N_tableau_pivot, 0) && Znth(k, N_tableau_pivot, 0) <= 2147483647 && 1 <= Znth(k, D_tableau_pivot, 1) && Znth(k, D_tableau_pivot, 1) <= 2147483647 && Zgcd(Zabs(Znth(k, N_tableau_pivot, 0)), Znth(k, D_tableau_pivot, 1)) == 1)) && leaving == Znth(R_tableau_pivot,B_tableau_pivot,0) && 0 <= leaving && leaving < V_tableau_pivot && leaving != E_tableau_pivot &&
 Zlength(CN) == 400 && Zlength(CD) == 400 && (forall (k: Z), In(k,simplex_pivot_slots(M_tableau_pivot,V_tableau_pivot)) => (-2147483647 <= Znth(k,CN,0) && Znth(k,CN,0) <= 2147483647 && 1 <= Znth(k,CD,1) && Znth(k,CD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,CN,0)),Znth(k,CD,1)) == 1)) && simplex_pivot_row_progress(N_tableau_pivot,D_tableau_pivot,R_tableau_pivot,E_tableau_pivot,j,CN,CD) && 0 <= j && j < V_tableau_pivot && -2147483647 <= Znth(16+R_tableau_pivot*24+j,CN,0) && Znth(16+R_tableau_pivot*24+j,CN,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+j,CD,1) && Znth(16+R_tableau_pivot*24+j,CD,1) <= 2147483647 && -2147483647 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) <= 2147483647 &&
store(&(s->rows),M_tableau_pivot) * store(&(s->vars),V_tableau_pivot) * IntArray::full(s->basic,M_tableau_pivot,B_tableau_pivot) * IntArray::full(s->is_basic,V_tableau_pivot,IB_tableau_pivot) * simplex_pivot_except(s,M_tableau_pivot,V_tableau_pivot,CN,CD,16+R_tableau_pivot*24+j,16+R_tableau_pivot*24+j) * store(&(s->a[row][j].num),Znth(16+R_tableau_pivot*24+j,CN,0)) * store(&(s->a[row][j].den),Znth(16+R_tableau_pivot*24+j,CD,1)) * store(&(pivot.num),Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0)) * store(&(pivot.den),Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1)) * store(&(one.num),1) * store(&(one.den),1) * undef_data_at(&(term.num)) * undef_data_at(&(term.den)) * undef_data_at(&(factor.num)) * undef_data_at(&(factor.den)) * undef_data_at(&i) */
        if (j != entering) {
            if (!rat_div(&s->a[row][j], &pivot, &s->a[row][j]) /*@ where (r_eq_x) */) return 0;
            s->a[row][j].num = -s->a[row][j].num;
        }
    }

/*@ Assert exists CN CD, s == S_tableau_pivot && row == R_tableau_pivot && entering == E_tableau_pivot && 1 <= M_tableau_pivot && M_tableau_pivot <= 16 && 1 <= V_tableau_pivot && V_tableau_pivot <= 24 &&
 0 <= R_tableau_pivot && R_tableau_pivot < M_tableau_pivot && 0 <= E_tableau_pivot && E_tableau_pivot < V_tableau_pivot && Zlength(N_tableau_pivot) == 400 && Zlength(D_tableau_pivot) == 400 &&
 NoDup(B_tableau_pivot) && (forall (k: Z), (0 <= k && k < M_tableau_pivot) => (0 <= Znth(k,B_tableau_pivot,0) && Znth(k,B_tableau_pivot,0) < V_tableau_pivot && Znth(Znth(k,B_tableau_pivot,0),IB_tableau_pivot,0) == 1)) &&
 (forall (k: Z), (0 <= k && k < V_tableau_pivot) => (0 <= Znth(k,IB_tableau_pivot,0) && Znth(k,IB_tableau_pivot,0) <= 1 && (Znth(k,IB_tableau_pivot,0) != 0 => In(k,B_tableau_pivot)))) && Znth(E_tableau_pivot,IB_tableau_pivot,0) == 0 &&
 (forall (i: Z) (k: Z), (0 <= i && i < M_tableau_pivot && 0 <= k && k < M_tableau_pivot) => Znth(16+i*24+Znth(k,B_tableau_pivot,0),N_tableau_pivot,0) == 0) &&
 (forall (k: Z), In(k, simplex_pivot_slots(M_tableau_pivot, V_tableau_pivot)) => (-2147483647 <= Znth(k, N_tableau_pivot, 0) && Znth(k, N_tableau_pivot, 0) <= 2147483647 && 1 <= Znth(k, D_tableau_pivot, 1) && Znth(k, D_tableau_pivot, 1) <= 2147483647 && Zgcd(Zabs(Znth(k, N_tableau_pivot, 0)), Znth(k, D_tableau_pivot, 1)) == 1)) && leaving == Znth(R_tableau_pivot,B_tableau_pivot,0) && 0 <= leaving && leaving < V_tableau_pivot && leaving != E_tableau_pivot &&
 Zlength(CN) == 400 && Zlength(CD) == 400 && (forall (k: Z), In(k,simplex_pivot_slots(M_tableau_pivot,V_tableau_pivot)) => (-2147483647 <= Znth(k,CN,0) && Znth(k,CN,0) <= 2147483647 && 1 <= Znth(k,CD,1) && Znth(k,CD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,CN,0)),Znth(k,CD,1)) == 1)) && simplex_pivot_row_progress(N_tableau_pivot,D_tableau_pivot,R_tableau_pivot,E_tableau_pivot,V_tableau_pivot,CN,CD) && j == V_tableau_pivot && -2147483647 <= Znth(16+R_tableau_pivot*24+leaving,CN,0) && Znth(16+R_tableau_pivot*24+leaving,CN,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+leaving,CD,1) && Znth(16+R_tableau_pivot*24+leaving,CD,1) <= 2147483647 && -2147483647 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) <= 2147483647 &&
store(&(s->rows),M_tableau_pivot) * store(&(s->vars),V_tableau_pivot) * IntArray::full(s->basic,M_tableau_pivot,B_tableau_pivot) * IntArray::full(s->is_basic,V_tableau_pivot,IB_tableau_pivot) * simplex_pivot_except(s,M_tableau_pivot,V_tableau_pivot,CN,CD,16+R_tableau_pivot*24+leaving,16+R_tableau_pivot*24+leaving) * store(&(s->a[row][leaving].num),Znth(16+R_tableau_pivot*24+leaving,CN,0)) * store(&(s->a[row][leaving].den),Znth(16+R_tableau_pivot*24+leaving,CD,1)) * store(&(pivot.num),Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0)) * store(&(pivot.den),Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1)) * store(&(one.num),1) * store(&(one.den),1) * undef_data_at(&(term.num)) * undef_data_at(&(term.den)) * undef_data_at(&(factor.num)) * undef_data_at(&(factor.den)) * undef_data_at(&i) */
    if (!rat_div(&one, &pivot, &s->a[row][leaving]) /*@ where (out_known) */) return 0;

/*@ Assert exists CN CD, s == S_tableau_pivot && row == R_tableau_pivot && entering == E_tableau_pivot && 1 <= M_tableau_pivot && M_tableau_pivot <= 16 && 1 <= V_tableau_pivot && V_tableau_pivot <= 24 &&
 0 <= R_tableau_pivot && R_tableau_pivot < M_tableau_pivot && 0 <= E_tableau_pivot && E_tableau_pivot < V_tableau_pivot && Zlength(N_tableau_pivot) == 400 && Zlength(D_tableau_pivot) == 400 &&
 NoDup(B_tableau_pivot) && (forall (k: Z), (0 <= k && k < M_tableau_pivot) => (0 <= Znth(k,B_tableau_pivot,0) && Znth(k,B_tableau_pivot,0) < V_tableau_pivot && Znth(Znth(k,B_tableau_pivot,0),IB_tableau_pivot,0) == 1)) &&
 (forall (k: Z), (0 <= k && k < V_tableau_pivot) => (0 <= Znth(k,IB_tableau_pivot,0) && Znth(k,IB_tableau_pivot,0) <= 1 && (Znth(k,IB_tableau_pivot,0) != 0 => In(k,B_tableau_pivot)))) && Znth(E_tableau_pivot,IB_tableau_pivot,0) == 0 &&
 (forall (i: Z) (k: Z), (0 <= i && i < M_tableau_pivot && 0 <= k && k < M_tableau_pivot) => Znth(16+i*24+Znth(k,B_tableau_pivot,0),N_tableau_pivot,0) == 0) &&
 (forall (k: Z), In(k, simplex_pivot_slots(M_tableau_pivot, V_tableau_pivot)) => (-2147483647 <= Znth(k, N_tableau_pivot, 0) && Znth(k, N_tableau_pivot, 0) <= 2147483647 && 1 <= Znth(k, D_tableau_pivot, 1) && Znth(k, D_tableau_pivot, 1) <= 2147483647 && Zgcd(Zabs(Znth(k, N_tableau_pivot, 0)), Znth(k, D_tableau_pivot, 1)) == 1)) && leaving == Znth(R_tableau_pivot,B_tableau_pivot,0) && 0 <= leaving && leaving < V_tableau_pivot && leaving != E_tableau_pivot &&
 Zlength(CN) == 400 && Zlength(CD) == 400 && (forall (k: Z), In(k,simplex_pivot_slots(M_tableau_pivot,V_tableau_pivot)) => (-2147483647 <= Znth(k,CN,0) && Znth(k,CN,0) <= 2147483647 && 1 <= Znth(k,CD,1) && Znth(k,CD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,CN,0)),Znth(k,CD,1)) == 1)) && simplex_pivot_ready_zero(N_tableau_pivot,D_tableau_pivot,V_tableau_pivot,R_tableau_pivot,E_tableau_pivot,leaving,CN,CD) && j == V_tableau_pivot && -2147483647 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,CN,0) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,CN,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,CD,1) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,CD,1) <= 2147483647 && -2147483647 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) <= 2147483647 &&
store(&(s->rows),M_tableau_pivot) * store(&(s->vars),V_tableau_pivot) * IntArray::full(s->basic,M_tableau_pivot,B_tableau_pivot) * IntArray::full(s->is_basic,V_tableau_pivot,IB_tableau_pivot) * simplex_pivot_except(s,M_tableau_pivot,V_tableau_pivot,CN,CD,16+R_tableau_pivot*24+E_tableau_pivot,16+R_tableau_pivot*24+E_tableau_pivot) * store(&(s->a[row][entering].num),Znth(16+R_tableau_pivot*24+E_tableau_pivot,CN,0)) * store(&(s->a[row][entering].den),Znth(16+R_tableau_pivot*24+E_tableau_pivot,CD,1)) * store(&(pivot.num),Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0)) * store(&(pivot.den),Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1)) * store(&(one.num),1) * store(&(one.den),1) * undef_data_at(&(term.num)) * undef_data_at(&(term.den)) * undef_data_at(&(factor.num)) * undef_data_at(&(factor.den)) * undef_data_at(&i) */
    rat_zero(&s->a[row][entering]) /*@ where (out_known) */;

/*@ Inv Assert exists CN CD, s == S_tableau_pivot && row == R_tableau_pivot && entering == E_tableau_pivot && 1 <= M_tableau_pivot && M_tableau_pivot <= 16 && 1 <= V_tableau_pivot && V_tableau_pivot <= 24 &&
 0 <= R_tableau_pivot && R_tableau_pivot < M_tableau_pivot && 0 <= E_tableau_pivot && E_tableau_pivot < V_tableau_pivot && Zlength(N_tableau_pivot) == 400 && Zlength(D_tableau_pivot) == 400 &&
 NoDup(B_tableau_pivot) && (forall (k: Z), (0 <= k && k < M_tableau_pivot) => (0 <= Znth(k,B_tableau_pivot,0) && Znth(k,B_tableau_pivot,0) < V_tableau_pivot && Znth(Znth(k,B_tableau_pivot,0),IB_tableau_pivot,0) == 1)) &&
 (forall (k: Z), (0 <= k && k < V_tableau_pivot) => (0 <= Znth(k,IB_tableau_pivot,0) && Znth(k,IB_tableau_pivot,0) <= 1 && (Znth(k,IB_tableau_pivot,0) != 0 => In(k,B_tableau_pivot)))) && Znth(E_tableau_pivot,IB_tableau_pivot,0) == 0 &&
 (forall (i: Z) (k: Z), (0 <= i && i < M_tableau_pivot && 0 <= k && k < M_tableau_pivot) => Znth(16+i*24+Znth(k,B_tableau_pivot,0),N_tableau_pivot,0) == 0) &&
 (forall (k: Z), In(k, simplex_pivot_slots(M_tableau_pivot, V_tableau_pivot)) => (-2147483647 <= Znth(k, N_tableau_pivot, 0) && Znth(k, N_tableau_pivot, 0) <= 2147483647 && 1 <= Znth(k, D_tableau_pivot, 1) && Znth(k, D_tableau_pivot, 1) <= 2147483647 && Zgcd(Zabs(Znth(k, N_tableau_pivot, 0)), Znth(k, D_tableau_pivot, 1)) == 1)) && leaving == Znth(R_tableau_pivot,B_tableau_pivot,0) && 0 <= leaving && leaving < V_tableau_pivot && leaving != E_tableau_pivot &&
 Zlength(CN) == 400 && Zlength(CD) == 400 && (forall (k: Z), In(k,simplex_pivot_slots(M_tableau_pivot,V_tableau_pivot)) => (-2147483647 <= Znth(k,CN,0) && Znth(k,CN,0) <= 2147483647 && 1 <= Znth(k,CD,1) && Znth(k,CD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,CN,0)),Znth(k,CD,1)) == 1)) && simplex_pivot_rows_progress(N_tableau_pivot,D_tableau_pivot,V_tableau_pivot,R_tableau_pivot,E_tableau_pivot,leaving,i,CN,CD) && 0 <= i && i <= M_tableau_pivot && -2147483647 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) <= 2147483647 &&
store(&(s->rows),M_tableau_pivot) * store(&(s->vars),V_tableau_pivot) * IntArray::full(s->basic,M_tableau_pivot,B_tableau_pivot) * IntArray::full(s->is_basic,V_tableau_pivot,IB_tableau_pivot) * simplex_pivot_memory(s,M_tableau_pivot,V_tableau_pivot,CN,CD) * store(&(pivot.num),Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0)) * store(&(pivot.den),Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1)) * store(&(one.num),1) * store(&(one.den),1) * undef_data_at(&(term.num)) * undef_data_at(&(term.den)) * undef_data_at(&(factor.num)) * undef_data_at(&(factor.den)) * undef_data_at(&j) */
    for (i = 0; i < s->rows; i++) {
        if (i != row) {

/*@ Assert exists CN CD, s == S_tableau_pivot && row == R_tableau_pivot && entering == E_tableau_pivot && 1 <= M_tableau_pivot && M_tableau_pivot <= 16 && 1 <= V_tableau_pivot && V_tableau_pivot <= 24 &&
 0 <= R_tableau_pivot && R_tableau_pivot < M_tableau_pivot && 0 <= E_tableau_pivot && E_tableau_pivot < V_tableau_pivot && Zlength(N_tableau_pivot) == 400 && Zlength(D_tableau_pivot) == 400 &&
 NoDup(B_tableau_pivot) && (forall (k: Z), (0 <= k && k < M_tableau_pivot) => (0 <= Znth(k,B_tableau_pivot,0) && Znth(k,B_tableau_pivot,0) < V_tableau_pivot && Znth(Znth(k,B_tableau_pivot,0),IB_tableau_pivot,0) == 1)) &&
 (forall (k: Z), (0 <= k && k < V_tableau_pivot) => (0 <= Znth(k,IB_tableau_pivot,0) && Znth(k,IB_tableau_pivot,0) <= 1 && (Znth(k,IB_tableau_pivot,0) != 0 => In(k,B_tableau_pivot)))) && Znth(E_tableau_pivot,IB_tableau_pivot,0) == 0 &&
 (forall (i: Z) (k: Z), (0 <= i && i < M_tableau_pivot && 0 <= k && k < M_tableau_pivot) => Znth(16+i*24+Znth(k,B_tableau_pivot,0),N_tableau_pivot,0) == 0) &&
 (forall (k: Z), In(k, simplex_pivot_slots(M_tableau_pivot, V_tableau_pivot)) => (-2147483647 <= Znth(k, N_tableau_pivot, 0) && Znth(k, N_tableau_pivot, 0) <= 2147483647 && 1 <= Znth(k, D_tableau_pivot, 1) && Znth(k, D_tableau_pivot, 1) <= 2147483647 && Zgcd(Zabs(Znth(k, N_tableau_pivot, 0)), Znth(k, D_tableau_pivot, 1)) == 1)) && leaving == Znth(R_tableau_pivot,B_tableau_pivot,0) && 0 <= leaving && leaving < V_tableau_pivot && leaving != E_tableau_pivot &&
 Zlength(CN) == 400 && Zlength(CD) == 400 && (forall (k: Z), In(k,simplex_pivot_slots(M_tableau_pivot,V_tableau_pivot)) => (-2147483647 <= Znth(k,CN,0) && Znth(k,CN,0) <= 2147483647 && 1 <= Znth(k,CD,1) && Znth(k,CD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,CN,0)),Znth(k,CD,1)) == 1)) && simplex_pivot_rows_progress(N_tableau_pivot,D_tableau_pivot,V_tableau_pivot,R_tableau_pivot,E_tableau_pivot,leaving,i,CN,CD) && 0 <= i && i < M_tableau_pivot && i != R_tableau_pivot && -2147483647 <= Znth(16+i*24+E_tableau_pivot,CN,0) && Znth(16+i*24+E_tableau_pivot,CN,0) <= 2147483647 && 1 <= Znth(16+i*24+E_tableau_pivot,CD,1) && Znth(16+i*24+E_tableau_pivot,CD,1) <= 2147483647 && -2147483647 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) <= 2147483647 &&
store(&(s->rows),M_tableau_pivot) * store(&(s->vars),V_tableau_pivot) * IntArray::full(s->basic,M_tableau_pivot,B_tableau_pivot) * IntArray::full(s->is_basic,V_tableau_pivot,IB_tableau_pivot) * simplex_pivot_except(s,M_tableau_pivot,V_tableau_pivot,CN,CD,16+i*24+E_tableau_pivot,16+i*24+E_tableau_pivot) * store(&(s->a[i][entering].num),Znth(16+i*24+E_tableau_pivot,CN,0)) * store(&(s->a[i][entering].den),Znth(16+i*24+E_tableau_pivot,CD,1)) * store(&(pivot.num),Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0)) * store(&(pivot.den),Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1)) * store(&(one.num),1) * store(&(one.den),1) * undef_data_at(&(term.num)) * undef_data_at(&(term.den)) * undef_data_at(&(factor.num)) * undef_data_at(&(factor.den)) * undef_data_at(&j) */
            factor = s->a[i][entering];

/*@ Assert exists CN CD FN FD, s == S_tableau_pivot && row == R_tableau_pivot && entering == E_tableau_pivot && 1 <= M_tableau_pivot && M_tableau_pivot <= 16 && 1 <= V_tableau_pivot && V_tableau_pivot <= 24 &&
 0 <= R_tableau_pivot && R_tableau_pivot < M_tableau_pivot && 0 <= E_tableau_pivot && E_tableau_pivot < V_tableau_pivot && Zlength(N_tableau_pivot) == 400 && Zlength(D_tableau_pivot) == 400 &&
 NoDup(B_tableau_pivot) && (forall (k: Z), (0 <= k && k < M_tableau_pivot) => (0 <= Znth(k,B_tableau_pivot,0) && Znth(k,B_tableau_pivot,0) < V_tableau_pivot && Znth(Znth(k,B_tableau_pivot,0),IB_tableau_pivot,0) == 1)) &&
 (forall (k: Z), (0 <= k && k < V_tableau_pivot) => (0 <= Znth(k,IB_tableau_pivot,0) && Znth(k,IB_tableau_pivot,0) <= 1 && (Znth(k,IB_tableau_pivot,0) != 0 => In(k,B_tableau_pivot)))) && Znth(E_tableau_pivot,IB_tableau_pivot,0) == 0 &&
 (forall (i: Z) (k: Z), (0 <= i && i < M_tableau_pivot && 0 <= k && k < M_tableau_pivot) => Znth(16+i*24+Znth(k,B_tableau_pivot,0),N_tableau_pivot,0) == 0) &&
 (forall (k: Z), In(k, simplex_pivot_slots(M_tableau_pivot, V_tableau_pivot)) => (-2147483647 <= Znth(k, N_tableau_pivot, 0) && Znth(k, N_tableau_pivot, 0) <= 2147483647 && 1 <= Znth(k, D_tableau_pivot, 1) && Znth(k, D_tableau_pivot, 1) <= 2147483647 && Zgcd(Zabs(Znth(k, N_tableau_pivot, 0)), Znth(k, D_tableau_pivot, 1)) == 1)) && leaving == Znth(R_tableau_pivot,B_tableau_pivot,0) && 0 <= leaving && leaving < V_tableau_pivot && leaving != E_tableau_pivot &&
 Zlength(CN) == 400 && Zlength(CD) == 400 && (forall (k: Z), In(k,simplex_pivot_slots(M_tableau_pivot,V_tableau_pivot)) => (-2147483647 <= Znth(k,CN,0) && Znth(k,CN,0) <= 2147483647 && 1 <= Znth(k,CD,1) && Znth(k,CD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,CN,0)),Znth(k,CD,1)) == 1)) && simplex_pivot_rows_progress(N_tableau_pivot,D_tableau_pivot,V_tableau_pivot,R_tableau_pivot,E_tableau_pivot,leaving,i,CN,CD) && 0 <= i && i < M_tableau_pivot && i != R_tableau_pivot && -2147483647 <= Znth(i,CN,0) && Znth(i,CN,0) <= 2147483647 && 1 <= Znth(i,CD,1) && Znth(i,CD,1) <= 2147483647 && -2147483647 <= Znth(R_tableau_pivot,CN,0) && Znth(R_tableau_pivot,CN,0) <= 2147483647 && 1 <= Znth(R_tableau_pivot,CD,1) && Znth(R_tableau_pivot,CD,1) <= 2147483647 && -2147483647 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) <= 2147483647 && -2147483647 <= FN && FN <= 2147483647 && 1 <= FD && FD <= 2147483647 && simplex_pivot_factor(N_tableau_pivot,D_tableau_pivot,V_tableau_pivot,R_tableau_pivot,E_tableau_pivot,leaving,i,FN,FD) &&
store(&(s->rows),M_tableau_pivot) * store(&(s->vars),V_tableau_pivot) * IntArray::full(s->basic,M_tableau_pivot,B_tableau_pivot) * IntArray::full(s->is_basic,V_tableau_pivot,IB_tableau_pivot) * simplex_pivot_except(s,M_tableau_pivot,V_tableau_pivot,CN,CD,i,R_tableau_pivot) * store(&(s->rhs[i].num),Znth(i,CN,0)) * store(&(s->rhs[i].den),Znth(i,CD,1)) * store(&(s->rhs[row].num),Znth(R_tableau_pivot,CN,0)) * store(&(s->rhs[row].den),Znth(R_tableau_pivot,CD,1)) * store(&(pivot.num),Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0)) * store(&(pivot.den),Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1)) * store(&(one.num),1) * store(&(one.den),1) * undef_data_at(&(term.num)) * undef_data_at(&(term.den)) * store(&(factor.num),FN) * store(&(factor.den),FD) * undef_data_at(&j) */
            if (factor.num != 0) {
                if (!rat_mul(&factor, &s->rhs[row], &term) /*@ where (out_undef) A=factor.num, B=factor.den, C=s->rhs[row].num, D=s->rhs[row].den $ tableau_pivot */) return 0;
                if (!rat_add(&s->rhs[i], &term, &s->rhs[i]) /*@ where (r_eq_x) */) return 0;

/*@ Inv Assert exists CN CD FN FD, s == S_tableau_pivot && row == R_tableau_pivot && entering == E_tableau_pivot && 1 <= M_tableau_pivot && M_tableau_pivot <= 16 && 1 <= V_tableau_pivot && V_tableau_pivot <= 24 &&
 0 <= R_tableau_pivot && R_tableau_pivot < M_tableau_pivot && 0 <= E_tableau_pivot && E_tableau_pivot < V_tableau_pivot && Zlength(N_tableau_pivot) == 400 && Zlength(D_tableau_pivot) == 400 &&
 NoDup(B_tableau_pivot) && (forall (k: Z), (0 <= k && k < M_tableau_pivot) => (0 <= Znth(k,B_tableau_pivot,0) && Znth(k,B_tableau_pivot,0) < V_tableau_pivot && Znth(Znth(k,B_tableau_pivot,0),IB_tableau_pivot,0) == 1)) &&
 (forall (k: Z), (0 <= k && k < V_tableau_pivot) => (0 <= Znth(k,IB_tableau_pivot,0) && Znth(k,IB_tableau_pivot,0) <= 1 && (Znth(k,IB_tableau_pivot,0) != 0 => In(k,B_tableau_pivot)))) && Znth(E_tableau_pivot,IB_tableau_pivot,0) == 0 &&
 (forall (i: Z) (k: Z), (0 <= i && i < M_tableau_pivot && 0 <= k && k < M_tableau_pivot) => Znth(16+i*24+Znth(k,B_tableau_pivot,0),N_tableau_pivot,0) == 0) &&
 (forall (k: Z), In(k, simplex_pivot_slots(M_tableau_pivot, V_tableau_pivot)) => (-2147483647 <= Znth(k, N_tableau_pivot, 0) && Znth(k, N_tableau_pivot, 0) <= 2147483647 && 1 <= Znth(k, D_tableau_pivot, 1) && Znth(k, D_tableau_pivot, 1) <= 2147483647 && Zgcd(Zabs(Znth(k, N_tableau_pivot, 0)), Znth(k, D_tableau_pivot, 1)) == 1)) && leaving == Znth(R_tableau_pivot,B_tableau_pivot,0) && 0 <= leaving && leaving < V_tableau_pivot && leaving != E_tableau_pivot &&
 Zlength(CN) == 400 && Zlength(CD) == 400 && (forall (k: Z), In(k,simplex_pivot_slots(M_tableau_pivot,V_tableau_pivot)) => (-2147483647 <= Znth(k,CN,0) && Znth(k,CN,0) <= 2147483647 && 1 <= Znth(k,CD,1) && Znth(k,CD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,CN,0)),Znth(k,CD,1)) == 1)) && simplex_pivot_columns_progress(N_tableau_pivot,D_tableau_pivot,V_tableau_pivot,R_tableau_pivot,E_tableau_pivot,leaving,i,j,FN,FD,CN,CD) && 0 <= i && i < M_tableau_pivot && i != R_tableau_pivot && 0 <= j && j <= V_tableau_pivot && FN != 0 && -2147483647 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) <= 2147483647 && -2147483647 <= FN && FN <= 2147483647 && 1 <= FD && FD <= 2147483647 && simplex_pivot_factor(N_tableau_pivot,D_tableau_pivot,V_tableau_pivot,R_tableau_pivot,E_tableau_pivot,leaving,i,FN,FD) &&
store(&(s->rows),M_tableau_pivot) * store(&(s->vars),V_tableau_pivot) * IntArray::full(s->basic,M_tableau_pivot,B_tableau_pivot) * IntArray::full(s->is_basic,V_tableau_pivot,IB_tableau_pivot) * simplex_pivot_memory(s,M_tableau_pivot,V_tableau_pivot,CN,CD) * store(&(pivot.num),Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0)) * store(&(pivot.den),Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1)) * store(&(one.num),1) * store(&(one.den),1) * undef_data_at(&(term.num)) * undef_data_at(&(term.den)) * store(&(factor.num),FN) * store(&(factor.den),FD) */
                for (j = 0; j < s->vars; j++) {

/*@ Assert exists CN CD FN FD, s == S_tableau_pivot && row == R_tableau_pivot && entering == E_tableau_pivot && 1 <= M_tableau_pivot && M_tableau_pivot <= 16 && 1 <= V_tableau_pivot && V_tableau_pivot <= 24 &&
 0 <= R_tableau_pivot && R_tableau_pivot < M_tableau_pivot && 0 <= E_tableau_pivot && E_tableau_pivot < V_tableau_pivot && Zlength(N_tableau_pivot) == 400 && Zlength(D_tableau_pivot) == 400 &&
 NoDup(B_tableau_pivot) && (forall (k: Z), (0 <= k && k < M_tableau_pivot) => (0 <= Znth(k,B_tableau_pivot,0) && Znth(k,B_tableau_pivot,0) < V_tableau_pivot && Znth(Znth(k,B_tableau_pivot,0),IB_tableau_pivot,0) == 1)) &&
 (forall (k: Z), (0 <= k && k < V_tableau_pivot) => (0 <= Znth(k,IB_tableau_pivot,0) && Znth(k,IB_tableau_pivot,0) <= 1 && (Znth(k,IB_tableau_pivot,0) != 0 => In(k,B_tableau_pivot)))) && Znth(E_tableau_pivot,IB_tableau_pivot,0) == 0 &&
 (forall (i: Z) (k: Z), (0 <= i && i < M_tableau_pivot && 0 <= k && k < M_tableau_pivot) => Znth(16+i*24+Znth(k,B_tableau_pivot,0),N_tableau_pivot,0) == 0) &&
 (forall (k: Z), In(k, simplex_pivot_slots(M_tableau_pivot, V_tableau_pivot)) => (-2147483647 <= Znth(k, N_tableau_pivot, 0) && Znth(k, N_tableau_pivot, 0) <= 2147483647 && 1 <= Znth(k, D_tableau_pivot, 1) && Znth(k, D_tableau_pivot, 1) <= 2147483647 && Zgcd(Zabs(Znth(k, N_tableau_pivot, 0)), Znth(k, D_tableau_pivot, 1)) == 1)) && leaving == Znth(R_tableau_pivot,B_tableau_pivot,0) && 0 <= leaving && leaving < V_tableau_pivot && leaving != E_tableau_pivot &&
 Zlength(CN) == 400 && Zlength(CD) == 400 && (forall (k: Z), In(k,simplex_pivot_slots(M_tableau_pivot,V_tableau_pivot)) => (-2147483647 <= Znth(k,CN,0) && Znth(k,CN,0) <= 2147483647 && 1 <= Znth(k,CD,1) && Znth(k,CD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,CN,0)),Znth(k,CD,1)) == 1)) && simplex_pivot_columns_progress(N_tableau_pivot,D_tableau_pivot,V_tableau_pivot,R_tableau_pivot,E_tableau_pivot,leaving,i,j,FN,FD,CN,CD) && 0 <= i && i < M_tableau_pivot && i != R_tableau_pivot && 0 <= j && j < V_tableau_pivot && FN != 0 && -2147483647 <= Znth(16+R_tableau_pivot*24+j,CN,0) && Znth(16+R_tableau_pivot*24+j,CN,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+j,CD,1) && Znth(16+R_tableau_pivot*24+j,CD,1) <= 2147483647 && -2147483647 <= Znth(16+i*24+j,CN,0) && Znth(16+i*24+j,CN,0) <= 2147483647 && 1 <= Znth(16+i*24+j,CD,1) && Znth(16+i*24+j,CD,1) <= 2147483647 && -2147483647 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) <= 2147483647 && -2147483647 <= FN && FN <= 2147483647 && 1 <= FD && FD <= 2147483647 && simplex_pivot_factor(N_tableau_pivot,D_tableau_pivot,V_tableau_pivot,R_tableau_pivot,E_tableau_pivot,leaving,i,FN,FD) &&
store(&(s->rows),M_tableau_pivot) * store(&(s->vars),V_tableau_pivot) * IntArray::full(s->basic,M_tableau_pivot,B_tableau_pivot) * IntArray::full(s->is_basic,V_tableau_pivot,IB_tableau_pivot) * simplex_pivot_except(s,M_tableau_pivot,V_tableau_pivot,CN,CD,16+R_tableau_pivot*24+j,16+i*24+j) * store(&(s->a[row][j].num),Znth(16+R_tableau_pivot*24+j,CN,0)) * store(&(s->a[row][j].den),Znth(16+R_tableau_pivot*24+j,CD,1)) * store(&(s->a[i][j].num),Znth(16+i*24+j,CN,0)) * store(&(s->a[i][j].den),Znth(16+i*24+j,CD,1)) * store(&(pivot.num),Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0)) * store(&(pivot.den),Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1)) * store(&(one.num),1) * store(&(one.den),1) * undef_data_at(&(term.num)) * undef_data_at(&(term.den)) * store(&(factor.num),FN) * store(&(factor.den),FD) */
                    if (j != entering) {
                        if (!rat_mul(&factor, &s->a[row][j], &term) /*@ where (out_undef) A=factor.num, B=factor.den, C=s->a[row][j].num, D=s->a[row][j].den $ tableau_pivot */) return 0;
                        if (!rat_add(&s->a[i][j], &term, &s->a[i][j]) /*@ where (r_eq_x) */) return 0;
                    }
                }
            }

/*@ Assert exists CN CD FN FD, s == S_tableau_pivot && row == R_tableau_pivot && entering == E_tableau_pivot && 1 <= M_tableau_pivot && M_tableau_pivot <= 16 && 1 <= V_tableau_pivot && V_tableau_pivot <= 24 &&
 0 <= R_tableau_pivot && R_tableau_pivot < M_tableau_pivot && 0 <= E_tableau_pivot && E_tableau_pivot < V_tableau_pivot && Zlength(N_tableau_pivot) == 400 && Zlength(D_tableau_pivot) == 400 &&
 NoDup(B_tableau_pivot) && (forall (k: Z), (0 <= k && k < M_tableau_pivot) => (0 <= Znth(k,B_tableau_pivot,0) && Znth(k,B_tableau_pivot,0) < V_tableau_pivot && Znth(Znth(k,B_tableau_pivot,0),IB_tableau_pivot,0) == 1)) &&
 (forall (k: Z), (0 <= k && k < V_tableau_pivot) => (0 <= Znth(k,IB_tableau_pivot,0) && Znth(k,IB_tableau_pivot,0) <= 1 && (Znth(k,IB_tableau_pivot,0) != 0 => In(k,B_tableau_pivot)))) && Znth(E_tableau_pivot,IB_tableau_pivot,0) == 0 &&
 (forall (i: Z) (k: Z), (0 <= i && i < M_tableau_pivot && 0 <= k && k < M_tableau_pivot) => Znth(16+i*24+Znth(k,B_tableau_pivot,0),N_tableau_pivot,0) == 0) &&
 (forall (k: Z), In(k, simplex_pivot_slots(M_tableau_pivot, V_tableau_pivot)) => (-2147483647 <= Znth(k, N_tableau_pivot, 0) && Znth(k, N_tableau_pivot, 0) <= 2147483647 && 1 <= Znth(k, D_tableau_pivot, 1) && Znth(k, D_tableau_pivot, 1) <= 2147483647 && Zgcd(Zabs(Znth(k, N_tableau_pivot, 0)), Znth(k, D_tableau_pivot, 1)) == 1)) && leaving == Znth(R_tableau_pivot,B_tableau_pivot,0) && 0 <= leaving && leaving < V_tableau_pivot && leaving != E_tableau_pivot &&
 Zlength(CN) == 400 && Zlength(CD) == 400 && (forall (k: Z), In(k,simplex_pivot_slots(M_tableau_pivot,V_tableau_pivot)) => (-2147483647 <= Znth(k,CN,0) && Znth(k,CN,0) <= 2147483647 && 1 <= Znth(k,CD,1) && Znth(k,CD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,CN,0)),Znth(k,CD,1)) == 1)) && simplex_pivot_other_ready(N_tableau_pivot,D_tableau_pivot,V_tableau_pivot,R_tableau_pivot,E_tableau_pivot,leaving,i,FN,FD,CN,CD) && 0 <= i && i < M_tableau_pivot && i != R_tableau_pivot && -2147483647 <= Znth(16+i*24+E_tableau_pivot,CN,0) && Znth(16+i*24+E_tableau_pivot,CN,0) <= 2147483647 && 1 <= Znth(16+i*24+E_tableau_pivot,CD,1) && Znth(16+i*24+E_tableau_pivot,CD,1) <= 2147483647 && -2147483647 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) <= 2147483647 && -2147483647 <= FN && FN <= 2147483647 && 1 <= FD && FD <= 2147483647 && simplex_pivot_factor(N_tableau_pivot,D_tableau_pivot,V_tableau_pivot,R_tableau_pivot,E_tableau_pivot,leaving,i,FN,FD) &&
store(&(s->rows),M_tableau_pivot) * store(&(s->vars),V_tableau_pivot) * IntArray::full(s->basic,M_tableau_pivot,B_tableau_pivot) * IntArray::full(s->is_basic,V_tableau_pivot,IB_tableau_pivot) * simplex_pivot_except(s,M_tableau_pivot,V_tableau_pivot,CN,CD,16+i*24+E_tableau_pivot,16+i*24+E_tableau_pivot) * store(&(s->a[i][entering].num),Znth(16+i*24+E_tableau_pivot,CN,0)) * store(&(s->a[i][entering].den),Znth(16+i*24+E_tableau_pivot,CD,1)) * store(&(pivot.num),Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0)) * store(&(pivot.den),Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1)) * store(&(one.num),1) * store(&(one.den),1) * undef_data_at(&(term.num)) * undef_data_at(&(term.den)) * store(&(factor.num),FN) * store(&(factor.den),FD) * undef_data_at(&j) */
            rat_zero(&s->a[i][entering]) /*@ where (out_known) */;
        }
    }

/*@ Assert exists CN CD, s == S_tableau_pivot && row == R_tableau_pivot && entering == E_tableau_pivot && 1 <= M_tableau_pivot && M_tableau_pivot <= 16 && 1 <= V_tableau_pivot && V_tableau_pivot <= 24 &&
 0 <= R_tableau_pivot && R_tableau_pivot < M_tableau_pivot && 0 <= E_tableau_pivot && E_tableau_pivot < V_tableau_pivot && Zlength(N_tableau_pivot) == 400 && Zlength(D_tableau_pivot) == 400 && Zlength(IB_tableau_pivot) == V_tableau_pivot &&
 NoDup(B_tableau_pivot) && (forall (k: Z), (0 <= k && k < M_tableau_pivot) => (0 <= Znth(k,B_tableau_pivot,0) && Znth(k,B_tableau_pivot,0) < V_tableau_pivot && Znth(Znth(k,B_tableau_pivot,0),IB_tableau_pivot,0) == 1)) &&
 (forall (k: Z), (0 <= k && k < V_tableau_pivot) => (0 <= Znth(k,IB_tableau_pivot,0) && Znth(k,IB_tableau_pivot,0) <= 1 && (Znth(k,IB_tableau_pivot,0) != 0 => In(k,B_tableau_pivot)))) && Znth(E_tableau_pivot,IB_tableau_pivot,0) == 0 &&
 (forall (i: Z) (k: Z), (0 <= i && i < M_tableau_pivot && 0 <= k && k < M_tableau_pivot) => Znth(16+i*24+Znth(k,B_tableau_pivot,0),N_tableau_pivot,0) == 0) &&
 (forall (k: Z), In(k, simplex_pivot_slots(M_tableau_pivot, V_tableau_pivot)) => (-2147483647 <= Znth(k, N_tableau_pivot, 0) && Znth(k, N_tableau_pivot, 0) <= 2147483647 && 1 <= Znth(k, D_tableau_pivot, 1) && Znth(k, D_tableau_pivot, 1) <= 2147483647 && Zgcd(Zabs(Znth(k, N_tableau_pivot, 0)), Znth(k, D_tableau_pivot, 1)) == 1)) && leaving == Znth(R_tableau_pivot,B_tableau_pivot,0) && 0 <= leaving && leaving < V_tableau_pivot && leaving != E_tableau_pivot &&
 Zlength(CN) == 400 && Zlength(CD) == 400 && (forall (k: Z), In(k,simplex_pivot_slots(M_tableau_pivot,V_tableau_pivot)) => (-2147483647 <= Znth(k,CN,0) && Znth(k,CN,0) <= 2147483647 && 1 <= Znth(k,CD,1) && Znth(k,CD,1) <= 2147483647 && Zgcd(Zabs(Znth(k,CN,0)),Znth(k,CD,1)) == 1)) && simplex_pivot_rows_progress(N_tableau_pivot,D_tableau_pivot,V_tableau_pivot,R_tableau_pivot,E_tableau_pivot,leaving,i,CN,CD) && i == M_tableau_pivot && -2147483647 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0) <= 2147483647 && 1 <= Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) && Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1) <= 2147483647 &&
store(&(s->rows),M_tableau_pivot) * store(&(s->vars),V_tableau_pivot) * IntArray::missing_i(s->basic,row,0,M_tableau_pivot,B_tableau_pivot) * store(&(s->basic[row]),leaving) * simplex_pivot_flags_except(s,V_tableau_pivot,IB_tableau_pivot,leaving,entering) * store(&(s->is_basic[leaving]),1) * store(&(s->is_basic[entering]),0) * simplex_pivot_memory(s,M_tableau_pivot,V_tableau_pivot,CN,CD) * store(&(pivot.num),Znth(16+R_tableau_pivot*24+E_tableau_pivot,N_tableau_pivot,0)) * store(&(pivot.den),Znth(16+R_tableau_pivot*24+E_tableau_pivot,D_tableau_pivot,1)) * store(&(one.num),1) * store(&(one.den),1) * undef_data_at(&(term.num)) * undef_data_at(&(term.den)) * undef_data_at(&(factor.num)) * undef_data_at(&(factor.den)) * undef_data_at(&j) */
    s->basic[row] = entering;
    s->is_basic[leaving] = 0; s->is_basic[entering] = 1;
    return 1;
}
