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
 With S R V (IB AN AD RN RD B VN VD : list Z)
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
{
    int i, j;
    struct SxRat sum, product;
/*@ Inv Assert exists CN CD,
 s == S && 0 <= i && i <= R && 0 <= R && R <= 16 && 0 <= V && V <= 24 &&
 Zlength(AN) == R*24 && Zlength(AD) == R*24 && Zlength(RN) == R && Zlength(RD) == R &&
 (forall (k: Z), (0 <= k && k < R) => (0 <= Znth(k, B, 0) && Znth(k, B, 0) < V)) &&
Forall(Z::le(-2147483647), AN) && Forall(Z::ge(2147483647), AN) && Forall(Z::le(1), AD) && Forall(Z::ge(2147483647), AD) &&
Forall(Z::le(-2147483647), RN) && Forall(Z::ge(2147483647), RN) && Forall(Z::le(1), RD) && Forall(Z::ge(2147483647), RD) &&
Forall(Z::le(-2147483647), CN) && Forall(Z::ge(2147483647), CN) && Forall(Z::le(1), CD) && Forall(Z::ge(2147483647), CD) &&

 Zlength(CN) == V && Zlength(CD) == V &&
 simplex_recompute_prefix(IB, AN, AD, RN, RD, B, VN, VD, i, V, 1, CN, CD) &&
 store(&(s->rows), R) * store(&(s->vars), V) * IntArray::full(s->basic, R, B) * IntArray::full(s->is_basic, V, IB) * simplex_recompute_rhs(s, R, RN, RD) * simplex_recompute_matrix(s, R, V, AN, AD) * simplex_recompute_values(s, V, CN, CD) * undef_data_at(&j) * undef_data_at(&(sum.num)) * undef_data_at(&(sum.den)) * undef_data_at(&(product.num)) * undef_data_at(&(product.den)) */
    for (i = 0; i < s->rows; i++) {
/*@ Assert exists CN CD,
 s == S && 0 <= i && i < R && 0 <= R && R <= 16 && 0 <= V && V <= 24 &&
 Zlength(AN) == R*24 && Zlength(AD) == R*24 && Zlength(RN) == R && Zlength(RD) == R &&
 (forall (k: Z), (0 <= k && k < R) => (0 <= Znth(k, B, 0) && Znth(k, B, 0) < V)) &&
Forall(Z::le(-2147483647), AN) && Forall(Z::ge(2147483647), AN) && Forall(Z::le(1), AD) && Forall(Z::ge(2147483647), AD) &&
Forall(Z::le(-2147483647), RN) && Forall(Z::ge(2147483647), RN) && Forall(Z::le(1), RD) && Forall(Z::ge(2147483647), RD) &&
Forall(Z::le(-2147483647), CN) && Forall(Z::ge(2147483647), CN) && Forall(Z::le(1), CD) && Forall(Z::ge(2147483647), CD) &&

 Zlength(CN) == V && Zlength(CD) == V &&
 simplex_recompute_prefix(IB, AN, AD, RN, RD, B, VN, VD, i, V, 1, CN, CD) &&
 store(&(s->rows), R) * store(&(s->vars), V) * IntArray::full(s->basic, R, B) * IntArray::full(s->is_basic, V, IB) * simplex_recompute_rhs_except(s, R, RN, RD, i) * store(&(s->rhs[i].num), Znth(i, RN, 0)) * store(&(s->rhs[i].den), Znth(i, RD, 0)) * simplex_recompute_matrix(s, R, V, AN, AD) * simplex_recompute_values(s, V, CN, CD) * undef_data_at(&j) * undef_data_at(&(sum.num)) * undef_data_at(&(sum.den)) * undef_data_at(&(product.num)) * undef_data_at(&(product.den)) */
        sum = s->rhs[i];
/*@ Inv Assert exists CN CD N D,
 s == S && 0 <= i && i < R && 0 <= j && j <= V && 0 <= R && R <= 16 && 0 <= V && V <= 24 &&
 Zlength(AN) == R*24 && Zlength(AD) == R*24 && Zlength(RN) == R && Zlength(RD) == R &&
 (forall (k: Z), (0 <= k && k < R) => (0 <= Znth(k, B, 0) && Znth(k, B, 0) < V)) &&
Forall(Z::le(-2147483647), AN) && Forall(Z::ge(2147483647), AN) && Forall(Z::le(1), AD) && Forall(Z::ge(2147483647), AD) &&
Forall(Z::le(-2147483647), RN) && Forall(Z::ge(2147483647), RN) && Forall(Z::le(1), RD) && Forall(Z::ge(2147483647), RD) &&
Forall(Z::le(-2147483647), CN) && Forall(Z::ge(2147483647), CN) && Forall(Z::le(1), CD) && Forall(Z::ge(2147483647), CD) &&

 -2147483647 <= N && N <= 2147483647 && 1 <= D && D <= 2147483647 &&
 Zlength(CN) == V && Zlength(CD) == V &&
 simplex_recompute_prefix(IB, AN, AD, RN, RD, B, VN, VD, i, V, 1, CN, CD) &&
 simplex_recompute_sum(IB, AN, AD, CN, CD, RN, RD, i, j, N, D) &&
 store(&(s->rows), R) * store(&(s->vars), V) * IntArray::full(s->basic, R, B) * IntArray::full(s->is_basic, V, IB) * simplex_recompute_rhs(s, R, RN, RD) * simplex_recompute_matrix(s, R, V, AN, AD) * simplex_recompute_values(s, V, CN, CD) * store(&(sum.num), N) * store(&(sum.den), D) * undef_data_at(&(product.num)) * undef_data_at(&(product.den)) */
        for (j = 0; j < s->vars; j++) {
/*@ Assert exists CN CD N D,
 s == S && 0 <= i && i < R && 0 <= j && j < V && 0 <= R && R <= 16 && 0 <= V && V <= 24 &&
 Zlength(AN) == R*24 && Zlength(AD) == R*24 && Zlength(RN) == R && Zlength(RD) == R &&
 (forall (k: Z), (0 <= k && k < R) => (0 <= Znth(k, B, 0) && Znth(k, B, 0) < V)) &&
Forall(Z::le(-2147483647), AN) && Forall(Z::ge(2147483647), AN) && Forall(Z::le(1), AD) && Forall(Z::ge(2147483647), AD) &&
Forall(Z::le(-2147483647), RN) && Forall(Z::ge(2147483647), RN) && Forall(Z::le(1), RD) && Forall(Z::ge(2147483647), RD) &&
Forall(Z::le(-2147483647), CN) && Forall(Z::ge(2147483647), CN) && Forall(Z::le(1), CD) && Forall(Z::ge(2147483647), CD) &&

 -2147483647 <= N && N <= 2147483647 && 1 <= D && D <= 2147483647 &&
 Zlength(CN) == V && Zlength(CD) == V &&
 simplex_recompute_prefix(IB, AN, AD, RN, RD, B, VN, VD, i, V, 1, CN, CD) &&
 simplex_recompute_sum(IB, AN, AD, CN, CD, RN, RD, i, j, N, D) &&
 store(&(s->rows), R) * store(&(s->vars), V) * IntArray::full(s->basic, R, B) * IntArray::full(s->is_basic, V, IB) * simplex_recompute_rhs(s, R, RN, RD) * simplex_recompute_matrix_except(s, R, V, AN, AD, i, j) * store(&(s->a[i][j].num), Znth(i*24+j, AN, 0)) * store(&(s->a[i][j].den), Znth(i*24+j, AD, 0)) * simplex_recompute_values_except(s, V, CN, CD, j) * store(&(s->value[j].num), Znth(j, CN, 0)) * store(&(s->value[j].den), Znth(j, CD, 0)) * store(&(sum.num), N) * store(&(sum.den), D) * undef_data_at(&(product.num)) * undef_data_at(&(product.den)) */
            if (!s->is_basic[j] && s->a[i][j].num != 0) {
                if (!rat_mul(&s->a[i][j], &s->value[j], &product) /*@ where (out_undef) */) return 0;
                if (!rat_add(&sum, &product, &sum) /*@ where (r_eq_x) */) return 0;
            }
        }
/*@ Assert exists CN CD N D,
 s == S && s->basic[i] == Znth(i, B, 0) && 0 <= i && i < R && 0 <= j && j == V && 0 <= R && R <= 16 && 0 <= V && V <= 24 &&
 Zlength(AN) == R*24 && Zlength(AD) == R*24 && Zlength(RN) == R && Zlength(RD) == R &&
 (forall (k: Z), (0 <= k && k < R) => (0 <= Znth(k, B, 0) && Znth(k, B, 0) < V)) &&
Forall(Z::le(-2147483647), AN) && Forall(Z::ge(2147483647), AN) && Forall(Z::le(1), AD) && Forall(Z::ge(2147483647), AD) &&
Forall(Z::le(-2147483647), RN) && Forall(Z::ge(2147483647), RN) && Forall(Z::le(1), RD) && Forall(Z::ge(2147483647), RD) &&
Forall(Z::le(-2147483647), CN) && Forall(Z::ge(2147483647), CN) && Forall(Z::le(1), CD) && Forall(Z::ge(2147483647), CD) &&

 -2147483647 <= N && N <= 2147483647 && 1 <= D && D <= 2147483647 &&
 Zlength(CN) == V && Zlength(CD) == V &&
 simplex_recompute_prefix(IB, AN, AD, RN, RD, B, VN, VD, i, V, 1, CN, CD) &&
 simplex_recompute_sum(IB, AN, AD, CN, CD, RN, RD, i, j, N, D) &&
 store(&(s->rows), R) * store(&(s->vars), V) * IntArray::full(s->basic, R, B) * IntArray::full(s->is_basic, V, IB) * simplex_recompute_rhs(s, R, RN, RD) * simplex_recompute_matrix(s, R, V, AN, AD) * simplex_recompute_values_except(s, V, CN, CD, Znth(i, B, 0)) * store(&(s->value[Znth(i, B, 0)].num), Znth(Znth(i, B, 0), CN, 0)) * store(&(s->value[Znth(i, B, 0)].den), Znth(Znth(i, B, 0), CD, 0)) * store(&(sum.num), N) * store(&(sum.den), D) * undef_data_at(&(product.num)) * undef_data_at(&(product.den)) */
        s->value[s->basic[i]].num = sum.num;
        s->value[s->basic[i]].den = sum.den;
    }
    return 1;
}

