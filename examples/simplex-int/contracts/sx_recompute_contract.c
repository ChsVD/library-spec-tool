/* 独立已证接口参考：仅必要类型与目标声明，无callee重复声明或实现。 */
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

/* ========================================================================
 * 12. sx_recompute — 精确顺序重算与完成行的部分提交
 * 来源：qcp/QCP_examples/Applications_human/simplex_recompute/sx_recompute.c
 * 验证运行：simplex_recompute-20261103004647；controller final-check: done。
 * recompute：合法活动分数，精确返回值/实际value等于compute；不要求basic互异或标记一致。
 * zero_rows：仅rows字段资源，其余成员可由框架保持，无需初始化vars/数组。
 * 失败保留此前完成行；未完成行不写回。成功行数学和与初始化必成功已有库引理。
 * 未单独导出跨行入口快照的全行静态公式；该推论需标记一致性/基本索引互异条件。
 * 未单独证明C终止性或完整求解器可靠性；未知权限不等于精确填充字节承诺。
 * ======================================================================== */
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
/*@ zero_rows
 With (S : Z)
 Require s == S && store(&(s->rows), 0)
 Ensure __return == 1 && store(&(((struct SxState *)S)->rows), 0)
*/
;
