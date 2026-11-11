/* 独立已证接口：完整原 sx_pivot 实现，run simplex_pivot-20261103051637，final-check done。
 * tableau_pivot：精确受检顺序/失败前缀，成功闭式分数公式与方程解集等价。
 * 原生 a[16][24] 布局；400 槽 N/D 为纯数学索引，不要求非活动内存初始化。
 * 不读取 value/bounds/inputs；其已有资源由调用者 frame 保留。
 * 未知权限不等于字节/初始化标签快照；本文件无实现或重复 callee 声明。 */
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
