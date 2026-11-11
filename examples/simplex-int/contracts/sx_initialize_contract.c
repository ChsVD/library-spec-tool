/* 独立已证接口参考：仅类型和目标声明/四命名规约，无实现/callee重复声明。 */
#define INT_MIN (-2147483647 - 1)
#define INT_MAX 2147483647
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




/* ========================================================================
 * 13. sx_initialize — 精确初始化整数不等式工作表
 * 来源：qcp/QCP_examples/Applications_human/simplex_initialize/sx_initialize.c
 * 验证运行：simplex_initialize-20261103024305；controller final-check: done。
 * invalid_dimensions：无s/c内存要求，非法尺寸精确返回0。
 * rejected_coefficient：仅持有活动输入，含INT_MIN精确返回0且不访问s，无s/c分离要求。
 * zero_rows：不要求c所指内存；成功初始化所写字段，其余由框架保留。
 * initialized_matrix_non_alias：旧输出可未初始化，输入stride9，状态矩阵stride24；
 * 返回1并精确建立尺寸、basis/flags/bounds/RHS/矩阵/value的closed-form Init状态。
 * 四分支真实生成/证明；rat_zero与sx_recompute实际调用的合同与已证接口完全一致。
 * 函数成功不表示辅助变量已满足其上界或原约束可行；不包括完整求解器可靠性。
 * ======================================================================== */
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
