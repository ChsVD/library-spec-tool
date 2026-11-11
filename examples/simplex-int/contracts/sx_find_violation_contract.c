/* 独立接口参考：仅必要类型、声明与规约，不含函数实现。 */
/* ========================================================================
 * 11. sx_find_violation — 扫描约束违反情况，选择最小基本变量编号
 * 来源：qcp/QCP_examples/Applications_human/simplex_find_violation_retry/sx_find_violation.c
 * 验证运行：simplex_find_violation_retry-20261102093641；final-check: done。
 * separated_search：两个输出可写、互相分离且与整个状态分离；不读旧输出。
 * 成功：最小违反基本变量编号，同编号选最早物理行；本行上界违反覆盖下界。
 * 算术失败：返回0，保留失败行之前完整处理前缀的候选；不提交失败行。
 * 空扫描：返回1，row=-1，direction=0。精确模型具有计算等价性证明。
 * 允许重复基本变量索引；只要求启用且被访问的分数已初始化。
 * 未知内存权限不等于原始字节/初始化标签保持；无完整求解器正确性结论。
 * 尚未独立测试上层调用（含已初始化/混合输出的入口匹配）。
 * 旧 blocked 案例及共享库保留只读；本接口使用新的 retry 公共库。
 * ======================================================================== */
#define SX_INPUT_VARS 8
#define SX_ROWS 16
#define SX_VARS (SX_INPUT_VARS + SX_ROWS)

struct SxRat { int num; int den; };

struct SxState {
    int rows, vars, inputs;
    int basic[SX_ROWS];
    int is_basic[SX_VARS];
    int has_lower[SX_VARS], has_upper[SX_VARS];
    struct SxRat lower[SX_VARS], upper[SX_VARS], value[SX_VARS];
    struct SxRat rhs[SX_ROWS], a[SX_ROWS][SX_VARS];
};

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_find_violation_retry.simplex_find_violation_retry_lib */
/*@ Extern Coq
 (simplex_find_violation_spec : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_scan_prefix : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_scan_slots_memory : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Assertion)
 (simplex_scan_slots_except : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Assertion)
 (simplex_scan_unused_memory : Z -> Z -> Assertion)
 (simplex_scan_output_separation : Z -> Z -> Z -> Prop)
 (In : {A} -> A -> list A -> Prop)
*/

int sx_find_violation(struct SxState *s, int *row, int *direction)
/*@ separated_search
 With (BAS : list Z) (HL : list Z) (HU : list Z) (VN : list Z) (VD : list Z) (LN : list Z) (LD : list Z) (UN : list Z) (UD : list Z) M V S P Q
 Require s == S && row == P && direction == Q &&
 simplex_scan_output_separation(s, row, direction) &&
 0 <= M && M <= 16 && 0 <= V && V <= 24 &&
 (forall j, (0 <= j && j < M) => (0 <= Znth(j, BAS, 0) && Znth(j, BAS, 0) < V)) &&
 (forall j, (In(j, BAS) && (Znth(j, HL, 0) != 0 || Znth(j, HU, 0) != 0)) =>
    (-2147483648 <= Znth(j, VN, 0) && Znth(j, VN, 0) <= 2147483647 && 1 <= Znth(j, VD, 0) && Znth(j, VD, 0) <= 2147483647)) &&
 (forall j, (In(j, BAS) && Znth(j, HL, 0) != 0) =>
    (-2147483648 <= Znth(j, LN, 0) && Znth(j, LN, 0) <= 2147483647 && 1 <= Znth(j, LD, 0) && Znth(j, LD, 0) <= 2147483647)) &&
 (forall j, (In(j, BAS) && Znth(j, HU, 0) != 0) =>
    (-2147483648 <= Znth(j, UN, 0) && Znth(j, UN, 0) <= 2147483647 && 1 <= Znth(j, UD, 0) && Znth(j, UD, 0) <= 2147483647)) &&
 store(&(s->rows), M) * store(&(s->vars), V) *
 IntArray::full(s->basic, M, BAS) * simplex_scan_slots_memory(s, BAS, HL, HU, VN, VD, LN, LD, UN, UD) *
 simplex_scan_unused_memory(s, M) * undef_data_at(row) * undef_data_at(direction)
 Ensure exists R D, simplex_find_violation_spec(BAS, HL, HU, VN, VD, LN, LD, UN, UD, V, M, __return, R, D) &&
 store(&(((struct SxState *)S)->rows), M) * store(&(((struct SxState *)S)->vars), V) *
 IntArray::full(((struct SxState *)S)->basic, M, BAS) * simplex_scan_slots_memory(((struct SxState *)S), BAS, HL, HU, VN, VD, LN, LD, UN, UD) *
 simplex_scan_unused_memory(((struct SxState *)S), M) * data_at(((int *)P), int, R) * data_at(((int *)Q), int, D)
*/
;
