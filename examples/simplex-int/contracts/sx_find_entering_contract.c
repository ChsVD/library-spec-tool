/* 独立接口参考文件：仅声明、规约及必要类型，不包含实现。 */
/* ========================================================================
 * 10. sx_find_entering — 按列顺序寻找首个可进入变量
 * 来源：qcp/QCP_examples/Applications_human/simplex_find_entering/sx_find_entering.c
 * 验证运行：simplex_find_entering-20261102041019；final-check: done。
 * separated_search：输出指针与整个 SxState 分离；入口旧输出值无需已知。
 * 精确结果由 simplex_find_entering_spec 给出；compute_iff 证明其等价于计算函数。
 * q=1,e>=0：首个可进入列；q=1,e=-1：所有列跳过；q=0,e=-1：首次算术失败。
 * V=0 时不要求 row 有效；V>0 时要求 0<=row<16；direction 包含 0。
 * 保留已建模字段与未知内存权限；不承诺未知字段原始字节值。
 * 未单独测试上层调用，不包含完整求解器或 UNSAT 正确性结论。
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

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_find_entering.simplex_find_entering_lib */
/*@ Extern Coq
 (Forall : {A} -> (A -> Prop) -> list A -> Prop)
 (Z::le : Z -> Z -> Prop)
 (Z::ge : Z -> Z -> Prop)
 (simplex_find_entering_spec : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_enter_skipped : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
 (simplex_enter_slots_memory : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Assertion)
 (simplex_enter_slots_except : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Assertion)
 (simplex_enter_coeff_except : Z -> Z -> Z -> list Z -> list Z -> Z -> Assertion)
 (simplex_enter_unused_memory : Z -> Assertion)
 (simplex_enter_output_separation : Z -> Z -> Prop)
*/
int sx_find_entering(struct SxState *s, int row, int direction, int *entering)
/*@ separated_search
    With V S R D O (IB CN CD HL HU VN VD LN LD UN UD : list Z)
    Require s == S && row == R && direction == D && entering == O && 0 <= V && V <= 24 && (V == 0 || (0 <= row && row < 16)) &&
      -2147483648 <= row && row <= 2147483647 &&
      -2147483648 <= direction && direction <= 2147483647 &&
      Zlength(CN) == V && Zlength(CD) == V && Zlength(VN) == V && Zlength(VD) == V &&
      Forall(Z::le(-2147483647), CN) && Forall(Z::ge(2147483647), CN) &&
      Forall(Z::le(1), CD) && Forall(Z::ge(2147483647), CD) &&
      Forall(Z::le(-2147483647), VN) && Forall(Z::ge(2147483647), VN) &&
      Forall(Z::le(1), VD) && Forall(Z::ge(2147483647), VD) &&
      (forall (i: Z), (0 <= i && i < V && Znth(i, HL, 0) != 0) =>
        (-2147483647 <= Znth(i, LN, 0) && Znth(i, LN, 0) <= 2147483647 &&
         1 <= Znth(i, LD, 0) && Znth(i, LD, 0) <= 2147483647)) &&
      (forall (i: Z), (0 <= i && i < V && Znth(i, HU, 0) != 0) =>
        (-2147483647 <= Znth(i, UN, 0) && Znth(i, UN, 0) <= 2147483647 &&
         1 <= Znth(i, UD, 0) && Znth(i, UD, 0) <= 2147483647)) && simplex_enter_output_separation(s, entering) &&
      store(&(s->vars), V) *
      IntArray::full(s->is_basic, V, IB) * IntArray::undef_seg(s->is_basic, V, 24) *
      IntArray::full(s->has_lower, V, HL) * IntArray::undef_seg(s->has_lower, V, 24) *
      IntArray::full(s->has_upper, V, HU) * IntArray::undef_seg(s->has_upper, V, 24) *
      simplex_enter_slots_memory(s, row, V, CN, CD, HL, HU, VN, VD, LN, LD, UN, UD) * simplex_enter_unused_memory(s) * undef_data_at(entering)
    Ensure exists e, simplex_find_entering_spec(IB, CN, HL, HU, VN, VD, LN, LD, UN, UD,
        D, V, __return, e) && store(&(((struct SxState *)S)->vars), V) *
      IntArray::full(((struct SxState *)S)->is_basic, V, IB) * IntArray::undef_seg(((struct SxState *)S)->is_basic, V, 24) *
      IntArray::full(((struct SxState *)S)->has_lower, V, HL) * IntArray::undef_seg(((struct SxState *)S)->has_lower, V, 24) *
      IntArray::full(((struct SxState *)S)->has_upper, V, HU) * IntArray::undef_seg(((struct SxState *)S)->has_upper, V, 24) *
      simplex_enter_slots_memory(((struct SxState *)S), R, V, CN, CD, HL, HU, VN, VD, LN, LD, UN, UD) * simplex_enter_unused_memory(((struct SxState *)S)) * data_at(((int *)O), int, e)
*/
;
