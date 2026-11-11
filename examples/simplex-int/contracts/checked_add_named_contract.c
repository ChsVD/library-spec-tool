/* ========================================================================
 * 03. checked_add — 完整 int32 域受检加法，命名规约
 * 来源：qcp/QCP_examples/Applications_human/simplex_checked_add_branches/checked_add.c
 * 验证运行：simplex_checked_add_branches-20261102024202，final-check done。
 * out_undef失败归还undef权限；out_known失败保留old。成功均写精确和。
 * flag=1当且仅当两输入非INT_MIN，且和在[-INT_MAX,INT_MAX]内。
 * 原实现不变，复用原公共库；旧析取接口保留在checked_add_legacy_disjunctive_contract.c。
 * 调用匹配测试等待rat_add；不保证未知入口字节/初始化标签精确保留。
 * ======================================================================== */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_checked_add.simplex_checked_add_lib */
/*@ Extern Coq (checked_add_flag : Z -> Z -> Z) */

static int checked_add(int x, int y, int *out)
  /*@ out_undef
      With A B
      Require x == A && y == B &&
              -2147483648 <= x && x <= 2147483647 &&
              -2147483648 <= y && y <= 2147483647 &&
              undef_data_at(out)
      Ensure __return == checked_add_flag(A, B) &&
             ((__return == 1 && data_at(out, int, A + B)) ||
              (__return == 0 && undef_data_at(out)))
  */
  /*@ out_known
      With A B old
      Require x == A && y == B &&
              -2147483648 <= x && x <= 2147483647 &&
              -2147483648 <= y && y <= 2147483647 &&
              data_at(out, int, old)
      Ensure __return == checked_add_flag(A, B) &&
             ((__return == 1 && data_at(out, int, A + B)) ||
              (__return == 0 && data_at(out, int, old)))
  */
;
