/* ========================================================================
 * 03. checked_add — 完整 int32 域的受检加法（有效输出单元接口）
 * 来源（相对本实验根目录）：
 * qcp/QCP_examples/Applications_human/simplex_checked_add/checked_add.c
 * 通用库：
 * qcp/Rocq/examples/Applications_human/simplex_checked_add/simplex_checked_add_lib.v
 * 验证运行：simplex_checked_add-20261101231825，controller final-check: done。
 * checked_add_flag(X,Y)=1 当且仅当 X、Y 均非 -2147483648 且
 * -2147483647 <= X+Y <= 2147483647；否则为0。和为数学整数运算。
 * known=1：输出入口值为old，失败后保留old。
 * known=0：输出内容未知/可未初始化，失败后归还undef权限；
 *          不单独表达入口字节或初始化标签精确保留。
 * 成功时两种模式均写入精确入口和A+B。
 * 限制：未验证无需输出权限/NULL的额外拒绝接口，也未做独立调用匹配测试。
 * ======================================================================== */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_checked_add.simplex_checked_add_lib */
/*@ Extern Coq (checked_add_flag : Z -> Z -> Z) */

static int checked_add(int x, int y, int *out)
  /*@ With A B known old
      Require x == A && y == B &&
              -2147483648 <= x && x <= 2147483647 &&
              -2147483648 <= y && y <= 2147483647 &&
              ((known == 0 && undef_data_at(out)) ||
               (known == 1 && data_at(out, int, old)))
      Ensure __return == checked_add_flag(A, B) &&
             ((__return == 1 && data_at(out, int, A + B)) ||
              (__return == 0 &&
               ((known == 0 && undef_data_at(out)) ||
                (known == 1 && data_at(out, int, old)))))
  */
;

