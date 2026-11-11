/* ========================================================================
 * 02. checked_mul — 完整 int32 域的受检乘法
 * 来源（相对本实验根目录）：
 * qcp/QCP_examples/Applications_human/simplex_checked_mul/checked_mul.c
 * 通用库：
 * qcp/Rocq/examples/Applications_human/simplex_checked_mul/simplex_checked_mul_lib.v
 * 验证运行：simplex_checked_mul-20261101223403，controller final-check: done。
 * checked_mul_flag(X,Y)=1 当且仅当 X、Y 均非 -2147483648 且
 * |X*Y| <= 2147483647；否则为0。乘积、绝对值均为数学整数运算。
 * known=1：输出入口值为old，失败后保留old。
 * known=0：输出内容未知/可未初始化，失败后归还undef权限；
 *          这不单独表达入口字节或初始化标签精确保留。
 * 成功时两种模式均写入精确乘积A*B。
 * 本轮尚未做独立调用者的规约匹配测试。
 * ======================================================================== */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_checked_mul.simplex_checked_mul_lib */
/*@ Extern Coq (checked_mul_flag : Z -> Z -> Z) */

static int checked_mul(int x, int y, int *out)
  /*@ With A B known old
      Require x == A && y == B &&
              -2147483648 <= x && x <= 2147483647 &&
              -2147483648 <= y && y <= 2147483647 &&
              ((known == 0 && undef_data_at(out)) ||
               (known == 1 && data_at(out, int, old)))
      Ensure __return == checked_mul_flag(A, B) &&
             ((__return == 1 && data_at(out, int, A * B)) ||
              (__return == 0 &&
               ((known == 0 && undef_data_at(out)) ||
                (known == 1 && data_at(out, int, old)))))
  */
;

