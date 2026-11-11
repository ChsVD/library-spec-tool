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
