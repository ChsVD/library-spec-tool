/*
 * Simplex 函数声明与已验证规约汇总
 *
 * 用途：后续 QCP agent 查询函数接口、调用前提和返回保证时，优先阅读本文件。
 * 本文件不包含实现或循环不变量；需要检查实现、修改规约或重新证明时再查来源。
 * 通用定义与引理见各条目的 Coq Import；不得省略其适用前提。
 *
 * 本文件是从已验证源码抽取的接口参考，不是独立实现或额外证明产物。
 * 保留原声明的 static 属性，不将内部函数改为外部链接接口。
 */

/* ========================================================================
 * 01. positive_gcd — 非负 int32 输入的最大公因数
 * 来源（相对本实验根目录）：
 * qcp/QCP_examples/Applications_human/simplex_positive_gcd/positive_gcd.c
 * 通用库：
 * qcp/Rocq/examples/Applications_human/simplex_positive_gcd/simplex_positive_gcd_lib.v
 * 验证运行：simplex_positive_gcd-20261101220217，controller final-check: done。
 * Zgcd 表示 Coq 的 Z.gcd；包含单零和双零输入，Zgcd(0,0)=0。
 * 验证范围：QCP 生成的正确性义务已通过；未单独建立终止性证明。
 * ======================================================================== */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_positive_gcd.simplex_positive_gcd_lib */
/*@ Extern Coq (Zgcd : Z -> Z -> Z) */

static int positive_gcd(int a, int b)
  /*@ With A B
      Require a == A && b == B &&
              0 <= a && a <= 2147483647 &&
              0 <= b && b <= 2147483647 && emp
      Ensure __return == Zgcd(A, B) && emp
  */
;

/* ========================================================================
 * 02. checked_mul — 完整 int32 域受检乘法，SM2风格命名规约
 * 来源：qcp/QCP_examples/Applications_human/simplex_checked_mul_branches/checked_mul.c
 * 验证运行：simplex_checked_mul_branches-20261102002304，final-check done。
 * out_undef：成功写精确乘积，失败归还undef权限（非字节/初始化标签保证）。
 * out_known：成功写精确乘积，失败保留old。
 * 两支均return=checked_mul_flag(A,B)，完整机器输入域，INT_MIN被拒绝。
 * 调用按SM2写法明确选择：checked_mul(...)，附 where (out_undef) A=..., B=... 调用注释
 * 旧析取入口证明保留在原case；旧接口快照见checked_mul_legacy_disjunctive_contract.c。
 * ======================================================================== */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_checked_mul.simplex_checked_mul_lib */
/*@ Extern Coq (checked_mul_flag : Z -> Z -> Z) */

static int checked_mul(int x, int y, int *out)
  /*@ out_undef
      With A B
      Require x == A && y == B &&
              -2147483648 <= x && x <= 2147483647 &&
              -2147483648 <= y && y <= 2147483647 &&
              undef_data_at(out)
      Ensure __return == checked_mul_flag(A, B) &&
             ((__return == 1 && data_at(out, int, A * B)) ||
              (__return == 0 && undef_data_at(out)))
  */
  /*@ out_known
      With A B old
      Require x == A && y == B &&
              -2147483648 <= x && x <= 2147483647 &&
              -2147483648 <= y && y <= 2147483647 &&
              data_at(out, int, old)
      Ensure __return == checked_mul_flag(A, B) &&
             ((__return == 1 && data_at(out, int, A * B)) ||
              (__return == 0 && data_at(out, int, old)))
  */
;

/* ========================================================================
 * 03. checked_add — 完整 int32 域受检加法，命名规约
 * 来源：qcp/QCP_examples/Applications_human/simplex_checked_add_branches/checked_add.c
 * 验证运行：simplex_checked_add_branches-20261102024202，final-check done。
 * out_undef失败归还undef权限；out_known失败保留old。成功均写精确和。
 * flag=1当且仅当两输入非INT_MIN，且和在[-INT_MAX,INT_MAX]内。
 * 原实现不变，复用原公共库；旧析取接口保留在checked_add_legacy_disjunctive_contract.c。
 * out_undef已在rat_add三个分支实际调用且证明通过；out_known未另做调用测试。
 * 不保证未知入口字节/初始化标签精确保留。
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

/* ========================================================================
 * 04. rat_reduce — 有符号分子、正分母的原地约分
 * 来源：qcp/QCP_examples/Applications_human/simplex_rat_reduce/rat_reduce.c
 * 通用库：qcp/Rocq/examples/Applications_human/simplex_rat_reduce/simplex_rat_reduce_lib.v
 * 验证运行：simplex_rat_reduce-20261101234250，controller final-check: done。
 * 输入拥有两个已初始化字段，-INT_MAX<=N<=INT_MAX，1<=D<=INT_MAX。
 * simplex_rat_reduce_result(N,D,P,Q) 精确表示：
 * g=Z.gcd(abs(N),D)，P=Z.quot N g，Q=Z.quot D g。
 * 输出唯一确定、保持数值且互素；N=0得到(0,1)，已互素则不变。
 * 已在本函数符号执行中使用positive_gcd的已验证契约；auto部分由QCP负责。
 * 未额外证明整个C调用链的终止性，也未做rat_reduce外部调用专项测试。
 * ======================================================================== */
struct SxRat { int num; int den; };

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_rat_reduce.simplex_rat_reduce_lib */
/*@ Extern Coq
      (Zabs : Z -> Z)
      (simplex_rat_reduce_result : Z -> Z -> Z -> Z -> Prop)
*/

static void rat_reduce(struct SxRat *r)
  /*@ With N D
      Require -2147483647 <= N && N <= 2147483647 &&
              1 <= D && D <= 2147483647 &&
              store(&(r->num), N) * store(&(r->den), D)
      Ensure exists P Q,
              simplex_rat_reduce_result(N, D, P, Q) &&
              -2147483647 <= P && P <= 2147483647 &&
              1 <= Q && Q <= 2147483647 &&
              Zgcd(Zabs(P), Q) == 1 && N * Q == P * D &&
              (N != 0 || (P == 0 && Q == 1)) &&
              (Zgcd(Zabs(N), D) != 1 || (P == N && Q == D)) &&
              store(&(r->num), P) * store(&(r->den), Q)
  */
;

/* ========================================================================
 * 05. rat_mul — 受检有理数乘法，三对象分离
 * 来源：qcp/QCP_examples/Applications_human/simplex_rat_mul/rat_mul.c
 * 通用库：qcp/Rocq/examples/Applications_human/simplex_rat_mul/simplex_rat_mul_lib.v
 * 验证运行：simplex_rat_mul-20261102004917，final-check done。
 * out_undef/out_known分别表示输出两个字段未知/已知；输入对象均保持。
 * flag先检查分子积，再检查分母积，检查发生在约分前。
 * result为N=A*C、D=B*D、g=gcd(abs(N),D)时的P=N quot g、Q=D quot g。
 * 成功得到唯一既约乘积；失败保持已知旧值或归还undef权限。
 * 限制：不覆盖对象别名/部分重叠、混合已知未知字段、字节或初始化标签保留。
 * 多caller分支调用需用where(callee_branch)和$ caller_branch分别绑定作用域。
 * ======================================================================== */
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

/* ========================================================================
 * 06. rat_compare — 正分母分数的受检精确比较
 * 来源：qcp/QCP_examples/Applications_human/simplex_rat_compare/rat_compare.c
 * 通用库：qcp/Rocq/examples/Applications_human/simplex_rat_compare/simplex_rat_compare_lib.v
 * 验证运行：simplex_rat_compare-20261102013817，final-check done。
 * x/y初始化对象和order单元三块资源分离；分子完整int32，分母1..INT_MAX。
 * flag依序检查A*D、C*B；成功返回1，order精确为数学交叉积比较的-1/0/1。
 * out_known失败保留old，out_undef失败归还undef权限。两输入保持。
 * 不覆盖x=y、输出别名/部分重叠、非正分母或字节/初始化标签保留。
 * 函数自身已证明；尚未进行上层调用者使用本接口的专项测试。
 * ======================================================================== */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_rat_compare.simplex_rat_compare_lib */
/*@ Extern Coq
      (simplex_rat_compare_flag : Z -> Z -> Z -> Z -> Z)
      (simplex_rat_compare_order : Z -> Z -> Z -> Z -> Z)
*/

static int rat_compare(const struct SxRat *x, const struct SxRat *y,
                       int *order)
  /*@ out_undef
      With A B C D
      Require -2147483648 <= A && A <= 2147483647 &&
              -2147483648 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= D && D <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), D) *
              undef_data_at(order)
      Ensure __return == simplex_rat_compare_flag(A, B, C, D) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), D) *
             ((__return == 1 &&
                data_at(order, int, simplex_rat_compare_order(A, B, C, D))) ||
              (__return == 0 && undef_data_at(order)))
  */
  /*@ out_known
      With A B C D old
      Require -2147483648 <= A && A <= 2147483647 &&
              -2147483648 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= D && D <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), D) *
              data_at(order, int, old)
      Ensure __return == simplex_rat_compare_flag(A, B, C, D) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), D) *
             ((__return == 1 &&
                data_at(order, int, simplex_rat_compare_order(A, B, C, D))) ||
              (__return == 0 && data_at(order, int, old)))
  */
;

/* ========================================================================
 * 07. rat_div — 正分母输入分数的受检除法
 * 来源：qcp/QCP_examples/Applications_human/simplex_rat_div/rat_div.c
 * 通用库：qcp/Rocq/examples/Applications_human/simplex_rat_div/simplex_rat_div_lib.v
 * 验证运行：simplex_rat_div-20261102015856，final-check done。
 * 分子[-INT_MAX,INT_MAX]，分母[1,INT_MAX]；允许除数分子为零并返回失败。
 * r_eq_x：out=x，y分离；out_undef/out_known：输入输出均分离。
 * flag先拒绝C=0，再顺序检查P=A*E、Q=B*C。
 * 成功：N=(Q<0 ? -P : P)、D=abs(Q)、g=gcd(abs(N),D)，
 * 实际输出N quot g、D quot g，既约、正分母、范围合法，零输出为(0,1)。
 * 失败保持原地/已知输出旧值，未知输出只归还undef权限；y始终保持。
 * 不覆盖out=y、x=y、三者同址、部分重叠、混合已知/未知字段或INT_MIN分子。
 * 尚未做上层调用者使用rat_div的专项测试或整条调用链终止性证明。
 * ======================================================================== */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_rat_div.simplex_rat_div_lib */
/*@ Extern Coq
      (simplex_rat_div_flag : Z -> Z -> Z -> Z -> Z)
      (simplex_rat_div_result : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/

static int rat_div(const struct SxRat *x, const struct SxRat *y,
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
      Ensure __return == simplex_rat_div_flag(A, B, C, E) &&
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_div_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && A * E * Q == P * (B * C) &&
                (A != 0 || (P == 0 && Q == 1)) &&
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
      Ensure __return == simplex_rat_div_flag(A, B, C, E) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_div_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && A * E * Q == P * (B * C) &&
                (A != 0 || (P == 0 && Q == 1)) &&
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
      Ensure __return == simplex_rat_div_flag(A, B, C, E) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_div_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && A * E * Q == P * (B * C) &&
                (A != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && store(&(out->num), oldn) * store(&(out->den), oldd)))
  */
;

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

/* ========================================================================
 * 09. rat_zero — 将有理数对象置为规范零(0,1)
 * 来源：qcp/QCP_examples/Applications_human/simplex_rat_zero/rat_zero.c
 * 验证运行：simplex_rat_zero-20261102032152，final-check done。
 * out_undef：两个字段可写但值未知；out_known：两个字段已初始化、旧值任意。
 * 不读取旧值，不要求原分母为正或原有理数合法；输出精确为num=0、den=1。
 * 无新增通用定义/引理，无实质FME引理复用；属于无需此类引理的底层赋值函数。
 * 两分支共6条QCP auto义务，0条manual；auto按实验约定由QCP负责。
 * 未单独验证外部caller调用、混合初始化字段接口或非法指针入口。
 * ======================================================================== */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_rat_zero.simplex_rat_zero_lib */

static void rat_zero(struct SxRat *r)
  /*@ out_undef
      Require undef_data_at(&(r->num)) * undef_data_at(&(r->den))
      Ensure store(&(r->num), 0) * store(&(r->den), 1)
  */
  /*@ out_known
      With oldn oldd
      Require store(&(r->num), oldn) * store(&(r->den), oldd)
      Ensure store(&(r->num), 0) * store(&(r->den), 1)
  */
;

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
/* Additive framed_search independently proved in simplex_find_entering_preserve-20261103152352.
 * Minimal known read slice + native24-stride row numerators; other state requires caller frame.
 * 71primary/178split/13groups;27newhelpers +1compute-equivalence consumer theorem.
 */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_find_entering_preserve.simplex_find_entering_preserve_lib */
/*@ Extern Coq
 (simplex_scan_read_memory : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Assertion)
 (simplex_scan_read_except : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Assertion)
*/
/*@ Extern Coq
 (Zrange : Z -> Z -> list Z)
 (simplex_enter_num_memory : Z -> Z -> Z -> list Z -> Assertion)
 (simplex_enter_num_except : Z -> Z -> Z -> list Z -> Z -> Assertion)
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
/*@ framed_search
    With V S R D O (IB CN HL HU VN VD LN LD UN UD : list Z)
    Require s == S && row == R && direction == D && entering == O && 0 <= V && V <= 24 && (V == 0 || (0 <= row && row < 16)) &&
      -2147483648 <= row && row <= 2147483647 &&
      -2147483648 <= direction && direction <= 2147483647 &&
      Zlength(CN) == V && Zlength(VN) == V && Zlength(VD) == V &&
      Forall(Z::le(-2147483647), CN) && Forall(Z::ge(2147483647), CN) &&
      Forall(Z::le(-2147483647), VN) && Forall(Z::ge(2147483647), VN) &&
      Forall(Z::le(1), VD) && Forall(Z::ge(2147483647), VD) &&
      (forall (i: Z), (0 <= i && i < V && Znth(i, HL, 0) != 0) =>
        (-2147483647 <= Znth(i, LN, 0) && Znth(i, LN, 0) <= 2147483647 &&
         1 <= Znth(i, LD, 0) && Znth(i, LD, 0) <= 2147483647)) &&
      (forall (i: Z), (0 <= i && i < V && Znth(i, HU, 0) != 0) =>
        (-2147483647 <= Znth(i, UN, 0) && Znth(i, UN, 0) <= 2147483647 &&
         1 <= Znth(i, UD, 0) && Znth(i, UD, 0) <= 2147483647)) &&
      store(&(s->vars), V) * IntArray::full(s->is_basic, V, IB) *
      simplex_scan_read_memory(s, Zrange(0, V), HL, HU, VN, VD, LN, LD, UN, UD) *
      simplex_enter_num_memory(s, row, V, CN) * undef_data_at(entering)
    Ensure exists e, simplex_find_entering_spec(IB, CN, HL, HU, VN, VD, LN, LD, UN, UD,
        D, V, __return, e) && store(&(((struct SxState *)S)->vars), V) *
      IntArray::full(((struct SxState *)S)->is_basic, V, IB) *
      simplex_scan_read_memory(((struct SxState *)S), Zrange(0, V), HL, HU, VN, VD, LN, LD, UN, UD) *
      simplex_enter_num_memory(((struct SxState *)S), R, V, CN) * data_at(((int *)O), int, e)
*/
;

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

/* Additive frameable interface independently proved in simplex_find_violation_preserve-20261103113604;
 * original separated_search retained. Resources outside the read slice require caller framing.
 */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_find_violation_preserve.simplex_find_violation_preserve_lib */

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
/*@ framed_search
 With (BAS : list Z) (HL : list Z) (HU : list Z) (VN : list Z) (VD : list Z) (LN : list Z) (LD : list Z) (UN : list Z) (UD : list Z) M V S P Q
 Require s == S && row == P && direction == Q &&
 0 <= M && M <= 16 && 0 <= V && V <= 24 &&
 (forall j, (0 <= j && j < M) => (0 <= Znth(j, BAS, 0) && Znth(j, BAS, 0) < V)) &&
 (forall j, (In(j, BAS) && (Znth(j, HL, 0) != 0 || Znth(j, HU, 0) != 0)) =>
    (-2147483648 <= Znth(j, VN, 0) && Znth(j, VN, 0) <= 2147483647 && 1 <= Znth(j, VD, 0) && Znth(j, VD, 0) <= 2147483647)) &&
 (forall j, (In(j, BAS) && Znth(j, HL, 0) != 0) =>
    (-2147483648 <= Znth(j, LN, 0) && Znth(j, LN, 0) <= 2147483647 && 1 <= Znth(j, LD, 0) && Znth(j, LD, 0) <= 2147483647)) &&
 (forall j, (In(j, BAS) && Znth(j, HU, 0) != 0) =>
    (-2147483648 <= Znth(j, UN, 0) && Znth(j, UN, 0) <= 2147483647 && 1 <= Znth(j, UD, 0) && Znth(j, UD, 0) <= 2147483647)) &&
 store(&(s->rows), M) * store(&(s->vars), V) *
 IntArray::full(s->basic, M, BAS) * simplex_scan_read_memory(s, BAS, HL, HU, VN, VD, LN, LD, UN, UD) *
 undef_data_at(row) * undef_data_at(direction)
 Ensure exists R D, simplex_find_violation_spec(BAS, HL, HU, VN, VD, LN, LD, UN, UD, V, M, __return, R, D) &&
 store(&(((struct SxState *)S)->rows), M) * store(&(((struct SxState *)S)->vars), V) *
 IntArray::full(((struct SxState *)S)->basic, M, BAS) * simplex_scan_read_memory(((struct SxState *)S), BAS, HL, HU, VN, VD, LN, LD, UN, UD) *
 data_at(((int *)P), int, R) * data_at(((int *)Q), int, D)
*/
;

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

/* ========================================================================
 * 14. sx_pivot — 受检有理数换基，精确失败前缀及成功方程等价
 * 来源：qcp/QCP_examples/Applications_human/simplex_pivot/sx_pivot.c
 * 验证运行：simplex_pivot-20261103051637；独立 final-check: done。
 * 38 top-level/23 split，10组，202个 suffixed helpers；所有必需路线通过。
 * 精确 rhs/a 更新顺序；失败保留已完成前缀，basic/is_basic 仅全部算术成功后提交。
 * 成功含实际 compute→closed→equiv 证明，不把抽象 residual iff 当成该证明。
 * 零枢轴入口保留；不要求 value/bounds/inputs 初始化，未知内存不冒充旧字节。
 * ======================================================================== */
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

/* ========================================================================
 * 15. sx_solve — bounded checked Simplex, exact state and rational soundness
 * Run simplex_solve-20261104112017; independent final-check done/passed/errors[].
 * 28 top-level +90 split spans,10 groups,15 new proved suffix helpers.
 * Original C body unchanged, including dynamic SxRat assignments.
 * Searches precede budget guard; partial Pivot/Recompute commits are preserved.
 * Fixed entrance A; FEASIBLE actual values witness rationals, UNSAT all rationals.
 * Review collection only, not a newly proved unified translation unit.
 * ======================================================================== */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_solve.simplex_solve_lib */
/*@ Extern Coq (simplex_solve_snapshot :: *) */
/*@ Extern Coq
 (simplex_solve_pack : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> simplex_solve_snapshot)
 (simplex_solve_normal : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> simplex_solve_snapshot -> Prop)
 (simplex_solve_origin : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> simplex_solve_snapshot -> Prop)
 (simplex_solve_result : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
 (simplex_solve_witness : list Z -> Z -> Z -> list Z -> list Z -> Prop)
 (simplex_solve_unsat : list Z -> Z -> Z -> Prop)
 (simplex_solve_variables : Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Assertion)
*/
int sx_solve(struct SxState *s, int pivot_limit)
/*@ negative_budget
 With L
 Require pivot_limit == L && -2147483648 <= L && L < 0
 Ensure __return == -1
*/
/*@ normal_state
 With S L M I V (A N D B IB HL HU LN LD UN UD VN VD : list Z)
 Require s == S && pivot_limit == L && 0 <= L && L <= 2147483647 &&
 0 <= M && M <= 16 && 0 <= I && I <= 8 && V == M+I && 0 <= V && V <= 24 &&
 Zlength(N) == 400 && Zlength(D) == 400 && Zlength(B) == M &&
 Zlength(IB) == V && Zlength(HL) == V && Zlength(HU) == V &&
 Zlength(LN) == V && Zlength(LD) == V && Zlength(UN) == V && Zlength(UD) == V &&
 Zlength(VN) == V && Zlength(VD) == V &&
 (forall (i: Z) (j: Z), (0 <= i && i < M && 0 <= j && j <= I) =>
   (-2147483647 <= Znth(i*9+j,A,0) && Znth(i*9+j,A,0) <= 2147483647)) &&
 simplex_solve_normal(A,HL,HU,LN,LD,UN,UD,M,I,simplex_solve_pack(N,D,B,IB,VN,VD)) &&
 simplex_solve_origin(A,HL,HU,LN,LD,UN,UD,M,I,simplex_solve_pack(N,D,B,IB,VN,VD)) &&
 store(&(s->rows),M) * store(&(s->vars),V) * store(&(s->inputs),I) *
 IntArray::full(s->basic,M,B) * IntArray::full(s->is_basic,V,IB) *
 simplex_pivot_memory(s,M,V,N,D) * simplex_solve_variables(s,V,HL,HU,VN,VD,LN,LD,UN,UD)
 Ensure exists ON OD OB OIB OVN OVD,
 (__return == -1 || __return == 0 || __return == 1) &&
 simplex_solve_result(HL,HU,LN,LD,UN,UD,M,V,L,N,D,B,IB,VN,VD,__return,ON,OD,OB,OIB,OVN,OVD) &&
 (__return != -1 =>
   (simplex_solve_normal(A,HL,HU,LN,LD,UN,UD,M,I,simplex_solve_pack(ON,OD,OB,OIB,OVN,OVD)) &&
    simplex_solve_origin(A,HL,HU,LN,LD,UN,UD,M,I,simplex_solve_pack(ON,OD,OB,OIB,OVN,OVD)))) &&
 (__return == 0 => simplex_solve_witness(A,M,I,OVN,OVD)) &&
 (__return == 1 => simplex_solve_unsat(A,M,I)) &&
 store(&(((struct SxState *)S)->rows),M) * store(&(((struct SxState *)S)->vars),V) *
 store(&(((struct SxState *)S)->inputs),I) *
 IntArray::full(((struct SxState *)S)->basic,M,OB) * IntArray::full(((struct SxState *)S)->is_basic,V,OIB) *
 simplex_pivot_memory(S,M,V,ON,OD) * simplex_solve_variables(S,V,HL,HU,OVN,OVD,LN,LD,UN,UD)
*/
;
