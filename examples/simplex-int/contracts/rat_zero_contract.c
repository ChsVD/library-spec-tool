/* 接口片段：共享SxRat声明见simplex_function_contracts.c。 */
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
