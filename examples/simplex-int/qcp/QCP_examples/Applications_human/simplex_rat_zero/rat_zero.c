/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_rat_zero.simplex_rat_zero_lib */

struct SxRat { int num; int den; };

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
  /*@ out_undef */
  /*@ out_known */
{ r->num = 0; r->den = 1; }
