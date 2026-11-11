/* Verification copy of YCrypt/sm2/fieldOp.c::mul_by_2_mod_p. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ Import Coq Require Import
      SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement
 */

void double_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(result, Zmod(2 * A, SM2_P_Z)) *
      store_sm2_p
 */;

// result = 2*a mod P (alias for double_mod_p)
void mul_by_2_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(result, Zmod(2 * A, SM2_P_Z)) *
      store_sm2_p
 */
;

void mul_by_2_mod_p(const u32 *a, u32 *result)
/*@ mont_non_alias <= non_alias
    With A
    Require
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(2 * A)) *
      store_sm2_p
 */
;

void mul_by_2_mod_p(const u32 *a, u32 *result)
/*@ non_alias */
{
	double_mod_p(a, result) /*@ where (non_alias) */;
}
