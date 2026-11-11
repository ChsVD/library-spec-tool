/* Verification copy of YCrypt/sm2/fieldOp.c::mul_by_3_mod_p. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
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

void add_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias
    With A B
    Require
      store_fp(a, A) *
      store_fp(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(b, B) *
      store_fp(result, Zmod(A + B, SM2_P_Z)) *
      store_sm2_p
 */;

// result = 3*a mod P
void mul_by_3_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(result, Zmod(3 * A, SM2_P_Z)) *
      store_sm2_p
 */
/*@ in_place
    With A
    Require
      result == a &&
      store_fp(a, A) *
      store_sm2_p
    Ensure
      result == a &&
      store_fp(result, Zmod(3 * A, SM2_P_Z)) *
      store_sm2_p
 */
;

void mul_by_3_mod_p(const u32 *a, u32 *result)
/*@ mont_in_place <= in_place
    With A
    Require
      result == a &&
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_sm2_p
    Ensure
      result == a &&
      store_fp(result, mont_p(3 * A)) *
      store_sm2_p
 */
;

void mul_by_3_mod_p(const u32 *a, u32 *result)
/*@ non_alias */
/*@ in_place */
{
	/*@ do open_store_fp */
	/*@ do open_store_u256 */
	u32 tmp_a, tmp_2a;
	// Copy a in case result == a
	tmp_a = *a;

	// tmp_2a = 2*a mod P
	double_mod_p(&tmp_a, &tmp_2a) /*@ where (non_alias) */;

	// result = tmp_2a + a mod P
	add_mod_p(&tmp_2a, &tmp_a, result) /*@ where (non_alias) */;
}
