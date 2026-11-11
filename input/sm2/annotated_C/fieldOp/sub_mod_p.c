/* Verification copy of YCrypt/sm2/fieldOp.c::sub_mod_p. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ Import Coq Require Import
      SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement
 */

u1 portable_addcarryx_u64(u1 carry_in, u8 a, u8 b, u8* result)
/*@ Require
      0 <= carry_in && carry_in <= 1 &&
      0 <= a && a < U64_MOD &&
      0 <= b && b < U64_MOD &&
      has_permission(result)
    Ensure
      exists out,
        0 <= out && out < U64_MOD &&
        0 <= __return && __return <= 1 &&
        a + b + carry_in == out + __return * U64_MOD &&
        store(result, unsigned long long, out)
 */;

void sub_mod_p(const u32 *a, const u32 *b, u32 *result)
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
      store_fp(result, Zmod(A - B, SM2_P_Z)) *
      store_sm2_p
 */
/*@ r_eq_a
    With A B
    Require
      result == a &&
      store_fp(a, A) *
      store_fp(b, B) *
      store_sm2_p
    Ensure
      result == a &&
      store_fp(result, Zmod(A - B, SM2_P_Z)) *
      store_fp(b, B) *
      store_sm2_p
 */
/*@ r_eq_b
    With A B
    Require
      result == b &&
      store_fp(a, A) *
      store_fp(b, B) *
      store_sm2_p
    Ensure
      result == b &&
      store_fp(a, A) *
      store_fp(result, Zmod(A - B, SM2_P_Z)) *
      store_sm2_p
 */
;

void sub_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_non_alias <= non_alias
    With A B
    Require
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      store_fp(result, mont_p(A - B)) *
      store_sm2_p
 */
;

void sub_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_r_eq_b <= r_eq_b
    With A B
    Require
      result == b &&
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      store_sm2_p
    Ensure
      result == b &&
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(A - B)) *
      store_sm2_p
 */
;

void sub_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias */
/*@ r_eq_a */
/*@ r_eq_b */
{
	/*@ do open_store_fp */
	/*@ do open_store_u256 */
	/*@ do open_sm2_p */
	u1 carry = 1;
	// a - b (using two's complement)
	carry = portable_addcarryx_u64(carry, a->v[0], ~b->v[0], &result->v[0]);
	carry = portable_addcarryx_u64(carry, a->v[1], ~b->v[1], &result->v[1]);
	carry = portable_addcarryx_u64(carry, a->v[2], ~b->v[2], &result->v[2]);
	carry = portable_addcarryx_u64(carry, a->v[3], ~b->v[3], &result->v[3]);

	// If a - b < 0 (no carry), add P
	if (!carry) {
		carry = 0;
		carry = portable_addcarryx_u64(carry, result->v[0], SM2_P.v[0], &result->v[0]);
		carry = portable_addcarryx_u64(carry, result->v[1], SM2_P.v[1], &result->v[1]);
		carry = portable_addcarryx_u64(carry, result->v[2], SM2_P.v[2], &result->v[2]);
		carry = portable_addcarryx_u64(carry, result->v[3], SM2_P.v[3], &result->v[3]);
	}
}
