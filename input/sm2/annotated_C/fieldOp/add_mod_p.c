/* Verification copy of YCrypt/sm2/fieldOp.c::add_mod_p. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/u32_alias.strategies" */
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
 */
/*@ a_eq_b
    With A
    Require
      a == b &&
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      a == b &&
      store_fp(a, A) *
      store_fp(result, Zmod(A + A, SM2_P_Z)) *
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
      store_fp(result, Zmod(A + B, SM2_P_Z)) *
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
      store_fp(result, Zmod(A + B, SM2_P_Z)) *
      store_sm2_p
 */
;

void add_mod_p(const u32 *a, const u32 *b, u32 *result)
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
      store_fp(result, mont_p(A + B)) *
      store_sm2_p
 */
;

void add_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias */
/*@ a_eq_b */
/*@ r_eq_a */
/*@ r_eq_b */
{
	/*@ do open_store_fp */
	/*@ do open_store_u256 */
	/*@ do open_sm2_p */
	u1 carry = 0;
	u32 tmp;
	/*@ UInt64Array::undef_full(&(tmp.v[0]), 4) */
	// a + b
	carry = portable_addcarryx_u64(carry, a->v[0], b->v[0], &tmp.v[0]);
	carry = portable_addcarryx_u64(carry, a->v[1], b->v[1], &tmp.v[1]);
	carry = portable_addcarryx_u64(carry, a->v[2], b->v[2], &tmp.v[2]);
	carry = portable_addcarryx_u64(carry, a->v[3], b->v[3], &tmp.v[3]);

	// tmp - P (using two's complement: tmp + (~P + 1) = tmp - P)
	u1 borrow = 1;
	borrow = portable_addcarryx_u64(borrow, tmp.v[0], ~SM2_P.v[0], &result->v[0]);
	borrow = portable_addcarryx_u64(borrow, tmp.v[1], ~SM2_P.v[1], &result->v[1]);
	borrow = portable_addcarryx_u64(borrow, tmp.v[2], ~SM2_P.v[2], &result->v[2]);
	borrow = portable_addcarryx_u64(borrow, tmp.v[3], ~SM2_P.v[3], &result->v[3]);

	// If (a + b) < P, use tmp; otherwise use result (which is tmp - P)
	// borrow == 0 means tmp < P, so we need to use tmp
	if (!(carry | borrow)) {
		result->v[0] = tmp.v[0];
		result->v[1] = tmp.v[1];
		result->v[2] = tmp.v[2];
		result->v[3] = tmp.v[3];
	}
	/*@ Assert
	      exists (limbs : list Z),
	        a == a@pre &&
	        b == b@pre &&
	        result == result@pre &&
	        Zlength(limbs) == 4 &&
	        u64_list_bounded(limbs) &&
	        u64_list_value(limbs) == Zmod(A_non_alias + B_non_alias, U256_MOD) &&
	        store_fp(a, A_non_alias) *
	        store_fp(b, B_non_alias) *
	        store_fp(result, Zmod(A_non_alias + B_non_alias, SM2_P_Z)) *
	        StructPredu32(&(tmp), make_record_u32(limbs)) *
	        store_sm2_p *
	        has_permission(&carry) *
	        has_permission(&borrow)
	        $ non_alias
	 */
	/*@ Assert
	      exists (limbs : list Z),
	        a == a@pre &&
	        b == b@pre &&
	        result == result@pre &&
	        a == b &&
	        Zlength(limbs) == 4 &&
	        u64_list_bounded(limbs) &&
	        u64_list_value(limbs) == Zmod(A_a_eq_b + A_a_eq_b, U256_MOD) &&
	        store_fp(a, A_a_eq_b) *
	        store_fp(result, Zmod(A_a_eq_b + A_a_eq_b, SM2_P_Z)) *
	        StructPredu32(&(tmp), make_record_u32(limbs)) *
	        store_sm2_p *
	        has_permission(&carry) *
	        has_permission(&borrow)
	        $ a_eq_b
	 */
	/*@ Assert
	      exists (limbs : list Z),
	        a == a@pre &&
	        b == b@pre &&
	        result == result@pre &&
	        result == a &&
	        Zlength(limbs) == 4 &&
	        u64_list_bounded(limbs) &&
	        u64_list_value(limbs) == Zmod(A_r_eq_a + B_r_eq_a, U256_MOD) &&
	        store_fp(result, Zmod(A_r_eq_a + B_r_eq_a, SM2_P_Z)) *
	        store_fp(b, B_r_eq_a) *
	        StructPredu32(&(tmp), make_record_u32(limbs)) *
	        store_sm2_p *
	        has_permission(&carry) *
	        has_permission(&borrow)
	        $ r_eq_a
	 */
	/*@ Assert
	      exists (limbs : list Z),
	        a == a@pre &&
	        b == b@pre &&
	        result == result@pre &&
	        result == b &&
	        Zlength(limbs) == 4 &&
	        u64_list_bounded(limbs) &&
	        u64_list_value(limbs) == Zmod(A_r_eq_b + B_r_eq_b, U256_MOD) &&
	        store_fp(a, A_r_eq_b) *
	        store_fp(result, Zmod(A_r_eq_b + B_r_eq_b, SM2_P_Z)) *
	        StructPredu32(&(tmp), make_record_u32(limbs)) *
	        store_sm2_p *
	        has_permission(&carry) *
	        has_permission(&borrow)
	        $ r_eq_b
	 */
}
