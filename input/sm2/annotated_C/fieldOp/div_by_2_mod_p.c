/* Verification copy of YCrypt/sm2/fieldOp.c::div_by_2_mod_p. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
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

// result = a / 2 mod P
void div_by_2_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      result != a &&
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(result, fp_div2(A)) *
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
      store_fp(result, fp_div2(A)) *
      store_sm2_p
 */
;

void div_by_2_mod_p(const u32 *a, u32 *result)
/*@ mont_non_alias <= non_alias
    With A
    Require
      result != a &&
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(fp_div2(A))) *
      store_sm2_p
 */
;

void div_by_2_mod_p(const u32 *a, u32 *result)
/*@ non_alias */
/*@ in_place */
{
	/*@ do open_store_fp */
	/*@ do open_store_u256 */
	/*@ do open_sm2_p */
	u32 tmp;
	// Copy a in case result == a
	tmp = *a;

	// If a is odd, add P first
	if (tmp.v[0] & 1) {
		u1 carry = 0;
		carry = portable_addcarryx_u64(carry, tmp.v[0], SM2_P.v[0], &tmp.v[0]);
		carry = portable_addcarryx_u64(carry, tmp.v[1], SM2_P.v[1], &tmp.v[1]);
		carry = portable_addcarryx_u64(carry, tmp.v[2], SM2_P.v[2], &tmp.v[2]);
		carry = portable_addcarryx_u64(carry, tmp.v[3], SM2_P.v[3], &tmp.v[3]);
		/*@ Assert
		      exists T C,
		      0 <= T && T < U256_MOD &&
		      0 <= C && C <= 1 &&
			      a == a@pre &&
			      result == result@pre &&
			      fp_div2_adjusted(A_non_alias) == T + C * U256_MOD &&
			      store_u256(&tmp, T) *
			      store(&carry, unsigned char, C) *
			      store_fp(a, A_non_alias) *
		      UInt64Array::undef_full(&(result->v[0]), 4) *
		      store_sm2_p
		      $ non_alias
		 */
		/*@ Assert
		      exists T C,
		      result == a &&
		      0 <= T && T < U256_MOD &&
		      0 <= C && C <= 1 &&
			      a == a@pre &&
			      result == result@pre &&
			      fp_div2_adjusted(A_in_place) == T + C * U256_MOD &&
			      store_u256(&tmp, T) *
			      store(&carry, unsigned char, C) *
			      store_fp(result, A_in_place) *
		      store_sm2_p
			      $ in_place
		 */
		/*@ do open_store_fp */
		/*@ do open_store_u256 */
		// Note: carry here would go to bit 256, but we shift right so it becomes bit 255
		// Since P is odd and a < P, (a + P) fits in 257 bits, right shift gives 256 bits
		if (carry) {
			// The carry bit becomes the MSB after right shift
			result->v[0] = (tmp.v[0] >> 1) | (tmp.v[1] << 63);
			result->v[1] = (tmp.v[1] >> 1) | (tmp.v[2] << 63);
			result->v[2] = (tmp.v[2] >> 1) | (tmp.v[3] << 63);
			result->v[3] = (tmp.v[3] >> 1) | ((u8)1 << 63);
			return;
		}
	}

	// Right shift by 1
	/*@ do open_u64_array4 */
	result->v[0] = (tmp.v[0] >> 1) | (tmp.v[1] << 63);
	result->v[1] = (tmp.v[1] >> 1) | (tmp.v[2] << 63);
	result->v[2] = (tmp.v[2] >> 1) | (tmp.v[3] << 63);
	result->v[3] = tmp.v[3] >> 1;
}
