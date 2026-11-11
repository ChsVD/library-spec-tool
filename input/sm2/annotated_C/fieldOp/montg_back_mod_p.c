/* Verification copy of YCrypt/sm2/fieldOp.c::montg_back_mod_p. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */

void sm2p_mong_mul(const u32* x, const u32* y, u32* result)
/*@ non_alias
    With X Y
    Require
      store_u256(x, X) *
      store_u256(y, Y) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * Y + K * SM2_P_Z &&
        store_u256(x, X) *
        store_u256(y, Y) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ r_eq_x
    With X Y
    Require
      result == x &&
      store_u256(x, X) *
      store_u256(y, Y) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        result == x &&
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * Y + K * SM2_P_Z &&
        store_fp(result, Zout) *
        store_u256(y, Y) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void montg_back_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      store_u256(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == A + K * SM2_P_Z &&
        store_u256(a, A) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ in_place
    With A
    Require
      result == a &&
      store_u256(a, A) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        result == a &&
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == A + K * SM2_P_Z &&
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void montg_back_mod_p(const u32 *a, u32 *result)
/*@ regular_non_alias <= non_alias
    With A
    Require
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(result, A) *
      store_sm2_p *
      store_sm2_rhop
 */
;

void montg_back_mod_p(const u32 *a, u32 *result)
/*@ regular_in_place <= in_place
    With A
    Require
      result == a &&
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == a &&
      store_fp(result, A) *
      store_sm2_p *
      store_sm2_rhop
 */
;

void montg_back_mod_p(const u32 *a, u32 *result)
/*@ non_alias */
/*@ in_place */
{
	// result = a * 1 * R^(-1) mod P
	const u32 ONE = {{ 1, 0, 0, 0 }};
	sm2p_mong_mul(a, &ONE, result)
	/*@
	  where (non_alias) X = A_non_alias, Y = 1
	    $ non_alias
	  where (r_eq_x) X = A_in_place, Y = 1
	    $ in_place
	 */;
}
