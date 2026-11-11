/* Verification copy of YCrypt/sm2/fieldOp.c::montg_to_mod_p. */

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
;

void montg_to_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      store_u256(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == A * SM2_H_Z + K * SM2_P_Z &&
        store_u256(a, A) *
        store_fp(result, Zout) *
        store_sm2_h *
        store_sm2_p *
        store_sm2_rhop
 */
;

void montg_to_mod_p(const u32 *a, u32 *result)
/*@ mont_non_alias <= non_alias
    With A
    Require
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(a, A) *
      store_fp(result, mont_p(A)) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop
 */
;

void montg_to_mod_p(const u32 *a, u32 *result)
/*@ non_alias */
{
	// result = a * H mod P, where H = R^2 mod P = 2^512 mod P
	/*@ do open_sm2_h */
	sm2p_mong_mul(a, &SM2_H, result)
	/*@
	  where (non_alias) X = A_non_alias, Y = SM2_H_Z
	    $ non_alias
	 */;
}
