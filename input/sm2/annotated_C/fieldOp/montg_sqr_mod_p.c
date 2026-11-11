/* Verification copy of YCrypt/sm2/fieldOp.c::montg_sqr_mod_p. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */

void sm2p_mong_pow(const u32* x, u32* result)
/*@ non_alias
    With X
    Require
      store_u256(x, X) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * X + K * SM2_P_Z &&
        store_u256(x, X) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ r_eq_x
    With X
    Require
      result == x &&
      store_u256(x, X) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * X + K * SM2_P_Z &&
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void montg_sqr_mod_p(const u32 *a, u32 *result)
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
        Zout * U256_MOD == A * A + K * SM2_P_Z &&
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
        Zout * U256_MOD == A * A + K * SM2_P_Z &&
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void montg_sqr_mod_p(const u32 *a, u32 *result)
/*@ mont_non_alias <= non_alias
    With A
    Require
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(A * A)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

void montg_sqr_mod_p(const u32 *a, u32 *result)
/*@ mont_in_place <= in_place
    With A
    Require
      result == a &&
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == a &&
      store_fp(result, mont_p(A * A)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

void montg_sqr_mod_p(const u32 *a, u32 *result)
/*@ non_alias */
/*@ in_place */
{
	sm2p_mong_pow(a, result)
	/*@
	  where (non_alias) X = A_non_alias
	    $ non_alias
	  where (r_eq_x) X = A_in_place
	    $ in_place
	 */;
}
