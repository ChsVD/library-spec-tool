/* Verification copy of YCrypt/sm2/fieldOp.c::inv_for_mul_mod_p. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */

extern void montg_inv_mod_p_ex(const UINT64 a[4], UINT64 r[4])
/*@ non_alias
    With A
    Require
      A != 0 && A < SM2_P_Z &&
      store_u256_limbs(a, A) *
      UInt64Array::undef_full(r, 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Ainv_non,
        0 <= Ainv_non && Ainv_non < SM2_P_Z &&
        Zmod(A * Ainv_non, SM2_P_Z) == 1 &&
        store_u256_limbs(a, A) *
        store_u256_limbs(r, mont_p(Ainv_non)) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ in_place
    With A
    Require
      r == a &&
      A != 0 && A < SM2_P_Z &&
      store_u256_limbs(a, A) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Ainv_in,
        r == a &&
        0 <= Ainv_in && Ainv_in < SM2_P_Z &&
        Zmod(A * Ainv_in, SM2_P_Z) == 1 &&
        store_u256_limbs(r, mont_p(Ainv_in)) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void montg_back_mod_p(const u32 *a, u32 *result)
/*@ regular_in_place
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

void inv_for_mul_mod_p(const u32* input, u32* result)
/*@ non_alias
    With A
    Require
      A != 0 &&
      store_fp(input, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Ainv,
        0 <= Ainv && Ainv < SM2_P_Z &&
        Zmod(A * Ainv, SM2_P_Z) == 1 &&
        store_fp(input, A) *
        store_fp(result, Ainv) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ in_place
    With A
    Require
      result == input &&
      A != 0 &&
      store_fp(input, A) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Ainv,
        result == input &&
        0 <= Ainv && Ainv < SM2_P_Z &&
        Zmod(A * Ainv, SM2_P_Z) == 1 &&
        store_fp(result, Ainv) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ non_alias */
/*@ in_place */
{
	/*@ do open_store_fp */
	/*@ do open_store_u256 */
	montg_inv_mod_p_ex(input->v, result->v)
	/*@
	  where (non_alias) A = A_non_alias
	    $ non_alias
	  where (in_place) A = A_in_place
	    $ in_place
	 */;
	/*@ Given Ainv_non $ non_alias */
	/*@ Given Ainv_in $ in_place */
	/*@ do open_store_u256 */
	montg_back_mod_p(result, result)
	/*@
	  where (regular_in_place) A = Ainv_non
	    $ non_alias
	  where (regular_in_place) A = Ainv_in
	    $ in_place
	 */;
}
