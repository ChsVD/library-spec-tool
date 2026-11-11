/*
 * Verification extraction of YCrypt/sm2/ecc_montg.c::montg_inv_mod_p_ex.
 * Source baseline: be2f5161f972ebc063c7e35b84b129944b754fbc.
 */

#include "../include/ecc.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/ecc_montg_helper_views.strategies" */

/*@ Import Coq Import Snaive_C_Rules */

void MontgInvModp(const u32 *a, u32 *result)
/*@ mont_non_alias
    With A
    Require
      A != 0 &&
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Ainv_non,
        0 <= Ainv_non && Ainv_non < SM2_P_Z &&
        Zmod(A * Ainv_non, SM2_P_Z) == 1 &&
        store_fp(a, A) *
        store_fp(result, mont_p(Ainv_non)) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ mont_in_place
    With A
    Require
      result == a &&
      A != 0 &&
      store_fp(a, A) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Ainv_in,
        result == a &&
        0 <= Ainv_in && Ainv_in < SM2_P_Z &&
        Zmod(A * Ainv_in, SM2_P_Z) == 1 &&
        store_fp(result, mont_p(Ainv_in)) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void montg_inv_mod_p_ex(const UINT64 a[4], UINT64 r[4])
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

void montg_inv_mod_p_ex(const UINT64 a[4], UINT64 r[4])
/*@ field_non_alias <= non_alias
    With A PA PR
    Require
      a == PA && r == PR &&
      0 <= A && A != 0 && A < SM2_P_Z &&
      store_fp(PA, A) * UInt64Array::undef_full(r, 4) *
      store_sm2_p * store_sm2_rhop
    Ensure
      exists ZI,
        a == PA && r == PR &&
        0 <= ZI && ZI < SM2_P_Z &&
        Zmod(A * ZI, SM2_P_Z) == 1 &&
        store_fp(PA, A) * store_fp(PR, mont_p(ZI)) *
        store_sm2_p * store_sm2_rhop
 */
;

// Perform inversion in montgomery domain (mod P)
void montg_inv_mod_p_ex(const UINT64 a[4], UINT64 r[4])
/*@ non_alias */
/*@ in_place */
{
	/*@ do raw_to_store_fp */
	/*@ do raw_undef_to_u32 */
	MontgInvModp((const u32*)a, (u32*)r)
	/*@
	  where (mont_non_alias) A = A_non_alias
	    $ non_alias
	  where (mont_in_place) A = A_in_place
	    $ in_place
	 */;
	/*@ Given Ainv_non $ non_alias */
	/*@ Given Ainv_in $ in_place */
	/*@ do store_fp_to_raw */
}
