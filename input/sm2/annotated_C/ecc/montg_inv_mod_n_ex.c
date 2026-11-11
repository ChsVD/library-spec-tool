/* Verification copy of YCrypt/sm2/ecc_montg.c::montg_inv_mod_n_ex. */

#include "../include/ecc.h"
#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/ecc_montg_helper_views.strategies" */

void MontgInvModn(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      A != 0 &&
      store_fn(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists z_call_non k_call_non,
        0 <= z_call_non && z_call_non < SM2_N_Z &&
        A * z_call_non == U256_MOD + k_call_non * SM2_N_Z &&
        store_fn(a, A) *
        store_fn(result, z_call_non) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
/*@ in_place
    With A
    Require
      result == a &&
      A != 0 &&
      store_fn(a, A) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists z_call_in k_call_in,
        result == a &&
        0 <= z_call_in && z_call_in < SM2_N_Z &&
        A * z_call_in == U256_MOD + k_call_in * SM2_N_Z &&
        store_fn(result, z_call_in) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
;

void montg_inv_mod_n_ex(const UINT64 a[4], UINT64 r[4])
/*@ non_alias
    With A
    Require
      A != 0 && A < SM2_N_Z &&
      store_u256_limbs(a, A) *
      UInt64Array::undef_full(r, 4) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists Znon K1non,
        0 <= Znon && Znon < SM2_N_Z &&
        A * Znon == U256_MOD + K1non * SM2_N_Z &&
        store_u256_limbs(a, A) *
        store_u256_limbs(r, Znon) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
/*@ in_place
    With A
    Require
      r == a &&
      A != 0 && A < SM2_N_Z &&
      store_u256_limbs(a, A) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists Zin K1in,
        r == a &&
        0 <= Zin && Zin < SM2_N_Z &&
        A * Zin == U256_MOD + K1in * SM2_N_Z &&
        store_u256_limbs(r, Zin) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
/*@ non_alias */
/*@ in_place */
{
	/*@ do raw_to_store_fn */
	/*@ do raw_undef_to_u32 */
	MontgInvModn((const u32*)a, (u32*)r)
	/*@
	  where (non_alias) A = A_non_alias
	    $ non_alias
	  where (in_place) A = A_in_place
	    $ in_place
	 */;
	/*@ Given z_call_non k_call_non $ non_alias */
	/*@ Given z_call_in k_call_in $ in_place */
	/*@ do store_fn_to_raw */
}
