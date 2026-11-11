/* Verification copy of YCrypt/sm2/fieldOp.c::inv_for_mul_mod_n. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */

extern void montg_inv_mod_n_ex(const UINT64 a[4], UINT64 r[4])
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
;

void sm2n_mong_mul(const u32* x, const u32* y, u32* result)
/*@ r_eq_x
    With X Y
    Require
      result == x &&
      store_fn(x, X) *
      store_fn(y, Y) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists R K2,
        0 <= R && R < SM2_N_Z &&
        R * U256_MOD == X * Y + K2 * SM2_N_Z &&
        result == x &&
        store_fn(result, R) *
        store_fn(y, Y) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
;

void inv_for_mul_mod_n(const u32* input, u32* result)
/*@ non_alias
    With A
    Require
      A != 0 &&
      store_fn(input, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists Ainv,
        0 <= Ainv && Ainv < SM2_N_Z &&
        Zmod(A * Ainv, SM2_N_Z) == 1 &&
        store_fn(input, A) *
        store_fn(result, Ainv) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
/*@ in_place
    With A
    Require
      result == input &&
      A != 0 &&
      store_fn(input, A) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists Ainv,
        result == input &&
        0 <= Ainv && Ainv < SM2_N_Z &&
        Zmod(A * Ainv, SM2_N_Z) == 1 &&
        store_fn(result, Ainv) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
/*@ non_alias */
/*@ in_place */
{
	/*@ do open_store_fn */
	/*@ do open_store_u256 */
	const u32 ONE = { 1,0, 0, 0 };
	montg_inv_mod_n_ex(input->v, result->v)
	/*@
	  where (non_alias) A = A_non_alias
	    $ non_alias
	  where (in_place) A = A_in_place
	    $ in_place
	 */;
	/*@ Given Znon K1non $ non_alias */
	/*@ Given Zin K1in $ in_place */
	/*@ do open_store_u256 */
	sm2n_mong_mul(result, &ONE,result)
	/*@
	  where (r_eq_x) X = Znon, Y = 1
	    $ non_alias
	  where (r_eq_x) X = Zin, Y = 1
	    $ in_place
	 */;
	/*@ Given R K2 $ non_alias */
	/*@ Given R K2 $ in_place */
}
