/* Verification copy of YCrypt/sm2/basicOp.c::sm2n_mong_mul. */

#include "../include/basicOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/basicop_facts.strategies" */

void raw_mul(const UINT64 a[4], const UINT64 b[4], UINT64 result[8])
/*@ non_alias
    With A B
    Require
      store_u256_limbs(a, A) *
      store_u256_limbs(b, B) *
      UInt64Array::undef_full(result, 8)
    Ensure
      0 <= A * B && A * B < U512_MOD &&
      store_u256_limbs(a, A) *
      store_u256_limbs(b, B) *
      store_u64_limbs(result, 8, A * B)
 */
;

void sm2n_mong_mul_core(UINT64 interim[9], u32* result)
/*@ With T
    Require
      0 <= T && T < SM2_N_Z * U256_MOD &&
      store_u64_limbs(interim, 8, T) *
      store(interim + 8, unsigned long long, 0) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists R K,
        0 <= R && R < SM2_N_Z &&
        R * U256_MOD == T + K * SM2_N_Z &&
        UInt64Array::full_shape(interim, 9) *
        store_fn(result, R) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
;

void sm2n_mong_mul(const u32* x, const u32* y, u32* result)
/*@ non_alias
    With X Y
    Require
      store_fn(x, X) *
      store_fn(y, Y) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists R K,
        0 <= R && R < SM2_N_Z &&
        R * U256_MOD == X * Y + K * SM2_N_Z &&
        store_fn(x, X) *
        store_fn(y, Y) *
        store_fn(result, R) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
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
      exists R K,
        0 <= R && R < SM2_N_Z &&
        R * U256_MOD == X * Y + K * SM2_N_Z &&
        result == x &&
        store_fn(result, R) *
        store_fn(y, Y) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
/*@ non_alias */
/*@ r_eq_x */
{
	/*@ do open_store_fn */
	u8 interim[9] = { 0 };
	raw_mul(x->v, y->v, interim)
	/*@
	  where (non_alias)
	    A = X_non_alias, B = Y_non_alias
	    $ non_alias
	  where (non_alias)
	    A = X_r_eq_x, B = Y_r_eq_x
	    $ r_eq_x
	 */;

	/*@ do sm2n_mul_bound */
	sm2n_mong_mul_core(interim, result)
	/*@
	  where T = X_non_alias * Y_non_alias
	    $ non_alias
	  where T = X_r_eq_x * Y_r_eq_x
	    $ r_eq_x
	 */;
	/*@ do normalize_u64_shape_base */
}
