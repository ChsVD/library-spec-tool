/* Verification copy of YCrypt/sm2/fieldOp.c::mul_mod_n. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */

bool u32_eq_one(const u32 *a)
/*@ With A
    Require
      store_u256(a, A)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == 1) ||
       (__return == 0 && A != 1)) &&
      store_u256(a, A)
 */;

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
 */;

void mul_mod_n(const u32* x, const u32* y, u32* result)
/*@ non_alias
    With X Y
    Require
      store_fn(x, X) *
      store_fn(y, Y) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_nh *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      store_fn(x, X) *
      store_fn(y, Y) *
      store_fn(result, Zmod(X * Y, SM2_N_Z)) *
      store_sm2_nh *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
 */
/*@ non_alias */
{
	if (u32_eq_one(x))
	{
		/*@ Assert
		      x == x@pre &&
		      y == y@pre &&
		      result == result@pre &&
		      X == 1 &&
		      store_fn(x, X) *
		      store_fn(y, Y) *
		      UndefStructPredu32(result) *
		      store_sm2_nh *
		      store_sm2_n *
		      store_sm2_rhon *
		      store_sm2_neg_inv_n
		 */
		/*@ do open_store_fn */
		/*@ do open_store_u256 */
		*result = *y;
		return;
	}
	if (u32_eq_one(y))
	{
		/*@ Assert
		      x == x@pre &&
		      y == y@pre &&
		      result == result@pre &&
		      X != 1 &&
		      Y == 1 &&
		      store_fn(x, X) *
		      store_fn(y, Y) *
		      UndefStructPredu32(result) *
		      store_sm2_nh *
		      store_sm2_n *
		      store_sm2_rhon *
		      store_sm2_neg_inv_n
		 */
		/*@ do open_store_fn */
		/*@ do open_store_u256 */
		*result = *x;
		return;
	}

	sm2n_mong_mul(x, y, result) /*@ where (non_alias) */;
	/*@ Given R K */
	/*@ do open_sm2_nh */
	sm2n_mong_mul(result, &SM2_NH, result)
	  /*@ where (r_eq_x) X = R, Y = SM2_NH_Z */;
}
