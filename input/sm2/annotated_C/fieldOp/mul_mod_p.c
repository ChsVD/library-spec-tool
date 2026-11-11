/* Verification copy of YCrypt/sm2/fieldOp.c::mul_mod_p. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/u32_alias.strategies" */

bool u32_eq_one(const u32* a)
/*@ With (A : Z)
    Require
      store_u256(a, A)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == 1) ||
       (__return == 0 && A != 1)) &&
      store_u256(a, A)
 */
;

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
/*@ a_eq_b
    With A
    Require
      a == b &&
      store_u256_limbs(a, A) *
      UInt64Array::undef_full(result, 8)
    Ensure
      a == b &&
      0 <= A * A && A * A < U512_MOD &&
      store_u256_limbs(a, A) *
      store_u64_limbs(result, 8, A * A)
 */
;

void solinas_reduce(const u8 input[8], u32* result)
/*@ non_alias
    With T
    Require
      0 <= T && T < U512_MOD &&
      store_u64_limbs(input, 8, T) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        T == Zout + K * SM2_P_Z &&
        store_u64_limbs(input, 8, T) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void mul_mod_p(const u32* x, const u32* y, u32* result)
/*@ non_alias
    With X Y
    Require
      store_fp(x, X) *
      store_fp(y, Y) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(x, X) *
      store_fp(y, Y) *
      store_fp(result, Zmod(X * Y, SM2_P_Z)) *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ x_eq_y
    With X
    Require
      x == y &&
      store_fp(x, X) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      x == y &&
      store_fp(x, X) *
      store_fp(result, Zmod(X * X, SM2_P_Z)) *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ r_eq_x
    With X Y
    Require
      result == x &&
      store_fp(x, X) *
      store_fp(y, Y) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == x &&
      store_fp(result, Zmod(X * Y, SM2_P_Z)) *
      store_fp(y, Y) *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ r_eq_y
    With X Y
    Require
      result == y &&
      store_fp(x, X) *
      store_fp(y, Y) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == y &&
      store_fp(x, X) *
      store_fp(result, Zmod(X * Y, SM2_P_Z)) *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ non_alias */
/*@ x_eq_y */
/*@ r_eq_x */
/*@ r_eq_y */
{
#ifdef MONG
	if (u32_eq_one(x))
	{
		/*@ do open_store_fp */
		/*@ do open_store_u256 */
		*result = *y;
		return;
	}
	if (u32_eq_one(y))
	{
		/*@ do open_store_fp */
		/*@ do open_store_u256 */
		*result = *x;
		return;
	}

	// Non-standard use of montgomery multiplication
	montg_mul_mod_p(x->v, y->v, result->v);
	montg_mul_mod_p(result->v, SM2_H.v, result->v);
#else
	u8 res[8];
	if (u32_eq_one(x))
	{
		/*@ Assert
		      x == x@pre &&
		      y == y@pre &&
		      result == result@pre &&
		      X_non_alias == 1 &&
		      store_fp(x, X_non_alias) *
		      store_fp(y, Y_non_alias) *
		      UndefStructPredu32(result) *
		      UInt64Array::undef_full(res, 8) *
		      store_sm2_p *
		      store_sm2_rhop
		      $ non_alias
		 */
		/*@ Assert
		      x == x@pre &&
		      y == y@pre &&
		      result == result@pre &&
		      x == y &&
		      X_x_eq_y == 1 &&
			      store_fp(y, X_x_eq_y) *
		      UndefStructPredu32(result) *
		      UInt64Array::undef_full(res, 8) *
		      store_sm2_p *
		      store_sm2_rhop
		      $ x_eq_y
		 */
		/*@ Assert
		      x == x@pre &&
		      y == y@pre &&
		      result == result@pre &&
		      result == x &&
		      X_r_eq_x == 1 &&
		      store_fp(y, Y_r_eq_x) *
		      UndefStructPredu32(result) *
		      UInt64Array::undef_full(res, 8) *
		      store_sm2_p *
		      store_sm2_rhop
		      $ r_eq_x
		 */
		/*@ Assert
		      exists (limbs : list Z),
		        x == x@pre &&
		        y == y@pre &&
		        result == result@pre &&
		        result == y &&
		        X_r_eq_y == 1 &&
		        0 <= Y_r_eq_y && Y_r_eq_y < SM2_P_Z &&
		        Zlength(limbs) == 4 &&
		        u64_list_bounded(limbs) &&
		        u64_list_value(limbs) == Y_r_eq_y &&
		        store_fp(x, X_r_eq_y) *
		        StructPredu32(result, make_record_u32(limbs)) *
		        UInt64Array::undef_full(res, 8) *
		        store_sm2_p *
		        store_sm2_rhop
		        $ r_eq_y
		 */
		/*@ do open_store_fp */
		/*@ do open_store_u256 */
		*result = *y;
		return;
	}
	/*@ do open_store_fp */
	/*@ do open_store_u256 */
	if (u32_eq_one(y))
	{
		/*@ Assert
		      x == x@pre &&
		      y == y@pre &&
		      result == result@pre &&
		      X_non_alias != 1 &&
		      Y_non_alias == 1 &&
		      store_fp(x, X_non_alias) *
		      store_fp(y, Y_non_alias) *
		      UndefStructPredu32(result) *
		      UInt64Array::undef_full(res, 8) *
		      store_sm2_p *
		      store_sm2_rhop
		      $ non_alias
		 */
		/*@ Assert
		      exists (limbs : list Z),
		        x == x@pre &&
		        y == y@pre &&
		        result == result@pre &&
		        result == x &&
		        X_r_eq_x != 1 &&
		        Y_r_eq_x == 1 &&
		        0 <= X_r_eq_x && X_r_eq_x < SM2_P_Z &&
		        Zlength(limbs) == 4 &&
		        u64_list_bounded(limbs) &&
		        u64_list_value(limbs) == X_r_eq_x &&
		        StructPredu32(result, make_record_u32(limbs)) *
		        store_fp(y, Y_r_eq_x) *
		        UInt64Array::undef_full(res, 8) *
		        store_sm2_p *
		        store_sm2_rhop
		        $ r_eq_x
		 */
		/*@ Assert
		      x == x@pre &&
		      y == y@pre &&
		      result == result@pre &&
		      result == y &&
		      X_r_eq_y != 1 &&
		      Y_r_eq_y == 1 &&
		      store_fp(x, X_r_eq_y) *
		      UndefStructPredu32(result) *
		      UInt64Array::undef_full(res, 8) *
		      store_sm2_p *
		      store_sm2_rhop
		      $ r_eq_y
		 */
		/*@ do open_store_fp */
		/*@ do open_store_u256 */
		*result = *x;
		return;
	}
	raw_mul(x->v, y->v, res)
	/*@
	  where (non_alias)
	    A = X_non_alias, B = Y_non_alias
	    $ non_alias
	  where (a_eq_b)
	    A = X_x_eq_y
	    $ x_eq_y
	  where (non_alias)
	    A = X_r_eq_x, B = Y_r_eq_x
	    $ r_eq_x
	  where (non_alias)
	    A = X_r_eq_y, B = Y_r_eq_y
	    $ r_eq_y
	 */;
	solinas_reduce(res, result);
	/*@ do open_store_u64_limbs */
#endif
}
