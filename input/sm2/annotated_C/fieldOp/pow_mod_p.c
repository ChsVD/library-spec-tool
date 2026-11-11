/* Verification copy of YCrypt/sm2/fieldOp.c::pow_mod_p. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */

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

void raw_pow(const UINT64 a[4], UINT64 result[8])
/*@ With A
    Require
      store_u256_limbs(a, A) *
      UInt64Array::undef_full(result, 8)
    Ensure
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

//#define MONG
void pow_mod_p(const u32* x, u32* result)
/*@ non_alias
    With X
    Require
      store_fp(x, X) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(x, X) *
      store_fp(result, Zmod(X * X, SM2_P_Z)) *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ non_alias */
{
#ifdef MONG
	if (u32_eq_one(x))
	{
		/*@ do open_store_fp */
		/*@ do open_store_u256 */
		*result = *x;
		return;
	}

	// Non-standard use of montgomery multiplication
	montg_sqr_mod_p(x, result);
	montg_mul_mod_p(result, &SM2_H, result);
#else
	u8 res[8];
	if (u32_eq_one(x))
	{
		/*@ Assert
		      x == x@pre &&
		      result == result@pre &&
		      X == 1 &&
		      store_fp(x, X) *
		      UndefStructPredu32(result) *
		      UInt64Array::undef_full(res, 8) *
		      store_sm2_p *
		      store_sm2_rhop
		 */
		/*@ do open_store_fp */
		/*@ do open_store_u256 */
		*result = *x;
		return;
	}
	raw_pow(x->v, res);
	solinas_reduce(res, result);
	/*@ do open_store_u64_limbs */
#endif
}
