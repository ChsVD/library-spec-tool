/* Verification copy of YCrypt/sm2/basicOp.c::sm2p_mong_pow. */

#include "../include/basicOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */

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

void sm2p_mong_mul_core(UINT64 interim[9], u32* result)
/*@ With T
    Require
      0 <= T && T < U512_MOD &&
      store_u64_limbs(interim, 8, T) *
      store(interim + 8, unsigned long long, 0) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == T + K * SM2_P_Z &&
        UInt64Array::full_shape(interim, 9) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
;

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
/*@ non_alias */
/*@ r_eq_x */
{
	/*@ do open_store_fp */
	u8 interim[9] = { 0 };
	raw_pow(x->v, interim);

	sm2p_mong_mul_core(interim, result);
	/*@ do normalize_u64_shape_base */
}
