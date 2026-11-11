/* Verification copy of YCrypt/sm2/basicOp.c::sm2p_mong_mul. */

#include "../include/basicOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */

void raw_mul(const UINT64 a[4], const UINT64 b[4], UINT64 result[8])
/*@ With A B
    Require
      store_u256_limbs(a, A) *
      store_u256_limbs(b, B) *
      UInt64Array::undef_full(result, 8)
    Ensure
      0 <= A * B && A * B < U512_MOD &&
      store_u256_limbs(a, A) *
      store_u256_limbs(b, B) *
      store_u64_limbs(result, 8, A * B)
 */;

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
 */;

void sm2p_mong_mul(const u32* x, const u32* y, u32* result)
/*@ non_alias
    With X Y
    Require
      store_u256(x, X) *
      store_u256(y, Y) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * Y + K * SM2_P_Z &&
        store_u256(x, X) *
        store_u256(y, Y) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ r_eq_x
    With X Y
    Require
      result == x &&
      store_u256(x, X) *
      store_u256(y, Y) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        result == x &&
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * Y + K * SM2_P_Z &&
        store_fp(result, Zout) *
        store_u256(y, Y) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ r_eq_y
    With X Y
    Require
      result == y &&
      store_u256(x, X) *
      store_u256(y, Y) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        result == y &&
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * Y + K * SM2_P_Z &&
        store_u256(x, X) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ non_alias */
/*@ r_eq_x */
/*@ r_eq_y */
{
	/*@ do open_store_fp */
	u8 interim[9] = { 0 };
	raw_mul(x->v, y->v, interim);

	sm2p_mong_mul_core(interim, result);
	/*@ do normalize_u64_shape_base */
}
