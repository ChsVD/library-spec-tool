/* Verification copy of YCrypt/sm2/fieldOp.c::double_mod_p. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */

u1 portable_addcarryx_u64(u1 carry_in, u8 a, u8 b, u8* result)
/*@ Require
      0 <= carry_in && carry_in <= 1 &&
      0 <= a && a < U64_MOD &&
      0 <= b && b < U64_MOD &&
      has_permission(result)
    Ensure
      exists out,
        0 <= out && out < U64_MOD &&
        0 <= __return && __return <= 1 &&
        a + b + carry_in == out + __return * U64_MOD &&
        store(result, unsigned long long, out)
 */;

// result = 2*a mod P
void double_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(result, Zmod(2 * A, SM2_P_Z)) *
      store_sm2_p
 */
/*@ non_alias */
{
	/*@ do open_store_fp */
	/*@ do open_store_u256 */
	/*@ do open_sm2_p */
	u32 tmp;
	// Left shift (multiply by 2) - capture the overflow carry
	u1 overflow = a->v[3] >> 63;  // High bit that will be shifted out
	tmp.v[3] = (a->v[3] << 1) | (a->v[2] >> 63);
	tmp.v[2] = (a->v[2] << 1) | (a->v[1] >> 63);
	tmp.v[1] = (a->v[1] << 1) | (a->v[0] >> 63);
	tmp.v[0] = a->v[0] << 1;

	// tmp - P (add ~P + 1, i.e., subtract P)
	u1 borrow = 1;
	borrow = portable_addcarryx_u64(borrow, tmp.v[0], ~SM2_P.v[0], &result->v[0]);
	borrow = portable_addcarryx_u64(borrow, tmp.v[1], ~SM2_P.v[1], &result->v[1]);
	borrow = portable_addcarryx_u64(borrow, tmp.v[2], ~SM2_P.v[2], &result->v[2]);
	borrow = portable_addcarryx_u64(borrow, tmp.v[3], ~SM2_P.v[3], &result->v[3]);

	// If overflow, the subtraction result is always correct
	// If no overflow and no borrow (tmp < P), use tmp instead
	if (!overflow && !borrow) {
		result->v[0] = tmp.v[0];
		result->v[1] = tmp.v[1];
		result->v[2] = tmp.v[2];
		result->v[3] = tmp.v[3];
	}
}
