/* Verification copy of YCrypt/sm2/basicOp.c::u32_add. */

#include "../include/basicOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */

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

u1 u32_add(const u32* a, const u32* b, u32* result)
/*@ non_alias
    With A B
    Require
      store_u256(a, A) *
      store_u256(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4)
    Ensure
      exists S,
        0 <= S && S < U256_MOD &&
        0 <= __return && __return <= 1 &&
        A + B == S + __return * U256_MOD &&
        store_u256(a, A) *
        store_u256(b, B) *
        store_u256(result, S)
 */
/*@ r_eq_a
    With A B
    Require
      result == a &&
      store_u256(a, A) *
      store_u256(b, B)
    Ensure
      exists S,
        0 <= S && S < U256_MOD &&
        0 <= __return && __return <= 1 &&
        A + B == S + __return * U256_MOD &&
        result == a &&
        store_u256(result, S) *
        store_u256(b, B)
 */
/*@ r_eq_b
    With A B
    Require
      result == b &&
      store_u256(a, A) *
      store_u256(b, B)
    Ensure
      exists S,
        0 <= S && S < U256_MOD &&
        0 <= __return && __return <= 1 &&
        A + B == S + __return * U256_MOD &&
        result == b &&
        store_u256(a, A) *
        store_u256(result, S)
 */
/*@ non_alias */
/*@ r_eq_a */
/*@ r_eq_b */
{
	/*@ do open_store_u256 */
  u1 carry = 0;
  carry = portable_addcarryx_u64(carry, a->v[0], b->v[0], &result->v[0]);
  carry = portable_addcarryx_u64(carry, a->v[1], b->v[1], &result->v[1]);
  carry = portable_addcarryx_u64(carry, a->v[2], b->v[2], &result->v[2]);
  carry = portable_addcarryx_u64(carry, a->v[3], b->v[3], &result->v[3]);
  return carry;
}
