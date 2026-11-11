/* Verification copy of YCrypt/sm2/basicOp.c::portable_addcarryx_u64. */

#include "../include/basicOp.h"

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
 */
{
  u8 sum = a + b;
  u1 carry1 = (sum < a) ? 1 : 0;
  u8 sum2 = sum + carry_in;
  u1 carry2 = (sum2 < sum) ? 1 : 0;
  *result = sum2;
  return carry1 | carry2;
}
