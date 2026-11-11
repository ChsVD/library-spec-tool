/* Verification copy of YCrypt/sm2/basicOp.c::portable_mulx_u64. */

#include "../include/basicOp.h"

u8 portable_mulx_u64(u8 a, u8 b, u8* hi_ptr)
/*@ Require
      0 <= a && a < U64_MOD &&
      0 <= b && b < U64_MOD &&
      has_permission(hi_ptr)
    Ensure
      exists hi,
        0 <= __return && __return < U64_MOD &&
        0 <= hi && hi < U64_MOD &&
        a * b == __return + hi * U64_MOD &&
        store(hi_ptr, unsigned long long, hi)
 */
{
  u4 a_lo = (u4)a;
  u4 a_hi = (u4)(a >> 32);
  u4 b_lo = (u4)b;
  u4 b_hi = (u4)(b >> 32);

  u8 p0 = (u8)a_lo * b_lo;
  u8 p1 = (u8)a_lo * b_hi;
  u8 p2 = (u8)a_hi * b_lo;
  u8 p3 = (u8)a_hi * b_hi;

  u8 lo = p0;
  u8 hi = p3;

  u8 mid = p1 + p2;
  u1 mid_carry = (mid < p1) ? 1 : 0;

  u8 mid_lo = mid << 32;
  u8 mid_hi = (mid >> 32) + ((u8)mid_carry << 32);

  lo += mid_lo;
  u1 lo_carry = (lo < mid_lo) ? 1 : 0;
  hi += mid_hi + lo_carry;

  *hi_ptr = hi;
  return lo;
}
