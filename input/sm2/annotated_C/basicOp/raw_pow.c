#include "../include/basicOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/raw_pow_arrays.strategies" */

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
 */;

// 256-bit squaring: result[8] = a[4] * a[4]
// Optimized by computing off-diagonal terms once and doubling
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
{
	/*@ do open_store_u256 */
	u8 h, l;
	u1 carry, carry2 = 0;
	result[2] = 0;
	result[1] = 0;
	result[0] = 0;

	// Square term: add a[i]*a[i] directly
#define SQR_ACC(i) \
	l = portable_mulx_u64(a[i], a[i], &h); \
	carry = portable_addcarryx_u64(0, result[(i)*2], l, &result[(i)*2]); \
	carry2 += portable_addcarryx_u64(carry, result[(i)*2+1], h, &result[(i)*2+1])

	// Cross term: add 2*a[i]*a[j] (where i < j)
#define MUL2_ACC(i, j) \
	l = portable_mulx_u64(a[i], a[j], &h); \
	carry = portable_addcarryx_u64(0, result[(i)+(j)], (l << 1), &result[(i)+(j)]); \
	carry2 += portable_addcarryx_u64(carry, result[(i)+(j)+1], (h << 1) | (l >> 63), &result[(i)+(j)+1]); \
	carry2 += (h >> 63)

	// result[0]: a[0]^2
	SQR_ACC(0);  // carry2 must remain 0 here

	// result[1]: 2*a[0]*a[1]
	MUL2_ACC(0, 1);
	result[3] = carry2; carry2 = 0;

	// result[2]: a[1]^2 + 2*a[0]*a[2]
	SQR_ACC(1);
	MUL2_ACC(0, 2);
	result[4] = carry2; carry2 = 0;

	// result[3]: 2*a[0]*a[3] + 2*a[1]*a[2]
	MUL2_ACC(0, 3);
	MUL2_ACC(1, 2);
	result[5] = carry2; carry2 = 0;

	// result[4]: a[2]^2 + 2*a[1]*a[3]
	SQR_ACC(2);
	MUL2_ACC(1, 3);
	result[6] = carry2; carry2 = 0;

	// result[5]: 2*a[2]*a[3]
	MUL2_ACC(2, 3);
	result[7] = carry2;  // carry2 becomes the initial value for result[7]

	// result[6], result[7]: a[3]^2
	SQR_ACC(3);

#undef SQR_ACC
#undef MUL2_ACC
}
