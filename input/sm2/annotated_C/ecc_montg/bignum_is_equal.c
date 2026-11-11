/*
 * Verification extraction of YCrypt/sm2/ecc_montg.c::bignum_is_equal.
 * Source baseline: YCrypt/sm2/ecc_montg.c (2026-08-14 extraction).
 */

#include "../include/ecc.h"
#include <stdbool.h>
/*@ include strategies "../strategy/sm2_representation.strategies" */

// Test wether two number is equal
static inline bool bignum_is_equal(const UINT64 a[4], const UINT64 b[4])
/*@ non_alias
    With A B
    Require
      store_u256_limbs(a, A) *
      store_u256_limbs(b, B)
    Ensure
      ((__return == 1 && A == B) ||
       (__return == 0 && A != B)) &&
      store_u256_limbs(a, A) *
      store_u256_limbs(b, B)
 */
/*@ non_alias */
{
	/*@ do open_store_u256 */
	const bool ret =
		(a[0] ^ b[0]) |
		(a[1] ^ b[1]) |
		(a[2] ^ b[2]) |
		(a[3] ^ b[3]);
	return !ret;
}
