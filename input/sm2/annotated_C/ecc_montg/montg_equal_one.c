/*
 * Verification extraction of YCrypt/sm2/ecc_montg.c::montg_equal_one.
 * Source baseline: be2f5161f972ebc063c7e35b84b129944b754fbc.
 */

#include "../include/ecc.h"
#include "../include/ecc_constants.h"
#include <stdbool.h>
/*@ include strategies "../strategy/sm2_representation.strategies" */

/*@ Import Coq Import Snaive_C_Rules */

// Test wether equal to montgomery one
static inline bool montg_equal_one(const UINT64 src[4])
/*@ raw
    With A
    Require
      store_u256_limbs(src, A) *
      store_montg_one
    Ensure
      ((__return == 1 && A == MONTG_ONE_Z) ||
       (__return == 0 && A != MONTG_ONE_Z)) &&
      store_u256_limbs(src, A) *
      store_montg_one
 */
;

static inline bool montg_equal_one(const UINT64 src[4])
/*@ field <= raw
    With A P
    Require
      src == P &&
      0 <= A && A < SM2_P_Z &&
      store_fp(P, A) * store_montg_one
    Ensure
      src == P &&
      ((__return == 1 && A == MONTG_ONE_Z) ||
       (__return == 0 && A != MONTG_ONE_Z)) &&
      store_fp(P, A) * store_montg_one
 */
;

static inline bool montg_equal_one(const UINT64 src[4])
/*@ raw */
{
	/*@ store_montg_one which implies store_u256_limbs(MONTG_ONE, MONTG_ONE_Z) */
	/*@ do open_store_u256 */
	const bool ret =
		(src[0] ^ MONTG_ONE[0]) |
		(src[1] ^ MONTG_ONE[1]) |
		(src[2] ^ MONTG_ONE[2]) |
		(src[3] ^ MONTG_ONE[3]);
	return !ret;
}
