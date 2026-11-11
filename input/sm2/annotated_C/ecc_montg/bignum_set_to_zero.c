/*
 * Verification extraction of YCrypt/sm2/ecc_montg.c::bignum_set_to_zero.
 * Source baseline: be2f5161f972ebc063c7e35b84b129944b754fbc.
 */

#include "../include/ecc.h"
#include "../include/ecc_constants.h"
#include "../include/ecc_memory.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */

// Set a big number to zero
static inline void bignum_set_to_zero(UINT64 a[4])
/*@ raw
    Require
      UInt64Array::undef_full(a, 4)
    Ensure
      store_u256_limbs(a, 0)
 */
;

static inline void bignum_set_to_zero(UINT64 a[4])
/*@ field <= raw
    With P
    Require
      a == P && UInt64Array::undef_full(a, 4)
    Ensure
      a == P && store_fp(P, 0)
 */
;

static inline void bignum_set_to_zero(UINT64 a[4])
/*@ raw */
{
	memset(a, 0, sizeof(BN_ZERO));
}
