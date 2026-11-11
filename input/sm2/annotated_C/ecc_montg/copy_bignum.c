/*
 * Verification extraction of YCrypt/sm2/ecc_montg.c::copy_bignum.
 * Source baseline: be2f5161f972ebc063c7e35b84b129944b754fbc.
 */

#include "../include/ecc_memory.h"
#include "../include/ecc.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */

// Copy big number for 4 slob
static inline void copy_bignum(const UINT64* src, UINT64* dst)
/*@ raw
    With X
    Require
      store_u256_limbs(src, X) *
      UInt64Array::undef_full(dst, 4)
    Ensure
      store_u256_limbs(src, X) *
      store_u256_limbs(dst, X)
 */
;

static inline void copy_bignum(const UINT64* src, UINT64* dst)
/*@ field_non_alias <= raw
    With X PS PD
    Require
      src == PS && dst == PD &&
      0 <= X && X < SM2_P_Z &&
      store_fp(PS, X) * UInt64Array::undef_full(dst, 4)
    Ensure
      src == PS && dst == PD &&
      store_fp(PS, X) * store_fp(PD, X)
 */
;

static inline void copy_bignum(const UINT64* src, UINT64* dst)
/*@ raw */
{
	memcpy(dst, src, sizeof(UINT64) * 4);
}
