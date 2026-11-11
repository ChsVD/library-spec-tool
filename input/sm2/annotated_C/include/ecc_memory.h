#ifndef ECC_MEMORY_H
#define ECC_MEMORY_H

#include "dataType.h"

/*
 * Verification models for the two fixed-size libc operations used by the
 * ECC helpers.  Separation of the source and destination resources supplies
 * memcpy's non-overlap requirement for the complete four-limb regions.
 */

UINT64* memcpy(UINT64* dest, const UINT64* src, size_t n)
/*@ u256_limbs
    With X
    Require
      n == 32 &&
      store_u256_limbs(src, X) *
      UInt64Array::undef_full(dest, 4)
    Ensure
      __return == dest &&
      store_u256_limbs(src, X) *
      store_u256_limbs(dest, X)
 */
;

UINT64* memset(UINT64* dest, int c, size_t n)
/*@ zero_u256_limbs
    Require
      c == 0 && n == 32 &&
      UInt64Array::undef_full(dest, 4)
    Ensure
      __return == dest &&
      store_u256_limbs(dest, 0)
 */
;

#endif
