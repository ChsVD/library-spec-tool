/*
 * Verification extraction of YCrypt/sm2/ecc_montg.c::montg_is_apoint_zero.
 * Source baseline: be2f5161f972ebc063c7e35b84b129944b754fbc.
 */

#include "../include/ecc.h"
#include "../include/ecc_constants.h"
#include <stdbool.h>
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_montg_helper_views.strategies" */

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
;

static inline bool montg_is_apoint_zero(const AFPoint* dst)
/*@ coords
    With X Y
    Require
      store_mont_afpoint_coords(dst, X, Y) *
      store_bn_zero
    Ensure
      ((__return == 1 && X == 0 && Y == 0) ||
       (__return == 0 && (X != 0 || Y != 0))) &&
      store_mont_afpoint_coords(dst, X, Y) *
      store_bn_zero
 */
;

static inline bool montg_is_apoint_zero(const AFPoint* dst)
/*@ point <= coords
    With (P : ec_point)
    Require
      store_mont_afpoint(dst, P) *
      store_bn_zero
    Ensure
      ((__return == 1 && P == ECInfinity) ||
       (__return == 0 && P != ECInfinity)) &&
      store_mont_afpoint(dst, P) *
      store_bn_zero
 */
;

// Whether this is a zero affine point
static inline bool montg_is_apoint_zero(const AFPoint* dst)
/*@ coords */
{
    // Affine zero point is represented as (0, 0)
    /*@ store_bn_zero which implies
          store_u256_limbs(BN_ZERO, 0) */
    /*@ do open_store_u256 */
    /*@ do open_mont_afpoint_coords */
    /*@ do open_afpoint_fields */
    /*@ do open_store_fp */
    if (!bignum_is_equal(dst->x.v, BN_ZERO)
        /*@ where (non_alias) A = mont_p(X), B = 0 */)
    {
        /*@ do close_store_u256_base0 */
        return false;
    }
    /*@ do close_store_u256_base0 */
    if (!bignum_is_equal(dst->y.v, BN_ZERO)
        /*@ where (non_alias) A = mont_p(Y), B = 0 */)
    {
        /*@ do close_store_u256_base0 */
        return false;
    }
    /*@ do close_store_u256_base0 */
    return true;
}
