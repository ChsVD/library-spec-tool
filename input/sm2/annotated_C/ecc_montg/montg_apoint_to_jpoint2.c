/*
 * Verification extraction of YCrypt/sm2/ecc_montg.c::montg_apoint_to_jpoint2.
 * Source baseline: be2f5161f972ebc063c7e35b84b129944b754fbc.
 */

#include "../include/ecc.h"
#include "../include/ecc_constants.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/u32_alias.strategies" */
/*@ include strategies "../strategy/ecc_montg_helper_views.strategies" */

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

static inline void montg_set_jpoint_to_zero(JPoint* dst)
/*@ coords
    Require
      store_montg_one *
      UInt64Array::undef_full(&(dst->x.v[0]), 4) *
      UInt64Array::undef_full(&(dst->y.v[0]), 4) *
      UInt64Array::undef_full(&(dst->z.v[0]), 4)
    Ensure
      store_montg_one *
      store_mont_jpoint_coords(dst, 1, 1, 0)
 */
;

static inline void copy_bignum(const UINT64* src, UINT64* dst)
/*@
    With X
    Require
      store_u256_limbs(src, X) *
      UInt64Array::undef_full(dst, 4)
    Ensure
      store_u256_limbs(src, X) *
      store_u256_limbs(dst, X)
 */
;

int montg_apoint_to_jpoint2(const AFPoint* a, JPoint* r)
/*@ non_alias
    With AX AY
    Require
      store_mont_afpoint_coords(a, AX, AY) *
      UInt64Array::undef_full(&(r->x.v[0]), 4) *
      UInt64Array::undef_full(&(r->y.v[0]), 4) *
      UInt64Array::undef_full(&(r->z.v[0]), 4) *
      store_bn_zero *
      store_montg_one
    Ensure
      exists RX RY RZ,
        __return == 1 &&
        ((AX == 0 && AY == 0 &&
          RX == 1 && RY == 1 && RZ == 0) ||
         ((AX != 0 || AY != 0) &&
          RX == AX && RY == AY && RZ == 1)) &&
        store_mont_afpoint_coords(a, AX, AY) *
        store_mont_jpoint_coords(r, RX, RY, RZ) *
        store_bn_zero *
        store_montg_one
 */
;

int montg_apoint_to_jpoint2(const AFPoint* a, JPoint* r)
/*@ point_non_alias <= non_alias
    With (P : ec_point)
    Require
      store_mont_afpoint(a, P) *
      UInt64Array::undef_full(&(r->x.v[0]), 4) *
      UInt64Array::undef_full(&(r->y.v[0]), 4) *
      UInt64Array::undef_full(&(r->z.v[0]), 4) *
      store_bn_zero *
      store_montg_one
    Ensure
      __return == 1 &&
      store_mont_afpoint(a, P) *
      store_mont_jpoint(r, P) *
      store_bn_zero *
      store_montg_one
 */
;

// Convert affine point (montgomery domain) to jacobian point (montgomery domain)
int montg_apoint_to_jpoint2(const AFPoint* a, JPoint* r)
/*@ non_alias */
{
	const UINT64* ax = a->x.v;
	const UINT64* ay = a->y.v;
	const UINT64* az = MONTG_ONE;
	UINT64* rx = r->x.v;
	UINT64* ry = r->y.v;
	UINT64* rz = r->z.v;

	if (montg_is_apoint_zero(a)
		/*@ where (coords) X = AX, Y = AY */)
	{
		montg_set_jpoint_to_zero(r) /*@ where (coords) */;
		return 1;
	}

	/*@ do open_mont_afpoint_coords */
	/*@ do open_afpoint_fields */
	/*@ do open_store_fp */

	copy_bignum(ax, rx) /*@ where X = mont_p(AX) */;
	/*@ do close_store_u256_base0 */

	copy_bignum(ay, ry) /*@ where X = mont_p(AY) */;
	/*@ do close_store_u256_base0 */

	/*@ store_montg_one which implies
	      store_u256_limbs(MONTG_ONE, MONTG_ONE_Z) */
	/*@ do open_raw_u256_limbs */
	copy_bignum(az, rz) /*@ where X = MONTG_ONE_Z */;
	/*@ do close_store_u256_base0 */

	return 1;
}
