/*
 * Verification extraction of YCrypt/sm2/ecc_montg.c::montg_jpoint_to_apoint.
 * YCrypt remains the authoritative source; this initial extraction preserves
 * the production function body for controller-driven annotation.
 */

#include "../include/ecc.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/u32_alias.strategies" */
/*@ include strategies "../strategy/ecc_montg_helper_views.strategies" */

/*@ Import Coq Require Import
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib
 */


static inline bool montg_is_jpoint_zero(const JPoint* dst)
/*@ coords
    With X Y Z
    Require
      store_mont_jpoint_coords(dst, X, Y, Z) *
      store_bn_zero
    Ensure
      ((__return == 1 && Z == 0) ||
       (__return == 0 && Z != 0)) &&
      store_mont_jpoint_coords(dst, X, Y, Z) *
      store_bn_zero
 */
;

static inline bool montg_equal_one(const UINT64 src[4])
/*@ field
    With A P
    Require
      src == P &&
      0 <= A && A < SM2_P_Z &&
      store_fp(P, A) *
      store_montg_one
    Ensure
      src == P &&
      ((__return == 1 && A == MONTG_ONE_Z) ||
       (__return == 0 && A != MONTG_ONE_Z)) &&
      store_fp(P, A) *
      store_montg_one
 */
;

static inline void bignum_set_to_zero(UINT64 a[4])
/*@
    Require UInt64Array::undef_full(a, 4)
    Ensure store_u256_limbs(a, 0)
 */
;

void montg_back_mod_p(const u32 *a, u32 *result)
/*@ regular_non_alias
    With A
    Require
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p * store_sm2_rhop
    Ensure
      store_fp(a, mont_p(A)) * store_fp(result, A) *
      store_sm2_p * store_sm2_rhop
 */
/*@ regular_in_place
    With A
    Require
      result == a && 0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) * store_sm2_p * store_sm2_rhop
    Ensure
      result == a && store_fp(result, A) *
      store_sm2_p * store_sm2_rhop
 */
;

void montg_inv_mod_p_ex(const UINT64 a[4], UINT64 r[4])
/*@ field_non_alias
    With A PA PR
    Require
      a == PA && r == PR &&
      0 <= A && A != 0 && A < SM2_P_Z &&
      store_fp(PA, A) * UInt64Array::undef_full(r, 4) *
      store_sm2_p * store_sm2_rhop
    Ensure
      exists ZI,
      a == PA && r == PR &&
      0 <= ZI && ZI < SM2_P_Z &&
      Zmod(A * ZI, SM2_P_Z) == 1 &&
      store_fp(PA, A) *
      store_fp(PR, mont_p(ZI)) *
      store_sm2_p * store_sm2_rhop
 */
;

void montg_sqr_mod_p(const u32 *a, u32 *result)
/*@ mont_non_alias
    With A
    Require
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) * UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p * store_sm2_rhop
    Ensure
      store_fp(a, mont_p(A)) * store_fp(result, mont_p(A * A)) *
      store_sm2_p * store_sm2_rhop
 */
;

void montg_mul_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_non_alias
    With A B
    Require
      0 <= A && A < SM2_P_Z && 0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p * store_sm2_rhop
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      store_fp(result, mont_p(A * B)) *
      store_sm2_p * store_sm2_rhop
 */
;

// Convert jacobian point (montgomery domain) to affine point (residue domain)
// Complexity:
//      3M + 1S + 1I
//      M: Multiplication
//      S: Square
//      I: Inversion
int montg_jpoint_to_apoint(const JPoint* a, UINT64* rx, UINT64* ry)
/*@ x_only
    With X Y Z
    Require
      rx != 0 && ry == 0 &&
      store_mont_jpoint_coords(a, X, Y, Z) *
      UInt64Array::undef_full(rx, 4) *
      store_bn_zero * store_montg_one * store_sm2_p * store_sm2_rhop
    Ensure
      exists RX,
        __return == 1 && ry == 0 &&
        ((Z == 0 && RX == 0) ||
         (Z != 0 &&
          (exists ZI,
            0 <= ZI && ZI < SM2_P_Z &&
            Zmod(Z * ZI, SM2_P_Z) == 1 &&
            RX == Zmod(X * ZI * ZI, SM2_P_Z)))) &&
        store_mont_jpoint_coords(a, X, Y, Z) *
        store_u256_limbs(rx, RX) *
        store_bn_zero * store_montg_one * store_sm2_p * store_sm2_rhop
 */
;

int montg_jpoint_to_apoint(const JPoint* a, UINT64* rx, UINT64* ry)
/*@ point_x_only <= x_only
    With (P : ec_point)
    Require
      rx != 0 && ry == 0 &&
      store_mont_jpoint(a, P) *
      UInt64Array::undef_full(rx, 4) *
      store_bn_zero * store_montg_one * store_sm2_p * store_sm2_rhop
    Ensure
      exists RX RY,
        __return == 1 && ry == 0 &&
        afpoint_represents(RX, RY, P) &&
        store_mont_jpoint(a, P) *
        store_u256_limbs(rx, RX) *
        store_bn_zero * store_montg_one * store_sm2_p * store_sm2_rhop
 */
;

int montg_jpoint_to_apoint(const JPoint* a, UINT64* rx, UINT64* ry)
/*@ x_only */
{
	const u32* ax = &(a->x);
	const u32* ay = &(a->y);
	const u32* az = &(a->z);
	u32 Zinv, Zisqr, T;

	/*@ store_mont_jpoint_coords(a, X, Y, Z) */
	if (montg_is_jpoint_zero(a) /*@ where (coords) X = X, Y = Y, Z = Z */)
	{
		if (rx) bignum_set_to_zero(rx);
		if (ry) bignum_set_to_zero(ry);
		return 1;
	}
	/*@ Z != 0 */

	/*@ do open_mont_jpoint_coords */
	/*@ do open_jpoint_fields */

	if (montg_equal_one(az->v)
	    /*@ where (field) A = mont_p(Z), P = az */)
	{
		/*@ do raw_undef_to_u32 */
		if (rx) montg_back_mod_p(ax, (u32*)rx)
			/*@ where (regular_non_alias) A = X */;
		/*@ do store_fp_output_to_raw */
		if (ry) montg_back_mod_p(ay, (u32*)ry)
			/*@ where (regular_non_alias) A = Y */;
		return 1;
	}

	/*@ store_fp(az, mont_p(Z)) */
	montg_back_mod_p(az, &T) /*@ where (regular_non_alias) A = Z */;
	/*@ UInt64Array::undef_full(Zinv.v, 4) */
	montg_inv_mod_p_ex(T.v, Zinv.v)
		/*@ where (field_non_alias)
		      A = Z, PA = &T, PR = &Zinv */;
	/*@ Given ZI */
	montg_sqr_mod_p(&Zinv, &Zisqr)
		/*@ where (mont_non_alias) A = ZI */;

	if (rx)
	{
		/*@ do raw_undef_to_u32 */
		montg_mul_mod_p(ax, &Zisqr, (u32*)rx)
			/*@ where (mont_non_alias) A = X,
			      B = Zmod(ZI * ZI, SM2_P_Z) */;
		montg_back_mod_p((u32*)rx, (u32*)rx)
			/*@ where (regular_in_place)
			      A = Zmod(X * ZI * ZI, SM2_P_Z) */;
		/*@ do store_fp_output_to_raw */
	}
	if (ry)
	{
		montg_mul_mod_p(&Zisqr, &Zinv, &T)
			/*@ where (mont_non_alias)
			      A = Zmod(ZI * ZI, SM2_P_Z), B = ZI */;
		/*@ do raw_undef_to_u32 */
		montg_mul_mod_p(ay, &T, (u32*)ry)
			/*@ where (mont_non_alias) A = Y,
			      B = Zmod(ZI * ZI * ZI, SM2_P_Z) */;
		montg_back_mod_p((u32*)ry, (u32*)ry)
			/*@ where (regular_in_place)
			      A = Zmod(Y * ZI * ZI * ZI, SM2_P_Z) */;
		/*@ do store_fp_output_to_raw */
	}
	return 1;
}
