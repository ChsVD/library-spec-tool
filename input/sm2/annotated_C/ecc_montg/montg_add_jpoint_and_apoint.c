/* Verification copy of YCrypt/sm2/ecc_montg.c::montg_add_jpoint_and_apoint. */

#include "../include/ecc.h"
#include "../include/fieldOp.h"
#include "../include/ecc_constants.h"
#include "../include/montg_add_jpoint_and_apoint_trace.h"
/*@ include strategies "../strategy/montg_add_jpoint_and_apoint_precompute.strategies" */
/*@ include strategies "../strategy/montg_add_jpoint_and_apoint_x.strategies" */
/*@ include strategies "../strategy/montg_add_jpoint_and_apoint_y.strategies" */
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_point_overwrite.strategies" */
/*@ include strategies "../strategy/ecc_point_facts.strategies" */
/*@ include strategies "../strategy/montg_add_jpoint_and_apoint_compare.strategies" */
/*@ include strategies "../strategy/montg_add_jpoint_and_apoint_result.strategies" */
/*@ include strategies "../strategy/montg_add_jpoint_and_apoint_cleanup.strategies" */

static inline bool montg_is_jpoint_zero(const JPoint* point)
/*@ point
    With (P : ec_point)
    Require store_mont_jpoint(point, P) * store_bn_zero
    Ensure
      ((__return == 1 && P == ECInfinity) ||
       (__return == 0 && P != ECInfinity)) &&
      store_mont_jpoint(point, P) * store_bn_zero
 */
;

static inline bool montg_is_apoint_zero(const AFPoint* point)
/*@ point
    With (P : ec_point)
    Require store_mont_afpoint(point, P) * store_bn_zero
    Ensure
      ((__return == 1 && P == ECInfinity) ||
       (__return == 0 && P != ECInfinity)) &&
      store_mont_afpoint(point, P) * store_bn_zero
 */
;

int montg_apoint_to_jpoint2(const AFPoint* a, JPoint* r)
/*@ point_non_alias
    With (P : ec_point)
    Require
      store_mont_afpoint(a, P) *
      UInt64Array::undef_full(&(r->x.v[0]), 4) *
      UInt64Array::undef_full(&(r->y.v[0]), 4) *
      UInt64Array::undef_full(&(r->z.v[0]), 4) *
      store_bn_zero * store_montg_one
    Ensure
      __return == 1 &&
      store_mont_afpoint(a, P) * store_mont_jpoint(r, P) *
      store_bn_zero * store_montg_one
 */
;

inline void CopyJPoint(const JPoint* src, JPoint* dst)
/*@ mont_non_alias
    With (P : ec_point)
    Require
      store_mont_jpoint(src, P) *
      UInt64Array::undef_full(&(dst->x.v[0]), 4) *
      UInt64Array::undef_full(&(dst->y.v[0]), 4) *
      UInt64Array::undef_full(&(dst->z.v[0]), 4)
    Ensure
      store_mont_jpoint(src, P) * store_mont_jpoint(dst, P)
 */
/*@ mont_in_place
    With (P : ec_point)
    Require dst == src && store_mont_jpoint(src, P)
    Ensure dst == src && store_mont_jpoint(dst, P)
 */
;

static inline bool bignum_is_equal(const UINT64 a[4], const UINT64 b[4])
/*@ non_alias
    With A B
    Require store_u256_limbs(a, A) * store_u256_limbs(b, B)
    Ensure
      ((__return == 1 && A == B) ||
       (__return == 0 && A != B)) &&
      store_u256_limbs(a, A) * store_u256_limbs(b, B)
 */
;

static inline void montg_set_jpoint_to_zero(JPoint* dst)
/*@ point
    Require
      store_montg_one *
      UInt64Array::undef_full(&(dst->x.v[0]), 4) *
      UInt64Array::undef_full(&(dst->y.v[0]), 4) *
      UInt64Array::undef_full(&(dst->z.v[0]), 4)
    Ensure store_montg_one * store_mont_jpoint(dst, ECInfinity)
 */
;

void montg_double_jpoint(const JPoint* a, JPoint* r)
/*@ non_alias
    With (P : ec_point)
    Require
      store_mont_jpoint(a, P) *
      UInt64Array::undef_full(&(r->x.v[0]), 4) *
      UInt64Array::undef_full(&(r->y.v[0]), 4) *
      UInt64Array::undef_full(&(r->z.v[0]), 4) *
      store_sm2_p * store_sm2_rhop
    Ensure
      store_mont_jpoint(a, P) *
      store_mont_jpoint(r, sm2_point_double(P)) *
      store_sm2_p * store_sm2_rhop
 */
/*@ in_place
    With (P : ec_point)
    Require
      r == a && store_mont_jpoint(a, P) *
      store_sm2_p * store_sm2_rhop
    Ensure
      r == a && store_mont_jpoint(r, sm2_point_double(P)) *
      store_sm2_p * store_sm2_rhop
 */
;

void montg_sqr_mod_p(const u32* a, u32* result)
/*@ mont_non_alias
    With A
    Require
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p * store_sm2_rhop
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(A * A)) *
      store_sm2_p * store_sm2_rhop
 */
;

void montg_mul_mod_p(const u32* a, const u32* b, u32* result)
/*@ mont_non_alias
    With A B
    Require
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) * store_fp(b, mont_p(B)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p * store_sm2_rhop
    Ensure
      store_fp(a, mont_p(A)) * store_fp(b, mont_p(B)) *
      store_fp(result, mont_p(A * B)) *
      store_sm2_p * store_sm2_rhop
 */
/*@ mont_r_eq_a
    With A B
    Require
      result == a &&
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) * store_fp(b, mont_p(B)) *
      store_sm2_p * store_sm2_rhop
    Ensure
      result == a && store_fp(result, mont_p(A * B)) *
      store_fp(b, mont_p(B)) * store_sm2_p * store_sm2_rhop
 */
/*@ mont_r_eq_b
    With A B
    Require
      result == b &&
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) * store_fp(b, mont_p(B)) *
      store_sm2_p * store_sm2_rhop
    Ensure
      result == b && store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(A * B)) *
      store_sm2_p * store_sm2_rhop
 */
;

void add_mod_p(const u32* a, const u32* b, u32* result)
/*@ r_eq_b
    With A B
    Require
      result == b && store_fp(a, A) * store_fp(b, B) * store_sm2_p
    Ensure
      result == b && store_fp(a, A) *
      store_fp(result, Zmod(A + B, SM2_P_Z)) * store_sm2_p
 */
;

void sub_mod_p(const u32* a, const u32* b, u32* result)
/*@ non_alias
    With A B
    Require
      store_fp(a, A) * store_fp(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4) * store_sm2_p
    Ensure
      store_fp(a, A) * store_fp(b, B) *
      store_fp(result, Zmod(A - B, SM2_P_Z)) * store_sm2_p
 */
/*@ r_eq_a
    With A B
    Require
      result == a && store_fp(a, A) * store_fp(b, B) * store_sm2_p
    Ensure
      result == a && store_fp(result, Zmod(A - B, SM2_P_Z)) *
      store_fp(b, B) * store_sm2_p
 */
/*@ r_eq_b
    With A B
    Require
      result == b && store_fp(a, A) * store_fp(b, B) * store_sm2_p
    Ensure
      result == b && store_fp(a, A) *
      store_fp(result, Zmod(A - B, SM2_P_Z)) * store_sm2_p
 */
;

void mul_by_2_mod_p(const u32* a, u32* result)
/*@ non_alias
    With A
    Require
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) * store_sm2_p
    Ensure
      store_fp(a, A) * store_fp(result, Zmod(2 * A, SM2_P_Z)) *
      store_sm2_p
 */
;

int montg_add_jpoint_and_apoint(
    const JPoint* a, const AFPoint* b, JPoint* r)
/*@ non_alias
    With (P Q : ec_point)
    Require
      store_mont_jpoint(a, P) * store_mont_afpoint(b, Q) *
      UInt64Array::undef_full(&(r->x.v[0]), 4) *
      UInt64Array::undef_full(&(r->y.v[0]), 4) *
      UInt64Array::undef_full(&(r->z.v[0]), 4) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
    Ensure
      __return == 1 &&
      store_mont_jpoint(a, P) * store_mont_afpoint(b, Q) *
      store_mont_jpoint(r, sm2_point_add(P, Q)) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
 */
/*@ r_eq_a
    With (P Q : ec_point)
    Require
      r == a &&
      store_mont_jpoint(a, P) * store_mont_afpoint(b, Q) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
    Ensure
      __return == 1 && r == a &&
      store_mont_jpoint(r, sm2_point_add(P, Q)) *
      store_mont_afpoint(b, Q) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
 */
/*@ non_alias */
/*@ r_eq_a */
{
	const u32* ax = &(a->x);
	const u32* ay = &(a->y);
	const u32* az = &(a->z);
	const u32* bx = &(b->x);
	const u32* by = &(b->y);

	u32* rx = &(r->x);
	u32* ry = &(r->y);
	u32* rz = &(r->z);
	u32 A, B, C, D, E, Zsqr, Ccub, T;

	if (montg_is_jpoint_zero(a)
	    /*@ where (point) P = P_non_alias $ non_alias
	        where (point) P = P_r_eq_a $ r_eq_a */)
	{
		montg_apoint_to_jpoint2(b, r)
		/*@ where (point_non_alias) P = Q_non_alias $ non_alias
		    where (point_non_alias) P = Q_r_eq_a $ r_eq_a */;
		return 1;
	}
	if (montg_is_apoint_zero(b)
	    /*@ where (point) P = Q_non_alias $ non_alias
	        where (point) P = Q_r_eq_a $ r_eq_a */)
	{
		CopyJPoint(a, r)
		/*@ where (mont_non_alias) P = P_non_alias $ non_alias
		    where (mont_in_place) P = P_r_eq_a $ r_eq_a */;
		return 1;
	}

	/*@ do open_mont_afpoint */
	/*@ do open_mont_jpoint */
	/*@ do open_mont_afpoint_coords */
	/*@ do open_mont_jpoint_coords */
	/*@ Given AX from x AY from y AZ from z BX from x BY from y */
	/*@ do finite_jpoint_coordinates */

	montg_sqr_mod_p(az, &Zsqr)
		/*@ where (mont_non_alias) A = AZ */;
	montg_mul_mod_p(bx, &Zsqr, &A)
		/*@ where (mont_non_alias) A = BX, B = maja_z2(AZ) */;

	montg_mul_mod_p(az, &Zsqr, &T)
		/*@ where (mont_non_alias) A = AZ, B = maja_z2(AZ) */;
	montg_mul_mod_p(by, &T, &B)
		/*@ where (mont_non_alias) A = BY, B = maja_z3(AZ) */;

	sub_mod_p(&A, ax, &C)
		/*@ where (non_alias)
		      A = mont_p(maja_u2(BX, AZ)), B = mont_p(AX) */;
	sub_mod_p(&B, ay, &D)
		/*@ where (non_alias)
		      A = mont_p(maja_s2(BY, AZ)), B = mont_p(AY) */;

	/* Handle equal and inverse finite inputs before the generic formula. */
	/*@ store_bn_zero which implies
	      store_u256_limbs(BN_ZERO, 0) */
	/*@ do open_store_u256 */
	/*@ do mont_maja_compare_open */
	if (bignum_is_equal(C.v, BN_ZERO)
	    /*@ where (non_alias) A = mont_p(maja_h(AX, BX, AZ)), B = 0 */)
	{
		if (bignum_is_equal(D.v, BN_ZERO)
		    /*@ where (non_alias) A = mont_p(maja_r(AY, BY, AZ)), B = 0 */)
		{
			/*@ do mont_maja_compare_close */
			/*@ do mont_maja_equal_points */
			montg_double_jpoint(a, r)
			/*@ where (non_alias) P = P_non_alias $ non_alias
			    where (in_place) P = P_r_eq_a $ r_eq_a */;
			/*@ do mont_maja_early_cleanup */
			return 1;
		}
		/*@ do mont_maja_compare_close */
		/*@ do mont_maja_inverse_sum */
		montg_set_jpoint_to_zero(r) /*@ where (point) */;
		/*@ do mont_maja_early_cleanup */
		return 1;
	}
	/*@ do mont_maja_compare_close */

	montg_sqr_mod_p(&C, &T)
		/*@ where (mont_non_alias) A = maja_h(AX, BX, AZ) */;
	montg_mul_mod_p(&C, &T, &Ccub)
		/*@ where (mont_non_alias)
		      A = maja_h(AX, BX, AZ), B = maja_h2(AX, BX, AZ) */;
	montg_mul_mod_p(ax, &T, &E)
		/*@ where (mont_non_alias) A = AX, B = maja_h2(AX, BX, AZ) */;

	mul_by_2_mod_p(&E, &T)
		/*@ where (non_alias) A = mont_p(maja_u1h2(AX, BX, AZ)) */;
	add_mod_p(&Ccub, &T, &T)
		/*@ where (r_eq_b)
		      A = mont_p(maja_h3(AX, BX, AZ)),
		      B = mont_p(maja_two_u1h2(AX, BX, AZ)) */;
	montg_sqr_mod_p(&D, rx)
		/*@ where (mont_non_alias) A = maja_r(AY, BY, AZ) */;
	sub_mod_p(rx, &T, rx)
		/*@ where (r_eq_a)
		      A = mont_p(maja_r2(AY, BY, AZ)),
		      B = mont_p(maja_x_adjust(AX, BX, AZ)) */;

	sub_mod_p(&E, rx, &T)
		/*@ where (non_alias)
		      A = mont_p(maja_u1h2(AX, BX, AZ)),
		      B = mont_p(maja_rx(AX, AY, AZ, BX, BY)) */;
	montg_mul_mod_p(&D, &T, &T)
		/*@ where (mont_r_eq_b)
		      A = maja_r(AY, BY, AZ),
		      B = maja_e_minus_rx(AX, AY, AZ, BX, BY) */;
	montg_mul_mod_p(ay, &Ccub, ry)
		/*@ where (mont_non_alias)
		      A = AY, B = maja_h3(AX, BX, AZ) $ non_alias
		    where (mont_r_eq_a)
		      A = AY, B = maja_h3(AX, BX, AZ) $ r_eq_a */;
	sub_mod_p(&T, ry, ry)
		/*@ where (r_eq_b)
		      A = mont_p(maja_r_times_delta(AX, AY, AZ, BX, BY)),
		      B = mont_p(maja_y1h3(AX, AY, BX, AZ)) */;

	montg_mul_mod_p(az, &C, rz)
		/*@ where (mont_non_alias)
		      A = AZ, B = maja_h(AX, BX, AZ) $ non_alias
		    where (mont_r_eq_a)
		      A = AZ, B = maja_h(AX, BX, AZ) $ r_eq_a */;
	/*@ do mont_maja_generic_result */
	/*@ do mont_maja_generic_cleanup */

	return 1;
}
