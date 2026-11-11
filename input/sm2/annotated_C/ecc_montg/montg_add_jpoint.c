/* Verification copy of YCrypt/sm2/ecc_montg.c::montg_add_jpoint. */

#include "../include/ecc.h"
#include "../include/fieldOp.h"
#include "../include/ecc_constants.h"
#include "../include/montg_add_jpoint_trace.h"
/*@ include strategies "../strategy/montg_add_jpoint_precompute.strategies" */
/*@ include strategies "../strategy/montg_add_jpoint_x.strategies" */
/*@ include strategies "../strategy/montg_add_jpoint_y.strategies" */
/*@ include strategies "../strategy/montg_add_jpoint_z.strategies" */
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_point_overwrite.strategies" */
/*@ include strategies "../strategy/ecc_point_facts.strategies" */
/*@ include strategies "../strategy/montg_add_jpoint_compare.strategies" */
/*@ include strategies "../strategy/montg_add_jpoint_cleanup.strategies" */
/*@ include strategies "../strategy/montg_add_jpoint_result.strategies" */
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
/*@ mont_r_eq_b
    With A B
    Require
      result == b &&
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) * store_fp(b, mont_p(B)) *
      store_sm2_p * store_sm2_rhop
    Ensure
      result == b &&
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(A * B)) *
      store_sm2_p * store_sm2_rhop
 */
;

void add_mod_p(const u32* a, const u32* b, u32* result)
/*@ non_alias
    With A B
    Require
      store_fp(a, A) * store_fp(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4) * store_sm2_p
    Ensure
      store_fp(a, A) * store_fp(b, B) *
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
      result == a &&
      store_fp(a, A) * store_fp(b, B) * store_sm2_p
    Ensure
      result == a &&
      store_fp(result, Zmod(A - B, SM2_P_Z)) *
      store_fp(b, B) * store_sm2_p
 */
;

void mul_by_2_mod_p(const u32* a, u32* result)
/*@ non_alias
    With A
    Require
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) * store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(result, Zmod(2 * A, SM2_P_Z)) * store_sm2_p
 */
;

void div_by_2_mod_p(const u32* a, u32* result)
/*@ in_place
    With A
    Require result == a && store_fp(a, A) * store_sm2_p
    Ensure result == a && store_fp(result, fp_div2(A)) * store_sm2_p
 */
;

u32* memcpy(u32* dst, const u32* src, size_t n)
/*@ non_alias
    With A
    Require
      n == 32 && store_fp(src, A) *
      UInt64Array::undef_full(&(dst->v[0]), 4)
    Ensure
      __return == dst &&
      store_fp(src, A) * store_fp(dst, A)
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

int montg_add_jpoint(const JPoint* a, const JPoint* b, JPoint* r)
/*@ non_alias
    With (P Q : ec_point)
    Require
      store_mont_jpoint(a, P) * store_mont_jpoint(b, Q) *
      UInt64Array::undef_full(&(r->x.v[0]), 4) *
      UInt64Array::undef_full(&(r->y.v[0]), 4) *
      UInt64Array::undef_full(&(r->z.v[0]), 4) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
    Ensure
      __return == 1 &&
      store_mont_jpoint(a, P) * store_mont_jpoint(b, Q) *
      store_mont_jpoint(r, sm2_point_add(P, Q)) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
 */
/*@ r_eq_a
    With (P Q : ec_point)
    Require
      r == a &&
      store_mont_jpoint(a, P) * store_mont_jpoint(b, Q) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
    Ensure
      __return == 1 && r == a &&
      store_mont_jpoint(r, sm2_point_add(P, Q)) *
      store_mont_jpoint(b, Q) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
 */
/*@ r_eq_b
    With (P Q : ec_point)
    Require
      r == b &&
      store_mont_jpoint(a, P) * store_mont_jpoint(b, Q) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
    Ensure
      __return == 1 && r == b &&
      store_mont_jpoint(a, P) *
      store_mont_jpoint(r, sm2_point_add(P, Q)) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
 */
/*@ non_alias */
/*@ r_eq_a */
/*@ r_eq_b */
{
	const u32 *ax = &(a->x);
	const u32 *ay = &(a->y);
	const u32 *az = &(a->z);
	const u32 *bx = &(b->x);
	const u32 *by = &(b->y);
	const u32 *bz = &(b->z);
	u32* rx = &(r->x);
	u32* ry = &(r->y);
	u32* rz = &(r->z);
	u32 U1, U2, U3, U4, U5, U6, U7, U8, U9, Z1sqr, Z2sqr, U3sqr, T;

	if (montg_is_jpoint_zero(a)
	    /*@ where (point) P = P_non_alias $ non_alias
	        where (point) P = P_r_eq_a $ r_eq_a
	        where (point) P = P_r_eq_b $ r_eq_b */)
		{
			CopyJPoint(b, r)
		/*@ where (mont_non_alias) P = Q_non_alias $ non_alias
		    where (mont_non_alias) P = Q_r_eq_a $ r_eq_a
		    where (mont_in_place) P = Q_r_eq_b $ r_eq_b */;
		return 1;
	}
	if (montg_is_jpoint_zero(b)
	    /*@ where (point) P = Q_non_alias $ non_alias
	        where (point) P = Q_r_eq_a $ r_eq_a
	        where (point) P = Q_r_eq_b $ r_eq_b */)
		{
			CopyJPoint(a, r)
		/*@ where (mont_non_alias) P = P_non_alias $ non_alias
		    where (mont_in_place) P = P_r_eq_a $ r_eq_a
		    where (mont_non_alias) P = P_r_eq_b $ r_eq_b */;
		return 1;
	}

	/*@ do open_mont_jpoint */
	/*@ do open_mont_jpoint_coords */
	/*@ Given AX from x AY from y AZ from z
	          BX from x BY from y BZ from z */
	/*@ do finite_jpoint_coordinates */

	montg_sqr_mod_p(az, &Z1sqr)
		/*@ where (mont_non_alias) A = AZ */;
	montg_sqr_mod_p(bz, &Z2sqr)
		/*@ where (mont_non_alias) A = BZ */;

	montg_mul_mod_p(ax, &Z2sqr, &U1)
		/*@ where (mont_non_alias) A = AX, B = aj_qz2(BZ) */;
	montg_mul_mod_p(bx, &Z1sqr, &U2)
		/*@ where (mont_non_alias) A = BX, B = aj_pz2(AZ) */;

	montg_mul_mod_p(az, &Z1sqr, &T)
		/*@ where (mont_non_alias) A = AZ, B = aj_pz2(AZ) */;
	montg_mul_mod_p(by, &T, &U5)
		/*@ where (mont_non_alias) A = BY, B = aj_pz3(AZ) */;

	montg_mul_mod_p(bz, &Z2sqr, &T)
		/*@ where (mont_non_alias) A = BZ, B = aj_qz2(BZ) */;
	montg_mul_mod_p(ay, &T, &U4)
		/*@ where (mont_non_alias) A = AY, B = aj_qz3(BZ) */;
	/*@ do mont_aj_compare_open */
	if (bignum_is_equal(U1.v, U2.v)
	    /*@ where (non_alias)
	          A = mont_p(aj_u1(AX, BZ)),
	          B = mont_p(aj_u2(BX, AZ)) */ &&
	    bignum_is_equal(U4.v, U5.v)
	    /*@ where (non_alias)
	          A = mont_p(aj_s1(AY, BZ)),
	          B = mont_p(aj_s2(BY, AZ)) */)
			{
				/*@ do mont_aj_compare_close */
				/*@ do mont_aj_equal_points */
				montg_double_jpoint(a, r)
			/*@ where (non_alias) P = P_non_alias $ non_alias
			    where (non_alias) P = P_r_eq_b $ r_eq_b
				    where (in_place) P = P_r_eq_a $ r_eq_a */;
					/*@ do mont_aj_equal_cleanup */
					return 1;
				}
	/*@ do mont_aj_compare_close */
	sub_mod_p(&U1, &U2, &U3)
		/*@ where (non_alias)
		      A = mont_p(aj_u1(AX, BZ)),
		      B = mont_p(aj_u2(BX, AZ)) */;
	sub_mod_p(&U4, &U5, &U6)
		/*@ where (non_alias)
		      A = mont_p(aj_s1(AY, BZ)),
		      B = mont_p(aj_s2(BY, AZ)) */;
	add_mod_p(&U1, &U2, &U7)
		/*@ where (non_alias)
		      A = mont_p(aj_u1(AX, BZ)),
		      B = mont_p(aj_u2(BX, AZ)) */;
	add_mod_p(&U4, &U5, &U8)
		/*@ where (non_alias)
		      A = mont_p(aj_s1(AY, BZ)),
		      B = mont_p(aj_s2(BY, AZ)) */;

	montg_sqr_mod_p(&U3, &U3sqr)
		/*@ where (mont_non_alias) A = aj_h(AX, AZ, BX, BZ) */;
	montg_mul_mod_p(&U7, &U3sqr, &T)
		/*@ where (mont_non_alias)
		      A = aj_u_sum(AX, AZ, BX, BZ),
		      B = aj_h2(AX, AZ, BX, BZ) */;

	montg_sqr_mod_p(&U6, rx)
		/*@ where (mont_non_alias) A = aj_rr(AY, AZ, BY, BZ) */;
	sub_mod_p(rx, &T, rx)
		/*@ where (r_eq_a)
		      A = mont_p(aj_rr2(AY, AZ, BY, BZ)),
		      B = mont_p(aj_base(AX, AZ, BX, BZ)) */;

	memcpy(&U9, &T, sizeof(UINT64) * 4)
		/*@ where (non_alias) A = mont_p(aj_base(AX, AZ, BX, BZ)) */;
	mul_by_2_mod_p(rx, &T)
		/*@ where (non_alias)
		      A = mont_p(aj_rx(AX, AY, AZ, BX, BY, BZ)) */;
	sub_mod_p(&U9, &T, &U9)
		/*@ where (r_eq_a)
		      A = mont_p(aj_base(AX, AZ, BX, BZ)),
		      B = mont_p(aj_twice_rx(AX, AY, AZ, BX, BY, BZ)) */;

	montg_mul_mod_p(&U3sqr, &U3, &T)
		/*@ where (mont_non_alias)
		      A = aj_h2(AX, AZ, BX, BZ),
		      B = aj_h(AX, AZ, BX, BZ) */;
	montg_mul_mod_p(&U8, &T, &T)
		/*@ where (mont_r_eq_b)
		      A = aj_s_sum(AY, AZ, BY, BZ),
		      B = Zmod(aj_h2(AX, AZ, BX, BZ) *
		               aj_h(AX, AZ, BX, BZ), SM2_P_Z) */;

	montg_mul_mod_p(&U9, &U6, ry)
		/*@ where (mont_non_alias)
		      A = aj_base_minus_twice_rx(AX, AY, AZ, BX, BY, BZ),
		      B = aj_rr(AY, AZ, BY, BZ) */;
	sub_mod_p(ry, &T, ry)
		/*@ where (r_eq_a)
		      A = mont_p(aj_left_y(AX, AY, AZ, BX, BY, BZ)),
		      B = mont_p(aj_right_y(AX, AY, AZ, BX, BY, BZ)) */;
	div_by_2_mod_p(ry, ry)
		/*@ where (in_place)
		      A = mont_p(aj_y_num(AX, AY, AZ, BX, BY, BZ)) */;

	montg_mul_mod_p(az, bz, &T)
		/*@ where (mont_non_alias) A = AZ, B = BZ */;
	montg_mul_mod_p(&T, &U3, rz)
		/*@ where (mont_non_alias)
		      A = aj_zbase(AZ, BZ),
		      B = aj_h(AX, AZ, BX, BZ) */;
	/*@ do mont_aj_generic_result */
	/*@ do mont_aj_generic_cleanup */

	return 1;
}
