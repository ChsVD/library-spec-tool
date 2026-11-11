/* Verification copy of YCrypt/sm2/ecc_montg.c::montg_double_jpoint. */

#include "../include/ecc.h"
#include "../include/fieldOp.h"
#include "../include/jpoint_double_trace.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/jpoint_double_trace.strategies" */

void montg_sqr_mod_p(const u32 *a, u32 *result)
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
/*@ mont_in_place
    With A
    Require
      result == a &&
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_sm2_p * store_sm2_rhop
    Ensure
      result == a &&
      store_fp(result, mont_p(A * A)) *
      store_sm2_p * store_sm2_rhop
 */;

void montg_mul_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_non_alias
    With A B
    Require
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
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
/*@ mont_r_eq_b
    With A B
    Require
      result == b &&
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      store_sm2_p * store_sm2_rhop
    Ensure
      result == b &&
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(A * B)) *
      store_sm2_p * store_sm2_rhop
 */;

void mul_by_2_mod_p(const u32 *a, u32 *result)
/*@ mont_non_alias
    With A
    Require
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      UInt64Array::undef_full(&(result->v[0]), 4) * store_sm2_p
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(2 * A)) * store_sm2_p
 */;

void div_by_2_mod_p(const u32 *a, u32 *result)
/*@ mont_non_alias
    With A
    Require
      result != a && 0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      UInt64Array::undef_full(&(result->v[0]), 4) * store_sm2_p
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(fp_div2(A))) * store_sm2_p
 */;

void add_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_non_alias
    With A B
    Require
      0 <= A && A < SM2_P_Z && 0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) * store_fp(b, mont_p(B)) *
      UInt64Array::undef_full(&(result->v[0]), 4) * store_sm2_p
    Ensure
      store_fp(a, mont_p(A)) * store_fp(b, mont_p(B)) *
      store_fp(result, mont_p(A + B)) * store_sm2_p
 */;

void sub_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_non_alias
    With A B
    Require
      0 <= A && A < SM2_P_Z && 0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) * store_fp(b, mont_p(B)) *
      UInt64Array::undef_full(&(result->v[0]), 4) * store_sm2_p
    Ensure
      store_fp(a, mont_p(A)) * store_fp(b, mont_p(B)) *
      store_fp(result, mont_p(A - B)) * store_sm2_p
 */
/*@ mont_r_eq_b
    With A B
    Require
      result == b &&
      0 <= A && A < SM2_P_Z && 0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) * store_fp(b, mont_p(B)) * store_sm2_p
    Ensure
      result == b &&
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(A - B)) * store_sm2_p
 */;

void mul_by_3_mod_p(const u32 *a, u32 *result)
/*@ mont_in_place
    With A
    Require
      result == a && 0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) * store_sm2_p
    Ensure
      result == a &&
      store_fp(result, mont_p(3 * A)) * store_sm2_p
 */;

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
      r == a &&
      store_mont_jpoint(a, P) *
      store_sm2_p * store_sm2_rhop
    Ensure
      r == a &&
      store_mont_jpoint(r, sm2_point_double(P)) *
      store_sm2_p * store_sm2_rhop
 */
/*@ non_alias */
/*@ in_place */
{
	/*@ store_mont_jpoint(a, P_non_alias) $ non_alias which implies
	      exists JX_non_alias JY_non_alias JZ_non_alias,
	        jpoint_represents(JX_non_alias, JY_non_alias, JZ_non_alias, P_non_alias) &&
	        store_mont_jpoint_coords(a, JX_non_alias, JY_non_alias, JZ_non_alias)
	      by open_mont_jpoint
	 */
	/*@ Given JX_non_alias JY_non_alias JZ_non_alias $ non_alias */
	/*@ store_mont_jpoint(a, P_in_place) $ in_place which implies
	      exists JX_in_place JY_in_place JZ_in_place,
	        jpoint_represents(JX_in_place, JY_in_place, JZ_in_place, P_in_place) &&
	        store_mont_jpoint_coords(a, JX_in_place, JY_in_place, JZ_in_place)
	      by open_mont_jpoint
	 */
	/*@ Given JX_in_place JY_in_place JZ_in_place $ in_place */
	/*@ do open_mont_jpoint_coords */
	const u32* ax = &(a->x);
	const u32* ay = &(a->y);
	const u32* az = &(a->z);
	u32* rx = &(r->x);
	u32* ry = &(r->y);
	u32* rz = &(r->z);
	u32 U1, U2, U3, Zsqr, T;
	/*@ rx == ax && ry == ay && rz == az by local $ in_place */

	montg_sqr_mod_p(az, &Zsqr)
	/*@
	  where (mont_non_alias) A = JZ_non_alias $ non_alias
	  where (mont_non_alias) A = JZ_in_place $ in_place
	 */;
	/*@ do jdouble_trace_mont */

	mul_by_2_mod_p(ay, &T)
	/*@
	  where (mont_non_alias) A = JY_non_alias $ non_alias
	  where (mont_non_alias) A = JY_in_place $ in_place
	 */;
	/*@ do jdouble_trace_mont */
	montg_mul_mod_p(&T, az, rz)
	/*@
	  where (mont_non_alias)
	    A = jdouble_trace_s2(JY_non_alias), B = JZ_non_alias
	    $ non_alias
	  where (mont_r_eq_b)
	    A = jdouble_trace_s2(JY_in_place), B = JZ_in_place
	    $ in_place
	 */;

	montg_sqr_mod_p(&T, &T)
	/*@
	  where (mont_in_place) A = jdouble_trace_s2(JY_non_alias) $ non_alias
	  where (mont_in_place) A = jdouble_trace_s2(JY_in_place) $ in_place
	 */;
	/*@ do jdouble_trace_mont */
	montg_mul_mod_p(&T, ax, &U2)
	/*@
	  where (mont_non_alias) A = jdouble_trace_m4(JY_non_alias), B = JX_non_alias
	    $ non_alias
	  where (mont_non_alias) A = jdouble_trace_m4(JY_in_place), B = JX_in_place
	    $ in_place
	 */;
	/*@ do jdouble_trace_mont */

	montg_sqr_mod_p(&T, &T)
	/*@
	  where (mont_in_place) A = jdouble_trace_m4(JY_non_alias) $ non_alias
	  where (mont_in_place) A = jdouble_trace_m4(JY_in_place) $ in_place
	 */;
	/*@ do jdouble_trace_mont */
	div_by_2_mod_p(&T, &U3)
	/*@
	  where (mont_non_alias) A = jdouble_trace_t16(JY_non_alias) $ non_alias
	  where (mont_non_alias) A = jdouble_trace_t16(JY_in_place) $ in_place
	 */;
	/*@ do jdouble_trace_mont */

	sub_mod_p(ax, &Zsqr, &T)
	/*@
	  where (mont_non_alias)
	    A = JX_non_alias, B = jdouble_trace_z2(JZ_non_alias) $ non_alias
	  where (mont_non_alias)
	    A = JX_in_place, B = jdouble_trace_z2(JZ_in_place) $ in_place
	 */;
	/*@ do jdouble_trace_mont */
	add_mod_p(ax, &Zsqr, &U1)
	/*@
	  where (mont_non_alias) A = JX_non_alias, B = jdouble_trace_z2(JZ_non_alias)
	    $ non_alias
	  where (mont_non_alias) A = JX_in_place, B = jdouble_trace_z2(JZ_in_place)
	    $ in_place
	 */;
	/*@ do jdouble_trace_mont */
	montg_mul_mod_p(&T, &U1, &U1)
	/*@
	  where (mont_r_eq_b)
	    A = jdouble_trace_diff(JX_non_alias,JZ_non_alias), B = jdouble_trace_sum(JX_non_alias,JZ_non_alias)
	    $ non_alias
	  where (mont_r_eq_b)
	    A = jdouble_trace_diff(JX_in_place,JZ_in_place), B = jdouble_trace_sum(JX_in_place,JZ_in_place)
	    $ in_place
	 */;
	/*@ do jdouble_trace_mont */
	mul_by_3_mod_p(&U1, &U1)
	/*@
	  where (mont_in_place) A = jdouble_trace_prod(JX_non_alias,JZ_non_alias) $ non_alias
		  where (mont_in_place) A = jdouble_trace_prod(JX_in_place,JZ_in_place) $ in_place
		 */;
	/*@ do jdouble_trace_mont */

	montg_sqr_mod_p(&U1, &T)
	/*@
	  where (mont_non_alias)
	    A = jdouble_trace_slope(JX_non_alias,JZ_non_alias) $ non_alias
	  where (mont_non_alias)
	    A = jdouble_trace_slope(JX_in_place,JZ_in_place) $ in_place
	 */;
	/*@ do jdouble_trace_mont */
	mul_by_2_mod_p(&U2, rx)
	/*@
	  where (mont_non_alias) A = jdouble_trace_s4(JX_non_alias,JY_non_alias) $ non_alias
	  where (mont_non_alias)
	    A = jdouble_trace_s4(JX_in_place,JY_in_place)
	    $ in_place
	 */;
	/*@ do jdouble_trace_mont */
	sub_mod_p(&T, rx, rx)
	/*@
	  where (mont_r_eq_b)
	    A = jdouble_trace_slope_sq(JX_non_alias,JZ_non_alias),
	    B = jdouble_trace_u8(JX_non_alias,JY_non_alias) $ non_alias
	  where (mont_r_eq_b)
	    A = jdouble_trace_slope_sq(JX_in_place,JZ_in_place),
	    B = jdouble_trace_u8(JX_in_place,JY_in_place) $ in_place
	 */;
	/*@ do jdouble_trace_mont */
	sub_mod_p(&U2, rx, &T)
	/*@
	  where (mont_non_alias)
	    A = jdouble_trace_s4(JX_non_alias,JY_non_alias),
	    B = jdouble_trace_rx(JX_non_alias,JY_non_alias,JZ_non_alias)
	    $ non_alias
	  where (mont_non_alias)
	    A = jdouble_trace_s4(JX_in_place,JY_in_place),
	    B = jdouble_trace_rx(JX_in_place,JY_in_place,JZ_in_place)
	    $ in_place
	 */;
	/*@ do jdouble_trace_mont */
	montg_mul_mod_p(&U1, &T, &T)
	/*@
	  where (mont_r_eq_b)
	    A = jdouble_trace_slope(JX_non_alias,JZ_non_alias), B = jdouble_trace_tmp(JX_non_alias,JY_non_alias,JZ_non_alias)
	    $ non_alias
	  where (mont_r_eq_b)
	    A = jdouble_trace_slope(JX_in_place,JZ_in_place), B = jdouble_trace_tmp(JX_in_place,JY_in_place,JZ_in_place)
	    $ in_place
	 */;
	/*@ do jdouble_trace_mont */
	sub_mod_p(&T, &U3, ry)
	/*@
	  where (mont_non_alias)
	    A = jdouble_trace_tmp2(JX_non_alias,JY_non_alias,JZ_non_alias), B = jdouble_trace_t8(JY_non_alias)
	    $ non_alias
	  where (mont_non_alias)
	    A = jdouble_trace_tmp2(JX_in_place,JY_in_place,JZ_in_place), B = jdouble_trace_t8(JY_in_place)
	    $ in_place
	 */;
	/*@ do jdouble_trace_mont */

}
