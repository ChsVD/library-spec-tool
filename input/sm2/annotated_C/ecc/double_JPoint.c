/* Verification copy of YCrypt/sm2/ecc.c::double_JPoint. */

#include "../include/ecc.h"
#include "../include/fieldOp.h"
#include "../include/jpoint_double_trace.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_point_copy_steps.strategies" */
/*@ include strategies "../strategy/jpoint_double_trace.strategies" */

bool equ_to_JPoint_one(const JPoint* point)
/*@ base
    With JX JY JZ
    Require
      store_jpoint_fields(point, JX, JY, JZ)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && JX == 1 && JY == 1 && JZ == 0) ||
       (__return == 0 && (JX != 1 || JY != 1 || JZ != 0))) &&
      store_jpoint_fields(point, JX, JY, JZ)
 */
/*@ point
    With (P : ec_point)
    Require
      store_jpoint_with_canonical_infinity(point, P)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && P == ECInfinity) ||
       (__return == 0 && P != ECInfinity)) &&
      store_jpoint_with_canonical_infinity(point, P)
 */;

void double_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(result, Zmod(2 * A, SM2_P_Z)) *
      store_sm2_p
 */;

void pow_mod_p(const u32* x, u32* result)
/*@ non_alias
    With X
    Require
      store_fp(x, X) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(x, X) *
      store_fp(result, Zmod(X * X, SM2_P_Z)) *
      store_sm2_p *
      store_sm2_rhop
 */;

void mul_mod_p(const u32* x, const u32* y, u32* result)
/*@ non_alias
    With X Y
    Require
      store_fp(x, X) *
      store_fp(y, Y) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(x, X) *
      store_fp(y, Y) *
      store_fp(result, Zmod(X * Y, SM2_P_Z)) *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ r_eq_a
    With X Y
    Require
      result == x &&
      store_fp(x, X) *
      store_fp(y, Y) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == x &&
      store_fp(result, Zmod(X * Y, SM2_P_Z)) *
      store_fp(y, Y) *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ r_eq_b
    With X Y
    Require
      result == y &&
      store_fp(x, X) *
      store_fp(y, Y) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == y &&
      store_fp(x, X) *
      store_fp(result, Zmod(X * Y, SM2_P_Z)) *
      store_sm2_p *
      store_sm2_rhop
 */;

void div_by_2_mod_p(const u32 *a, u32 *result)
/*@ in_place
    With A
    Require
      result == a &&
      store_fp(a, A) *
      store_sm2_p
    Ensure
      result == a &&
      store_fp(result, fp_div2(A)) *
      store_sm2_p
 */;

void add_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias
    With A B
    Require
      store_fp(a, A) *
      store_fp(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(b, B) *
      store_fp(result, Zmod(A + B, SM2_P_Z)) *
      store_sm2_p
 */;

void sub_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ r_eq_a
    With A B
    Require
      result == a &&
      store_fp(a, A) *
      store_fp(b, B) *
      store_sm2_p
    Ensure
      result == a &&
      store_fp(result, Zmod(A - B, SM2_P_Z)) *
      store_fp(b, B) *
      store_sm2_p
 */
/*@ r_eq_b
    With A B
    Require
      result == b &&
      store_fp(a, A) *
      store_fp(b, B) *
      store_sm2_p
    Ensure
      result == b &&
      store_fp(a, A) *
      store_fp(result, Zmod(A - B, SM2_P_Z)) *
      store_sm2_p
 */;

void mul_by_3_mod_p(const u32 *a, u32 *result)
/*@ in_place
    With A
    Require
      result == a &&
      store_fp(a, A) *
      store_sm2_p
    Ensure
      result == a &&
      store_fp(result, Zmod(3 * A, SM2_P_Z)) *
      store_sm2_p
 */;

void double_JPoint(const JPoint* pt, JPoint* result)
/*@ non_alias
    With (P : ec_point)
    Require
      store_jpoint_with_canonical_infinity(pt, P) *
      UInt64Array::undef_full(field_addr(field_addr(result, JPoint, x), u32, v), 4) *
      UInt64Array::undef_full(field_addr(field_addr(result, JPoint, y), u32, v), 4) *
      UInt64Array::undef_full(field_addr(field_addr(result, JPoint, z), u32, v), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_jpoint_with_canonical_infinity(pt, P) *
      store_jpoint_with_canonical_infinity(result, sm2_point_double(P)) *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ in_place
    With (P : ec_point)
    Require
      result == pt &&
      store_jpoint_with_canonical_infinity(pt, P) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == pt &&
      store_jpoint_with_canonical_infinity(result, sm2_point_double(P)) *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ non_alias */
/*@ in_place */
{
	/*@ do jpoint_undef_fields */
	u32 S, U, M;
	if (equ_to_JPoint_one(pt)
	    /*@ where (point) P = P_non_alias $ non_alias
	        where (point) P = P_in_place $ in_place */)
	{
		/*@ do open_jpoint_canonical */
		/*@ do materialize_jpoint_record */
		*result = *pt;
		return;
	}

	/*@ store_jpoint_with_canonical_infinity(pt, P_non_alias) $ non_alias
	    which implies
	    exists JX_non_alias JY_non_alias JZ_non_alias,
	      jpoint_represents(JX_non_alias, JY_non_alias, JZ_non_alias, P_non_alias) &&
	      jpoint_canonical_infinity_encoding(JX_non_alias, JY_non_alias, JZ_non_alias, P_non_alias) &&
	      store_jpoint_fields(pt, JX_non_alias, JY_non_alias, JZ_non_alias)
	 */
	/*@ Given JX_non_alias JY_non_alias JZ_non_alias $ non_alias */
	/*@ store_jpoint_with_canonical_infinity(pt, P_in_place) $ in_place
	    which implies
	    exists JX_in_place JY_in_place JZ_in_place,
	      jpoint_represents(JX_in_place, JY_in_place, JZ_in_place, P_in_place) &&
	      jpoint_canonical_infinity_encoding(JX_in_place, JY_in_place, JZ_in_place, P_in_place) &&
	      store_jpoint_fields(pt, JX_in_place, JY_in_place, JZ_in_place)
	 */
	/*@ Given JX_in_place JY_in_place JZ_in_place $ in_place */

	double_mod_p(&(pt->y), &S)
	/*@ where (non_alias) A = JY_non_alias $ non_alias
	    where (non_alias) A = JY_in_place $ in_place */;
	/*@ do jdouble_trace_plain */
	pow_mod_p(&(pt->z), &U)
	/*@ where (non_alias) X = JZ_non_alias $ non_alias
	    where (non_alias) X = JZ_in_place $ in_place */;
	/*@ do jdouble_trace_plain */

	pow_mod_p(&S, &M)
	/*@ where (non_alias) X = jdouble_trace_s2(JY_non_alias) $ non_alias
	    where (non_alias) X = jdouble_trace_s2(JY_in_place) $ in_place */;
	/*@ do jdouble_trace_plain */
	mul_mod_p(&S, &(pt->z), &(result->z))
	/*@ where (non_alias) X = jdouble_trace_s2(JY_non_alias), Y = JZ_non_alias $ non_alias
	    where (r_eq_b) X = jdouble_trace_s2(JY_in_place), Y = JZ_in_place $ in_place */;

	pow_mod_p(&M, &(result->y))
	/*@ where (non_alias) X = jdouble_trace_m4(JY_non_alias) $ non_alias
	    where (non_alias) X = jdouble_trace_m4(JY_in_place) $ in_place */;
	/*@ do jdouble_trace_plain */

	mul_mod_p(&M, &(pt->x), &S)
	/*@ where (non_alias) X = jdouble_trace_m4(JY_non_alias), Y = JX_non_alias $ non_alias
	    where (non_alias) X = jdouble_trace_m4(JY_in_place), Y = JX_in_place $ in_place */;
	/*@ do jdouble_trace_plain */
	div_by_2_mod_p(&(result->y), &(result->y))
	/*@ where (in_place) A = jdouble_trace_t16(JY_non_alias) $ non_alias
	    where (in_place) A = jdouble_trace_t16(JY_in_place) $ in_place */;
	/*@ do jdouble_trace_plain */

	add_mod_p(&U, &(pt->x), &M)
	/*@ where (non_alias) A = jdouble_trace_z2(JZ_non_alias), B = JX_non_alias $ non_alias
	    where (non_alias) A = jdouble_trace_z2(JZ_in_place), B = JX_in_place $ in_place */;
	/*@ do jdouble_trace_plain */
	sub_mod_p(&(pt->x), &U, &U)
	/*@ where (r_eq_b) A = JX_non_alias, B = jdouble_trace_z2(JZ_non_alias) $ non_alias
	    where (r_eq_b) A = JX_in_place, B = jdouble_trace_z2(JZ_in_place) $ in_place */;
	/*@ do jdouble_trace_plain */
	mul_mod_p(&M, &U, &M)
	/*@ where (r_eq_a) X = jdouble_trace_sum(JX_non_alias,JZ_non_alias), Y = jdouble_trace_diff(JX_non_alias,JZ_non_alias) $ non_alias
	    where (r_eq_a) X = jdouble_trace_sum(JX_in_place,JZ_in_place), Y = jdouble_trace_diff(JX_in_place,JZ_in_place) $ in_place */;
	/*@ do jdouble_trace_plain */
	mul_by_3_mod_p(&M, &M)
	/*@ where (in_place) A = jdouble_trace_prod(JX_non_alias,JZ_non_alias) $ non_alias
	    where (in_place) A = jdouble_trace_prod(JX_in_place,JZ_in_place) $ in_place */;
	/*@ do jdouble_trace_plain */

	double_mod_p(&S, &U)
	/*@ where (non_alias) A = jdouble_trace_s4(JX_non_alias,JY_non_alias) $ non_alias
	    where (non_alias) A = jdouble_trace_s4(JX_in_place,JY_in_place) $ in_place */;
	/*@ do jdouble_trace_plain */
	pow_mod_p(&M, &(result->x))
	/*@ where (non_alias) X = jdouble_trace_slope(JX_non_alias,JZ_non_alias) $ non_alias
	    where (non_alias) X = jdouble_trace_slope(JX_in_place,JZ_in_place) $ in_place */;
	/*@ do jdouble_trace_plain */
	sub_mod_p(&(result->x), &U, &(result->x))
	/*@ where (r_eq_a) A = jdouble_trace_slope_sq(JX_non_alias,JZ_non_alias), B = jdouble_trace_u8(JX_non_alias,JY_non_alias) $ non_alias
	    where (r_eq_a) A = jdouble_trace_slope_sq(JX_in_place,JZ_in_place), B = jdouble_trace_u8(JX_in_place,JY_in_place) $ in_place */;
	/*@ do jdouble_trace_plain */

	sub_mod_p(&S, &(result->x), &S)
	/*@ where (r_eq_a) A = jdouble_trace_s4(JX_non_alias,JY_non_alias), B = jdouble_trace_rx(JX_non_alias,JY_non_alias,JZ_non_alias) $ non_alias
	    where (r_eq_a) A = jdouble_trace_s4(JX_in_place,JY_in_place), B = jdouble_trace_rx(JX_in_place,JY_in_place,JZ_in_place) $ in_place */;
	/*@ do jdouble_trace_plain */
	mul_mod_p(&S, &M, &S)
	/*@ where (r_eq_a) X = jdouble_trace_tmp(JX_non_alias,JY_non_alias,JZ_non_alias), Y = jdouble_trace_slope(JX_non_alias,JZ_non_alias) $ non_alias
	    where (r_eq_a) X = jdouble_trace_tmp(JX_in_place,JY_in_place,JZ_in_place), Y = jdouble_trace_slope(JX_in_place,JZ_in_place) $ in_place */;
	/*@ do jdouble_trace_plain */
	sub_mod_p(&S, &(result->y), &(result->y))
	/*@ where (r_eq_b) A = jdouble_trace_tmp2(JX_non_alias,JY_non_alias,JZ_non_alias), B = jdouble_trace_t8(JY_non_alias) $ non_alias
	    where (r_eq_b) A = jdouble_trace_tmp2(JX_in_place,JY_in_place,JZ_in_place), B = jdouble_trace_t8(JY_in_place) $ in_place */;
	/*@ do jdouble_trace_plain */
}
