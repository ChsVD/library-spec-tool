
/* Verification copy of YCrypt/sm2/ecc.c::add_JPoint. */

#include "../include/ecc.h"
#include "../include/fieldOp.h"
#include "../include/add_JPoint_trace.h"
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */
/*@ include strategies "../strategy/ecc_point_facts.strategies" */
/*@ include strategies "../strategy/ecc_point_copy_steps.strategies" */
/*@ include strategies "../strategy/add_JPoint_boundary.strategies" */
/*@ include strategies "../strategy/add_JPoint_trace.strategies" */

bool equ_to_JPoint_one(const JPoint* point)
/*@ base
    With JX JY JZ
    Require store_jpoint_fields(point, JX, JY, JZ)
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

bool u32_eq(const u32 *a, const u32 *b)
/*@ base
    With A B
    Require store_u256(a, A) * store_u256(b, B)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == B) || (__return == 0 && A != B)) &&
      store_u256(a, A) * store_u256(b, B)
 */
/*@ fp <= base
    With A B
    Require store_fp(a, A) * store_fp(b, B)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == B) || (__return == 0 && A != B)) &&
      store_fp(a, A) * store_fp(b, B)
 */;

bool u32_eq_zero(const u32 *a)
/*@ base
    With A
    Require store_u256(a, A)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == 0) || (__return == 0 && A != 0)) &&
      store_u256(a, A)
 */
/*@ fp <= base
    With A
    Require store_fp(a, A)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == 0) || (__return == 0 && A != 0)) &&
      store_fp(a, A)
 */;

void pow_mod_p(const u32* x, u32* result)
/*@ non_alias With X
    Require store_fp(x, X) * UInt64Array::undef_full(&(result->v[0]), 4) * store_sm2_p * store_sm2_rhop
    Ensure store_fp(x, X) * store_fp(result, Zmod(X * X, SM2_P_Z)) * store_sm2_p * store_sm2_rhop
 */;

void mul_mod_p(const u32* x, const u32* y, u32* result)
/*@ non_alias With X Y
    Require store_fp(x, X) * store_fp(y, Y) * UInt64Array::undef_full(&(result->v[0]), 4) * store_sm2_p * store_sm2_rhop
    Ensure store_fp(x, X) * store_fp(y, Y) * store_fp(result, Zmod(X * Y, SM2_P_Z)) * store_sm2_p * store_sm2_rhop
 */
/*@ r_eq_a With X Y
    Require result == x && store_fp(x, X) * store_fp(y, Y) * store_sm2_p * store_sm2_rhop
    Ensure result == x && store_fp(result, Zmod(X * Y, SM2_P_Z)) * store_fp(y, Y) * store_sm2_p * store_sm2_rhop
 */
/*@ r_eq_b With X Y
    Require result == y && store_fp(x, X) * store_fp(y, Y) * store_sm2_p * store_sm2_rhop
    Ensure result == y && store_fp(x, X) * store_fp(result, Zmod(X * Y, SM2_P_Z)) * store_sm2_p * store_sm2_rhop
 */;

void add_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias With A B
    Require store_fp(a, A) * store_fp(b, B) * UInt64Array::undef_full(&(result->v[0]), 4) * store_sm2_p
    Ensure store_fp(a, A) * store_fp(b, B) * store_fp(result, Zmod(A + B, SM2_P_Z)) * store_sm2_p
 */
/*@ a_eq_b With A
    Require a == b && store_fp(a, A) * UInt64Array::undef_full(&(result->v[0]), 4) * store_sm2_p
    Ensure a == b && store_fp(a, A) * store_fp(result, Zmod(A + A, SM2_P_Z)) * store_sm2_p
 */;

void sub_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias With A B
    Require store_fp(a, A) * store_fp(b, B) * UInt64Array::undef_full(&(result->v[0]), 4) * store_sm2_p
    Ensure store_fp(a, A) * store_fp(b, B) * store_fp(result, Zmod(A - B, SM2_P_Z)) * store_sm2_p
 */
/*@ r_eq_b With A B
    Require result == b && store_fp(a, A) * store_fp(b, B) * store_sm2_p
    Ensure result == b && store_fp(a, A) * store_fp(result, Zmod(A - B, SM2_P_Z)) * store_sm2_p
 */;

void double_JPoint(const JPoint* pt, JPoint* result)
/*@ non_alias With P
    Require store_jpoint_with_canonical_infinity(pt,P) *
      UInt64Array::undef_full(field_addr(field_addr(result,JPoint,x),u32,v),4) *
      UInt64Array::undef_full(field_addr(field_addr(result,JPoint,y),u32,v),4) *
      UInt64Array::undef_full(field_addr(field_addr(result,JPoint,z),u32,v),4) *
      store_sm2_p * store_sm2_rhop
    Ensure store_jpoint_with_canonical_infinity(pt,P) *
      store_jpoint_with_canonical_infinity(result,sm2_point_double(P)) * store_sm2_p * store_sm2_rhop
 */
/*@ in_place With P
    Require result == pt &&
      store_jpoint_with_canonical_infinity(pt,P) * store_sm2_p * store_sm2_rhop
    Ensure result == pt &&
      store_jpoint_with_canonical_infinity(result,sm2_point_double(P)) * store_sm2_p * store_sm2_rhop
 */;

void add_JPoint(const JPoint* point1, const JPoint* point2, JPoint* result)
/*@ non_alias
    With (P1 P2 : ec_point)
    Require
      store_jpoint_with_canonical_infinity(point1,P1) *
      store_jpoint_with_canonical_infinity(point2,P2) *
      UInt64Array::undef_full(field_addr(field_addr(result,JPoint,x),u32,v),4) *
      UInt64Array::undef_full(field_addr(field_addr(result,JPoint,y),u32,v),4) *
      UInt64Array::undef_full(field_addr(field_addr(result,JPoint,z),u32,v),4) *
      store_jpoint_zero * store_sm2_inv2p *
      store_sm2_p * store_sm2_rhop
    Ensure
      store_jpoint_with_canonical_infinity(point1,P1) * store_jpoint_with_canonical_infinity(point2,P2) *
      store_jpoint_with_canonical_infinity(result,sm2_point_add(P1,P2)) *
      store_jpoint_zero * store_sm2_inv2p *
      store_sm2_p * store_sm2_rhop
 */
/*@ r_eq_point1
    With (P1 P2 : ec_point)
    Require result == point1 &&
      store_jpoint_with_canonical_infinity(point1,P1) * store_jpoint_with_canonical_infinity(point2,P2) *
      store_jpoint_zero * store_sm2_inv2p *
      store_sm2_p * store_sm2_rhop
    Ensure result == point1 &&
      store_jpoint_with_canonical_infinity(point2,P2) *
      store_jpoint_with_canonical_infinity(result,sm2_point_add(P1,P2)) *
      store_jpoint_zero * store_sm2_inv2p *
      store_sm2_p * store_sm2_rhop
 */
/*@ non_alias */
/*@ r_eq_point1 */
{
	/*@ do jpoint_undef_fields */
	/*@ do open_jpoint_zero */
	/*@ do open_sm2_inv2p */
	if (equ_to_JPoint_one(point1)
	    /*@ where (point) P = P1_non_alias $ non_alias
	        where (point) P = P1_r_eq_point1 $ r_eq_point1 */)
	{
		/*@ store_jpoint_with_canonical_infinity(point1,P1_non_alias) $ non_alias
		    which implies exists X1_non_alias Y1_non_alias Z1_non_alias,
		      jpoint_represents(X1_non_alias,Y1_non_alias,Z1_non_alias,P1_non_alias) &&
		      jpoint_canonical_infinity_encoding(X1_non_alias,Y1_non_alias,Z1_non_alias,P1_non_alias) &&
		      store_jpoint_fields(point1,X1_non_alias,Y1_non_alias,Z1_non_alias) */
		/*@ Given X1_non_alias Y1_non_alias Z1_non_alias $ non_alias */
		/*@ store_jpoint_with_canonical_infinity(point2,P2_non_alias) $ non_alias
		    which implies exists X2_non_alias Y2_non_alias Z2_non_alias,
		      jpoint_represents(X2_non_alias,Y2_non_alias,Z2_non_alias,P2_non_alias) &&
		      jpoint_canonical_infinity_encoding(X2_non_alias,Y2_non_alias,Z2_non_alias,P2_non_alias) &&
		      store_jpoint_fields(point2,X2_non_alias,Y2_non_alias,Z2_non_alias) */
		/*@ Given X2_non_alias Y2_non_alias Z2_non_alias $ non_alias */
		/*@ store_jpoint_with_canonical_infinity(point1,P1_r_eq_point1) $ r_eq_point1
		    which implies exists X1_r_eq_point1 Y1_r_eq_point1 Z1_r_eq_point1,
		      jpoint_represents(X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1,P1_r_eq_point1) &&
		      jpoint_canonical_infinity_encoding(X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1,P1_r_eq_point1) &&
		      store_jpoint_fields(point1,X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1) */
		/*@ Given X1_r_eq_point1 Y1_r_eq_point1 Z1_r_eq_point1 $ r_eq_point1 */
		/*@ store_jpoint_with_canonical_infinity(point2,P2_r_eq_point1) $ r_eq_point1
		    which implies exists X2_r_eq_point1 Y2_r_eq_point1 Z2_r_eq_point1,
		      jpoint_represents(X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1,P2_r_eq_point1) &&
		      jpoint_canonical_infinity_encoding(X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1,P2_r_eq_point1) &&
		      store_jpoint_fields(point2,X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1) */
		/*@ Given X2_r_eq_point1 Y2_r_eq_point1 Z2_r_eq_point1 $ r_eq_point1 */
		/*@ do jpoint_in_place_destination */
		/*@ store_jpoint_fields(point2,X2_non_alias,Y2_non_alias,Z2_non_alias) $ non_alias
		    which implies
		      exists copy_xs_non_alias copy_ys_non_alias copy_zs_non_alias,
		        Zlength(copy_xs_non_alias) == 4 && u64_list_bounded(copy_xs_non_alias) &&
		        u64_list_value(copy_xs_non_alias) == X2_non_alias &&
		        Zlength(copy_ys_non_alias) == 4 && u64_list_bounded(copy_ys_non_alias) &&
		        u64_list_value(copy_ys_non_alias) == Y2_non_alias &&
		        Zlength(copy_zs_non_alias) == 4 && u64_list_bounded(copy_zs_non_alias) &&
		        u64_list_value(copy_zs_non_alias) == Z2_non_alias &&
		        UInt64Array::full(&(point2->x.v[0]),4,copy_xs_non_alias) *
		        UInt64Array::full(&(point2->y.v[0]),4,copy_ys_non_alias) *
		        UInt64Array::full(&(point2->z.v[0]),4,copy_zs_non_alias)
		    by materialize_jpoint_record
		 */
		/*@ store_jpoint_fields(point2,X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1) $ r_eq_point1
		    which implies
		      exists copy_xs_r_eq_point1 copy_ys_r_eq_point1 copy_zs_r_eq_point1,
		        Zlength(copy_xs_r_eq_point1) == 4 && u64_list_bounded(copy_xs_r_eq_point1) &&
		        u64_list_value(copy_xs_r_eq_point1) == X2_r_eq_point1 &&
		        Zlength(copy_ys_r_eq_point1) == 4 && u64_list_bounded(copy_ys_r_eq_point1) &&
		        u64_list_value(copy_ys_r_eq_point1) == Y2_r_eq_point1 &&
		        Zlength(copy_zs_r_eq_point1) == 4 && u64_list_bounded(copy_zs_r_eq_point1) &&
		        u64_list_value(copy_zs_r_eq_point1) == Z2_r_eq_point1 &&
		        UInt64Array::full(&(point2->x.v[0]),4,copy_xs_r_eq_point1) *
		        UInt64Array::full(&(point2->y.v[0]),4,copy_ys_r_eq_point1) *
		        UInt64Array::full(&(point2->z.v[0]),4,copy_zs_r_eq_point1)
		    by materialize_jpoint_record
		 */
		*result = *point2;
		/*@ do aj_inf_left */
		return;
	}
	if (equ_to_JPoint_one(point2)
	    /*@ where (point) P = P2_non_alias $ non_alias
	        where (point) P = P2_r_eq_point1 $ r_eq_point1 */)
	{
		/*@ store_jpoint_with_canonical_infinity(point1,P1_non_alias) $ non_alias
		    which implies exists X1_non_alias Y1_non_alias Z1_non_alias,
		      jpoint_represents(X1_non_alias,Y1_non_alias,Z1_non_alias,P1_non_alias) &&
		      jpoint_canonical_infinity_encoding(X1_non_alias,Y1_non_alias,Z1_non_alias,P1_non_alias) &&
		      store_jpoint_fields(point1,X1_non_alias,Y1_non_alias,Z1_non_alias) */
		/*@ Given X1_non_alias Y1_non_alias Z1_non_alias $ non_alias */
		/*@ store_jpoint_with_canonical_infinity(point2,P2_non_alias) $ non_alias
		    which implies exists X2_non_alias Y2_non_alias Z2_non_alias,
		      jpoint_represents(X2_non_alias,Y2_non_alias,Z2_non_alias,P2_non_alias) &&
		      jpoint_canonical_infinity_encoding(X2_non_alias,Y2_non_alias,Z2_non_alias,P2_non_alias) &&
		      store_jpoint_fields(point2,X2_non_alias,Y2_non_alias,Z2_non_alias) */
		/*@ Given X2_non_alias Y2_non_alias Z2_non_alias $ non_alias */
		/*@ store_jpoint_with_canonical_infinity(point1,P1_r_eq_point1) $ r_eq_point1
		    which implies exists X1_r_eq_point1 Y1_r_eq_point1 Z1_r_eq_point1,
		      jpoint_represents(X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1,P1_r_eq_point1) &&
		      jpoint_canonical_infinity_encoding(X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1,P1_r_eq_point1) &&
		      store_jpoint_fields(point1,X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1) */
		/*@ Given X1_r_eq_point1 Y1_r_eq_point1 Z1_r_eq_point1 $ r_eq_point1 */
		/*@ store_jpoint_with_canonical_infinity(point2,P2_r_eq_point1) $ r_eq_point1
		    which implies exists X2_r_eq_point1 Y2_r_eq_point1 Z2_r_eq_point1,
		      jpoint_represents(X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1,P2_r_eq_point1) &&
		      jpoint_canonical_infinity_encoding(X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1,P2_r_eq_point1) &&
		      store_jpoint_fields(point2,X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1) */
		/*@ Given X2_r_eq_point1 Y2_r_eq_point1 Z2_r_eq_point1 $ r_eq_point1 */
		/*@ store_jpoint_fields(point1,X1_non_alias,Y1_non_alias,Z1_non_alias) $ non_alias
			    which implies
			      exists copy_xs_non_alias copy_ys_non_alias copy_zs_non_alias,
			        Zlength(copy_xs_non_alias) == 4 && u64_list_bounded(copy_xs_non_alias) &&
			        u64_list_value(copy_xs_non_alias) == X1_non_alias &&
			        Zlength(copy_ys_non_alias) == 4 && u64_list_bounded(copy_ys_non_alias) &&
			        u64_list_value(copy_ys_non_alias) == Y1_non_alias &&
			        Zlength(copy_zs_non_alias) == 4 && u64_list_bounded(copy_zs_non_alias) &&
			        u64_list_value(copy_zs_non_alias) == Z1_non_alias &&
			        UInt64Array::full(&(point1->x.v[0]),4,copy_xs_non_alias) *
			        UInt64Array::full(&(point1->y.v[0]),4,copy_ys_non_alias) *
			        UInt64Array::full(&(point1->z.v[0]),4,copy_zs_non_alias)
			    by materialize_jpoint_record
		 */
		*result = *point1;
		/*@ do aj_inf_right */
		return;
	}
	/*@ store_jpoint_with_canonical_infinity(point1,P1_non_alias) $ non_alias
	    which implies exists X1_non_alias Y1_non_alias Z1_non_alias,
	      jpoint_represents(X1_non_alias,Y1_non_alias,Z1_non_alias,P1_non_alias) &&
	      jpoint_canonical_infinity_encoding(X1_non_alias,Y1_non_alias,Z1_non_alias,P1_non_alias) &&
	      store_jpoint_fields(point1,X1_non_alias,Y1_non_alias,Z1_non_alias) */
	/*@ Given X1_non_alias Y1_non_alias Z1_non_alias $ non_alias */
	/*@ store_jpoint_with_canonical_infinity(point2,P2_non_alias) $ non_alias
	    which implies exists X2_non_alias Y2_non_alias Z2_non_alias,
	      jpoint_represents(X2_non_alias,Y2_non_alias,Z2_non_alias,P2_non_alias) &&
	      jpoint_canonical_infinity_encoding(X2_non_alias,Y2_non_alias,Z2_non_alias,P2_non_alias) &&
	      store_jpoint_fields(point2,X2_non_alias,Y2_non_alias,Z2_non_alias) */
	/*@ Given X2_non_alias Y2_non_alias Z2_non_alias $ non_alias */
	/*@ store_jpoint_with_canonical_infinity(point1,P1_r_eq_point1) $ r_eq_point1
	    which implies exists X1_r_eq_point1 Y1_r_eq_point1 Z1_r_eq_point1,
	      jpoint_represents(X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1,P1_r_eq_point1) &&
	      jpoint_canonical_infinity_encoding(X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1,P1_r_eq_point1) &&
	      store_jpoint_fields(point1,X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1) */
	/*@ Given X1_r_eq_point1 Y1_r_eq_point1 Z1_r_eq_point1 $ r_eq_point1 */
	/*@ store_jpoint_with_canonical_infinity(point2,P2_r_eq_point1) $ r_eq_point1
	    which implies exists X2_r_eq_point1 Y2_r_eq_point1 Z2_r_eq_point1,
	      jpoint_represents(X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1,P2_r_eq_point1) &&
	      jpoint_canonical_infinity_encoding(X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1,P2_r_eq_point1) &&
	      store_jpoint_fields(point2,X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1) */
	/*@ Given X2_r_eq_point1 Y2_r_eq_point1 Z2_r_eq_point1 $ r_eq_point1 */
	/*@ do finite_jpoint_coordinates */
	/*@ do open_jpoint_fields */

	u32 pz2, qz2, pz3, qz3, lambda1, lambda2;
	pow_mod_p(&point1->z, &pz2) /*@ where (non_alias) X = Z1_non_alias $ non_alias
    where (non_alias) X = Z1_r_eq_point1 $ r_eq_point1 */;
	/*@ do aj_pz2_step */
	pow_mod_p(&point2->z, &qz2) /*@ where (non_alias) X = Z2_non_alias $ non_alias
    where (non_alias) X = Z2_r_eq_point1 $ r_eq_point1 */;
	/*@ do aj_qz2_step */
	mul_mod_p(&pz2, &point1->z, &pz3) /*@ where (non_alias) X = aj_pz2(Z1_non_alias), Y = Z1_non_alias $ non_alias
    where (non_alias) X = aj_pz2(Z1_r_eq_point1), Y = Z1_r_eq_point1 $ r_eq_point1 */;
	/*@ do aj_trace_step */
	mul_mod_p(&qz2, &point2->z, &qz3) /*@ where (non_alias) X = aj_qz2(Z2_non_alias), Y = Z2_non_alias $ non_alias
    where (non_alias) X = aj_qz2(Z2_r_eq_point1), Y = Z2_r_eq_point1 $ r_eq_point1 */;
	/*@ do aj_trace_step */
	mul_mod_p(&point1->x, &qz2, &lambda1) /*@ where (non_alias) X = X1_non_alias, Y = aj_qz2(Z2_non_alias) $ non_alias
    where (non_alias) X = X1_r_eq_point1, Y = aj_qz2(Z2_r_eq_point1) $ r_eq_point1 */;
	/*@ do aj_trace_step */
	mul_mod_p(&point2->x, &pz2, &lambda2) /*@ where (non_alias) X = X2_non_alias, Y = aj_pz2(Z1_non_alias) $ non_alias
    where (non_alias) X = X2_r_eq_point1, Y = aj_pz2(Z1_r_eq_point1) $ r_eq_point1 */;
	/*@ do aj_trace_step */

	u32 lambda4, lambda5;
	mul_mod_p(&point1->y, &qz3, &lambda4) /*@ where (non_alias) X = Y1_non_alias, Y = aj_qz3(Z2_non_alias) $ non_alias
    where (non_alias) X = Y1_r_eq_point1, Y = aj_qz3(Z2_r_eq_point1) $ r_eq_point1 */;
	/*@ do aj_trace_step */
	mul_mod_p(&point2->y, &pz3, &lambda5) /*@ where (non_alias) X = Y2_non_alias, Y = aj_pz3(Z1_non_alias) $ non_alias
    where (non_alias) X = Y2_r_eq_point1, Y = aj_pz3(Z1_r_eq_point1) $ r_eq_point1 */;
	/*@ do aj_trace_step */
	if (u32_eq(&lambda1, &lambda2) /*@ where (fp) A = aj_u1(X1_non_alias,Z2_non_alias), B = aj_u2(X2_non_alias,Z1_non_alias) $ non_alias
    where (fp) A = aj_u1(X1_r_eq_point1,Z2_r_eq_point1), B = aj_u2(X2_r_eq_point1,Z1_r_eq_point1) $ r_eq_point1 */ &&
	    u32_eq(&lambda4, &lambda5) /*@ where (fp) A = aj_s1(Y1_non_alias,Z2_non_alias), B = aj_s2(Y2_non_alias,Z1_non_alias) $ non_alias
    where (fp) A = aj_s1(Y1_r_eq_point1,Z2_r_eq_point1), B = aj_s2(Y2_r_eq_point1,Z1_r_eq_point1) $ r_eq_point1 */)
	{
		double_JPoint(point1, result)
		/*@ where (non_alias) P = P1_non_alias $ non_alias
		    where (in_place) P = P1_r_eq_point1 $ r_eq_point1 */;
	}
	else
	{
		u32 lambda3, lambda6, lambda7, lambda8, l6l6, l7l3l3, x, lambda9, l9l6, l8l3l3, l8l3l3l3;
		add_mod_p(&lambda4, &lambda5, &lambda8) /*@ where (non_alias) A = aj_s1(Y1_non_alias,Z2_non_alias), B = aj_s2(Y2_non_alias,Z1_non_alias) $ non_alias
    where (non_alias) A = aj_s1(Y1_r_eq_point1,Z2_r_eq_point1), B = aj_s2(Y2_r_eq_point1,Z1_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */
		if (u32_eq(&lambda1, &lambda2) /*@ where (fp) A = aj_u1(X1_non_alias,Z2_non_alias), B = aj_u2(X2_non_alias,Z1_non_alias) $ non_alias
    where (fp) A = aj_u1(X1_r_eq_point1,Z2_r_eq_point1), B = aj_u2(X2_r_eq_point1,Z1_r_eq_point1) $ r_eq_point1 */ &&
		    u32_eq_zero(&lambda8) /*@ where (fp) A = aj_s_sum(Y1_non_alias,Z1_non_alias,Y2_non_alias,Z2_non_alias) $ non_alias
    where (fp) A = aj_s_sum(Y1_r_eq_point1,Z1_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1) $ r_eq_point1 */)
		{
			/*@ store_jpoint_fields(&JPoint_ZERO,1,1,0) $ non_alias which implies
			      exists copy_xs_non_alias copy_ys_non_alias copy_zs_non_alias,
			        Zlength(copy_xs_non_alias) == 4 && u64_list_bounded(copy_xs_non_alias) &&
			        u64_list_value(copy_xs_non_alias) == 1 &&
			        Zlength(copy_ys_non_alias) == 4 && u64_list_bounded(copy_ys_non_alias) &&
			        u64_list_value(copy_ys_non_alias) == 1 &&
			        Zlength(copy_zs_non_alias) == 4 && u64_list_bounded(copy_zs_non_alias) &&
			        u64_list_value(copy_zs_non_alias) == 0 &&
			        UInt64Array::full(&(JPoint_ZERO.x.v[0]),4,copy_xs_non_alias) *
			        UInt64Array::full(&(JPoint_ZERO.y.v[0]),4,copy_ys_non_alias) *
			        UInt64Array::full(&(JPoint_ZERO.z.v[0]),4,copy_zs_non_alias)
			    by materialize_jpoint_record
			 */
/*@ store_jpoint_fields(&JPoint_ZERO,1,1,0) $ r_eq_point1 which implies
			      exists copy_xs_r_eq_point1 copy_ys_r_eq_point1 copy_zs_r_eq_point1,
			        Zlength(copy_xs_r_eq_point1) == 4 && u64_list_bounded(copy_xs_r_eq_point1) &&
			        u64_list_value(copy_xs_r_eq_point1) == 1 &&
			        Zlength(copy_ys_r_eq_point1) == 4 && u64_list_bounded(copy_ys_r_eq_point1) &&
			        u64_list_value(copy_ys_r_eq_point1) == 1 &&
			        Zlength(copy_zs_r_eq_point1) == 4 && u64_list_bounded(copy_zs_r_eq_point1) &&
			        u64_list_value(copy_zs_r_eq_point1) == 0 &&
			        UInt64Array::full(&(JPoint_ZERO.x.v[0]),4,copy_xs_r_eq_point1) *
			        UInt64Array::full(&(JPoint_ZERO.y.v[0]),4,copy_ys_r_eq_point1) *
			        UInt64Array::full(&(JPoint_ZERO.z.v[0]),4,copy_zs_r_eq_point1)
			    by materialize_jpoint_record
			 */
			/*@ do jpoint_in_place_destination */
			*result = JPoint_ZERO;
			return;
		}
		/*@ aj_generic_trace_case(X1_non_alias,Y1_non_alias,Z1_non_alias,
		                            X2_non_alias,Y2_non_alias,Z2_non_alias)
		    $ non_alias
		 */
		/*@ aj_generic_trace_case(X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1,
		                            X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1)
		    $ r_eq_point1
		 */
		sub_mod_p(&lambda1, &lambda2, &lambda3) /*@ where (non_alias) A = aj_u1(X1_non_alias,Z2_non_alias), B = aj_u2(X2_non_alias,Z1_non_alias) $ non_alias
    where (non_alias) A = aj_u1(X1_r_eq_point1,Z2_r_eq_point1), B = aj_u2(X2_r_eq_point1,Z1_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */
		sub_mod_p(&lambda4, &lambda5, &lambda6) /*@ where (non_alias) A = aj_s1(Y1_non_alias,Z2_non_alias), B = aj_s2(Y2_non_alias,Z1_non_alias) $ non_alias
    where (non_alias) A = aj_s1(Y1_r_eq_point1,Z2_r_eq_point1), B = aj_s2(Y2_r_eq_point1,Z1_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */
		add_mod_p(&lambda1, &lambda2, &lambda7) /*@ where (non_alias) A = aj_u1(X1_non_alias,Z2_non_alias), B = aj_u2(X2_non_alias,Z1_non_alias) $ non_alias
    where (non_alias) A = aj_u1(X1_r_eq_point1,Z2_r_eq_point1), B = aj_u2(X2_r_eq_point1,Z1_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */
		pow_mod_p(&lambda6, &l6l6) /*@ where (non_alias) X = aj_rr(Y1_non_alias,Z1_non_alias,Y2_non_alias,Z2_non_alias) $ non_alias
    where (non_alias) X = aj_rr(Y1_r_eq_point1,Z1_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */
		pow_mod_p(&lambda3, &l7l3l3) /*@ where (non_alias) X = aj_h(X1_non_alias,Z1_non_alias,X2_non_alias,Z2_non_alias) $ non_alias
    where (non_alias) X = aj_h(X1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Z2_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */
		mul_mod_p(&lambda7, &l7l3l3, &l7l3l3) /*@ where (r_eq_b) X = aj_u_sum(X1_non_alias,Z1_non_alias,X2_non_alias,Z2_non_alias), Y = aj_h2(X1_non_alias,Z1_non_alias,X2_non_alias,Z2_non_alias) $ non_alias
    where (r_eq_b) X = aj_u_sum(X1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Z2_r_eq_point1), Y = aj_h2(X1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Z2_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */
		sub_mod_p(&l6l6, &l7l3l3, &x) /*@ where (non_alias) A = aj_rr2(Y1_non_alias,Z1_non_alias,Y2_non_alias,Z2_non_alias), B = aj_base(X1_non_alias,Z1_non_alias,X2_non_alias,Z2_non_alias) $ non_alias
    where (non_alias) A = aj_rr2(Y1_r_eq_point1,Z1_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1), B = aj_base(X1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Z2_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */
		add_mod_p(&x, &x, &lambda9) /*@ where (a_eq_b) A = aj_rx(X1_non_alias,Y1_non_alias,Z1_non_alias,X2_non_alias,Y2_non_alias,Z2_non_alias) $ non_alias
    where (a_eq_b) A = aj_rx(X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */
		sub_mod_p(&l7l3l3, &lambda9, &lambda9) /*@ where (r_eq_b) A = aj_base(X1_non_alias,Z1_non_alias,X2_non_alias,Z2_non_alias), B = aj_twice_rx(X1_non_alias,Y1_non_alias,Z1_non_alias,X2_non_alias,Y2_non_alias,Z2_non_alias) $ non_alias
    where (r_eq_b) A = aj_base(X1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Z2_r_eq_point1), B = aj_twice_rx(X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */
		mul_mod_p(&lambda9, &lambda6, &l9l6) /*@ where (non_alias) X = aj_base_minus_twice_rx(X1_non_alias,Y1_non_alias,Z1_non_alias,X2_non_alias,Y2_non_alias,Z2_non_alias), Y = aj_rr(Y1_non_alias,Z1_non_alias,Y2_non_alias,Z2_non_alias) $ non_alias
    where (non_alias) X = aj_base_minus_twice_rx(X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1), Y = aj_rr(Y1_r_eq_point1,Z1_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */
		pow_mod_p(&lambda3, &l8l3l3) /*@ where (non_alias) X = aj_h(X1_non_alias,Z1_non_alias,X2_non_alias,Z2_non_alias) $ non_alias
    where (non_alias) X = aj_h(X1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Z2_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */
		mul_mod_p(&lambda8, &l8l3l3, &l8l3l3) /*@ where (r_eq_b) X = aj_s_sum(Y1_non_alias,Z1_non_alias,Y2_non_alias,Z2_non_alias), Y = aj_h2(X1_non_alias,Z1_non_alias,X2_non_alias,Z2_non_alias) $ non_alias
    where (r_eq_b) X = aj_s_sum(Y1_r_eq_point1,Z1_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1), Y = aj_h2(X1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Z2_r_eq_point1) $ r_eq_point1 */;
		mul_mod_p(&l8l3l3, &lambda3, &l8l3l3l3) /*@ where (non_alias) X = Zmod(aj_s_sum(Y1_non_alias,Z1_non_alias,Y2_non_alias,Z2_non_alias) * aj_h2(X1_non_alias,Z1_non_alias,X2_non_alias,Z2_non_alias), SM2_P_Z), Y = aj_h(X1_non_alias,Z1_non_alias,X2_non_alias,Z2_non_alias) $ non_alias
    where (non_alias) X = Zmod(aj_s_sum(Y1_r_eq_point1,Z1_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1) * aj_h2(X1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Z2_r_eq_point1), SM2_P_Z), Y = aj_h(X1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Z2_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */

		u32 y, z;
		sub_mod_p(&l9l6, &l8l3l3l3, &y) /*@ where (non_alias) A = aj_left_y(X1_non_alias,Y1_non_alias,Z1_non_alias,X2_non_alias,Y2_non_alias,Z2_non_alias), B = aj_right_y(X1_non_alias,Y1_non_alias,Z1_non_alias,X2_non_alias,Y2_non_alias,Z2_non_alias) $ non_alias
    where (non_alias) A = aj_left_y(X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1), B = aj_right_y(X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */
		mul_mod_p(&y, &SM2_inv2P, &y) /*@ where (r_eq_a) X = aj_y_num(X1_non_alias,Y1_non_alias,Z1_non_alias,X2_non_alias,Y2_non_alias,Z2_non_alias), Y = SM2_P_INV2_Z $ non_alias
    where (r_eq_a) X = aj_y_num(X1_r_eq_point1,Y1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Y2_r_eq_point1,Z2_r_eq_point1), Y = SM2_P_INV2_Z $ r_eq_point1 */;
		/*@ do aj_trace_step */
		mul_mod_p(&point1->z, &point2->z, &z) /*@ where (non_alias) X = Z1_non_alias, Y = Z2_non_alias $ non_alias
    where (non_alias) X = Z1_r_eq_point1, Y = Z2_r_eq_point1 $ r_eq_point1 */;
		/*@ do aj_zbase_step */
		mul_mod_p(&z, &lambda3, &z) /*@ where (r_eq_a) X = aj_zbase(Z1_non_alias,Z2_non_alias), Y = aj_h(X1_non_alias,Z1_non_alias,X2_non_alias,Z2_non_alias) $ non_alias
    where (r_eq_a) X = aj_zbase(Z1_r_eq_point1,Z2_r_eq_point1), Y = aj_h(X1_r_eq_point1,Z1_r_eq_point1,X2_r_eq_point1,Z2_r_eq_point1) $ r_eq_point1 */;
		/*@ do aj_trace_step */
		/*@ do aj_rx_materialize */
		/*@ do aj_ry_materialize */
		/*@ do aj_rz_materialize */
		/*@ do jpoint_in_place_destination */
		/*@ do jpoint_undef_to_fields */
		result->x = x;
		result->y = y;
		result->z = z;
	}
}
