/* Verification copy of YCrypt/sm2/ecc.c::add_JPoint_and_AFPoint. */

#include "../include/ecc.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */
/*@ include strategies "../strategy/ecc_point_copy_steps.strategies" */
/*@ Import Coq Require Import
      SimpleC.EE.Applications_human.sm2.lib.add_JPoint_and_AFPoint_lib
 */
/*@ Extern Coq
      (store_mixed_add_result_impl :
        Z -> ec_point -> ec_point -> Assertion)
 */

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

bool equ_to_AFPoint_one(const AFPoint* point)
/*@ base
    With X Y
    Require
      store_afpoint_fields(point, X, Y)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && X == 0 && Y == 0) ||
       (__return == 0 && (X != 0 || Y != 0))) &&
      store_afpoint_fields(point, X, Y)
 */
/*@ point
    With (P : ec_point)
    Require
      store_afpoint(point, P)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && P == ECInfinity) ||
       (__return == 0 && P != ECInfinity)) &&
      store_afpoint(point, P)
 */;

void affine_to_jacobian(const AFPoint* point, JPoint* result)
/*@ non_alias
    With X Y
    Require
      store_afpoint_fields(point, X, Y) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_jpoint_zero
    Ensure
      exists RX RY RZ,
        afpoint_to_jpoint_coordinates(X, Y, RX, RY, RZ) &&
        store_afpoint_fields(point, X, Y) *
        store_jpoint_fields(result, RX, RY, RZ) *
        store_jpoint_zero
 */;

void affine_to_jacobian(const AFPoint* point, JPoint* result)
/*@ point_non_alias <= non_alias
    With (P : ec_point)
    Require
      store_afpoint(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_jpoint_zero
    Ensure
      store_afpoint(point, P) *
      store_jpoint_with_canonical_infinity(result, P) *
      store_jpoint_zero
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
/*@ r_eq_x
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
 */;

void add_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ a_eq_b
    With A
    Require
      a == b &&
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      a == b &&
      store_fp(a, A) *
      store_fp(result, Zmod(A + A, SM2_P_Z)) *
      store_sm2_p
 */;

void sub_mod_p(const u32 *a, const u32 *b, u32 *result)
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
      store_fp(result, Zmod(A - B, SM2_P_Z)) *
      store_sm2_p
 */
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
 */;

// Note: this function should
// ALWAYS be called with different point
void add_JPoint_and_AFPoint(
    const JPoint* point1, const AFPoint* point2, JPoint* result)
/*@ impl_non_alias
    With (P1 P2 : ec_point)
    Require
      ((P1 != ECInfinity && P2 != ECInfinity) => P1 != P2) &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
    Ensure
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      store_mixed_add_result_impl(result, P1, P2) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
 */
/*@ impl_r_eq_point1
    With (P1 P2 : ec_point)
    Require
      result == point1 &&
      ((P1 != ECInfinity && P2 != ECInfinity) => P1 != P2) &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
    Ensure
      result == point1 &&
      store_mixed_add_result_impl(result, P1, P2) *
      store_afpoint(point2, P2) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
 */
;

void add_JPoint_and_AFPoint(
    const JPoint* point1, const AFPoint* point2, JPoint* result)
/*@ non_alias <= impl_non_alias
    With (P1 P2 : ec_point)
    Require
      ((P1 != ECInfinity && P2 != ECInfinity) => P1 != P2) &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
    Ensure
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      store_jpoint(result, sm2_point_add(P1, P2)) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
 */
;

void add_JPoint_and_AFPoint(
    const JPoint* point1, const AFPoint* point2, JPoint* result)
/*@ canonical_non_alias <= impl_non_alias
    With (P1 P2 : ec_point)
    Require
      ((P1 != ECInfinity && P2 != ECInfinity) => P1 != P2) &&
      (P1 == ECInfinity || P2 == ECInfinity ||
       sm2_point_add(P1, P2) != ECInfinity) &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
    Ensure
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      store_jpoint_with_canonical_infinity(
        result, sm2_point_add(P1, P2)) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
 */
;

void add_JPoint_and_AFPoint(
    const JPoint* point1, const AFPoint* point2, JPoint* result)
/*@ r_eq_point1 <= impl_r_eq_point1
    With (P1 P2 : ec_point)
    Require
      result == point1 &&
      ((P1 != ECInfinity && P2 != ECInfinity) => P1 != P2) &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
    Ensure
      result == point1 &&
      store_jpoint(result, sm2_point_add(P1, P2)) *
      store_afpoint(point2, P2) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
 */
;

void add_JPoint_and_AFPoint(
    const JPoint* point1, const AFPoint* point2, JPoint* result)
/*@ canonical_r_eq_point1 <= impl_r_eq_point1
    With (P1 P2 : ec_point)
    Require
      result == point1 &&
      ((P1 != ECInfinity && P2 != ECInfinity) => P1 != P2) &&
      (P1 == ECInfinity || P2 == ECInfinity ||
       sm2_point_add(P1, P2) != ECInfinity) &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
    Ensure
      result == point1 &&
      store_jpoint_with_canonical_infinity(
        result, sm2_point_add(P1, P2)) *
      store_afpoint(point2, P2) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
 */
;

void add_JPoint_and_AFPoint(
    const JPoint* point1, const AFPoint* point2, JPoint* result)
/*@ impl_non_alias */
/*@ impl_r_eq_point1 */
{
	if (equ_to_JPoint_one(point1)
	    /*@ where (point) P = P1_impl_non_alias $ impl_non_alias
	        where (point) P = P1_impl_r_eq_point1 $ impl_r_eq_point1 */)
	{
		/*@ do open_jpoint_canonical */
		/*@ do jpoint_in_place_destination */
		/*@ do jpoint_undef_to_fields */
		affine_to_jacobian(point2, result)
		/*@
		  where (point_non_alias) P = P2_impl_non_alias
		    $ impl_non_alias
		  where (point_non_alias) P = P2_impl_r_eq_point1
		    $ impl_r_eq_point1
		 */;
		return;
	}

	if (equ_to_AFPoint_one(point2)
	    /*@ where (point) P = P2_impl_non_alias $ impl_non_alias
	        where (point) P = P2_impl_r_eq_point1 $ impl_r_eq_point1 */)
	{
			/*@
				  store_jpoint_with_canonical_infinity(
				    point1, P1_impl_non_alias) *
				  UInt64Array::undef_full(&(result->x.v[0]), 4) *
				  UInt64Array::undef_full(&(result->y.v[0]), 4) *
				  UInt64Array::undef_full(&(result->z.v[0]), 4)
				  $ impl_non_alias
				  which implies
				  exists JX JY JZ,
				  exists (x_limbs y_limbs z_limbs : list Z),
				    jpoint_represents(
				      JX, JY, JZ, P1_impl_non_alias) &&
				    jpoint_canonical_infinity_encoding(
				      JX, JY, JZ, P1_impl_non_alias) &&
				    Zlength(x_limbs) == 4 &&
				    u64_list_bounded(x_limbs) &&
				    u64_list_value(x_limbs) == JX &&
				    Zlength(y_limbs) == 4 &&
				    u64_list_bounded(y_limbs) &&
				    u64_list_value(y_limbs) == JY &&
				    Zlength(z_limbs) == 4 &&
				    u64_list_bounded(z_limbs) &&
				    u64_list_value(z_limbs) == JZ &&
				    StructPredJPoint(
				      point1,
				      make_record_jpoint(
				        make_record_u32(x_limbs),
				        make_record_u32(y_limbs),
				        make_record_u32(z_limbs))) *
				    UndefStructPredJPoint(result)
			 */
			*result = *point1;
		return;
	}

	/*@ do open_jpoint_canonical */
	/*@ do open_afpoint */
	u32 z2, A, B, C2, C3, X1C2, D2, X1C22, tmp;
	pow_mod_p(&point1->z, &z2);
	mul_mod_p(&point2->x, &z2, &A)
	/*@ where (non_alias) $ impl_non_alias impl_r_eq_point1 */;
	mul_mod_p(&point2->y, &z2, &B)
	/*@ where (non_alias) $ impl_non_alias impl_r_eq_point1 */;
	mul_mod_p(&B, &point1->z, &B)
	/*@
	  where (r_eq_x) $ impl_non_alias
	  where (r_eq_x) $ impl_r_eq_point1
	 */;

	sub_mod_p(&A, &point1->x, &A)
	/*@
	  where (r_eq_a) $ impl_non_alias
	  where (r_eq_a) $ impl_r_eq_point1
	 */;
		sub_mod_p(&B, &point1->y, &B)
		/*@
		  where (r_eq_a) $ impl_non_alias
		  where (r_eq_a) $ impl_r_eq_point1
		 */;


		pow_mod_p(&A, &C2);
	mul_mod_p(&C2, &A, &C3)
	/*@ where (non_alias) $ impl_non_alias impl_r_eq_point1 */;
		mul_mod_p(&point1->x, &C2, &X1C2)
		/*@ where (non_alias) $ impl_non_alias impl_r_eq_point1 */;
		pow_mod_p(&B, &D2);


		add_mod_p(&X1C2, &X1C2, &X1C22)
	/*@
	  where (a_eq_b) $ impl_non_alias
	  where (a_eq_b) $ impl_r_eq_point1
	 */;
	sub_mod_p(&D2, &X1C22, &result->x)
	/*@ where (non_alias) $ impl_non_alias impl_r_eq_point1 */;
	sub_mod_p(&result->x, &C3, &result->x)
	/*@
	  where (r_eq_a) $ impl_non_alias
	  where (r_eq_a) $ impl_r_eq_point1
	 */;
		sub_mod_p(&X1C2, &result->x, &tmp)
		/*@ where (non_alias) $ impl_non_alias impl_r_eq_point1 */;


		mul_mod_p(&B, &tmp, &B)
	/*@
	  where (r_eq_x) $ impl_non_alias
	  where (r_eq_x) $ impl_r_eq_point1
	 */;
	mul_mod_p(&point1->y, &C3, &tmp)
	/*@ where (non_alias) $ impl_non_alias impl_r_eq_point1 */;
	sub_mod_p(&B, &tmp, &result->y)
	/*@ where (non_alias) $ impl_non_alias impl_r_eq_point1 */;

	mul_mod_p(&point1->z, &A, &result->z)
	/*@
	  where (non_alias) $ impl_non_alias
	  where (r_eq_x) $ impl_r_eq_point1
	 */;
}
