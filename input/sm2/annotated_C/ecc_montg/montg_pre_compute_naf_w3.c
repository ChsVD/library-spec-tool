/* Verification copy of YCrypt/sm2/ecc_montg.c::montg_pre_compute_naf_w3. */

#include "../include/ecc.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_point_copy_steps.strategies" */
/*@ include strategies "../strategy/ecc_point_overwrite.strategies" */
/*@ include strategies "../strategy/wnaf3_precomp_points.strategies" */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.sm2.lib.sm2_no_three_torsion */

int montg_apoint_to_montg(const AFPoint* a, AFPoint* result)
/*@ non_alias
    With X Y
    Require
      store_afpoint_fields(a, X, Y) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      __return == 1 &&
      store_afpoint_fields(a, X, Y) *
      store_mont_afpoint_coords(result, X, Y) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop
 */;

int montg_apoint_to_montg(const AFPoint* a, AFPoint* result)
/*@ point_non_alias
    With (P : ec_point)
    Require
      store_afpoint(a, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      __return == 1 &&
      store_afpoint(a, P) *
      store_mont_afpoint(result, P) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop
 */;

void AFPoint_neg(const AFPoint* point, AFPoint* result)
/*@ non_alias
    With X Y
    Require
      Y != 0 &&
      store_afpoint_fields(point, X, Y) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_sm2_p
    Ensure
      store_afpoint_fields(point, X, Y) *
      store_afpoint_fields(result, X, Zmod(-Y, SM2_P_Z)) *
      store_sm2_p
 */;

void AFPoint_neg(const AFPoint* point, AFPoint* result)
/*@ mont_point_non_alias
    With (P : ec_point)
    Require
      P != ECInfinity &&
      store_mont_afpoint(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_sm2_p
    Ensure
      store_mont_afpoint(point, P) *
      store_mont_afpoint(result, sm2_point_negate(P)) *
      store_sm2_p
 */;

int montg_apoint_to_jpoint2(const AFPoint* point, JPoint* result)
/*@ non_alias
    With X Y
    Require
      store_mont_afpoint_coords(point, X, Y) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_bn_zero *
      store_montg_one
    Ensure
      exists RX RY RZ,
        __return == 1 &&
        ((X == 0 && Y == 0 &&
          RX == 1 && RY == 1 && RZ == 0) ||
         ((X != 0 || Y != 0) &&
          RX == X && RY == Y && RZ == 1)) &&
        store_mont_afpoint_coords(point, X, Y) *
        store_mont_jpoint_coords(result, RX, RY, RZ) *
        store_bn_zero *
        store_montg_one
 */;

int montg_apoint_to_jpoint2(const AFPoint* point, JPoint* result)
/*@ point_non_alias
    With (P : ec_point)
    Require
      store_mont_afpoint(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_bn_zero *
      store_montg_one
    Ensure
      __return == 1 &&
      store_mont_afpoint(point, P) *
      store_mont_jpoint(result, P) *
      store_bn_zero *
      store_montg_one
 */;

void montg_double_jpoint_ex(const JPoint* point, JPoint* result)
/*@ non_alias
    With (P : ec_point)
    Require
      store_mont_jpoint(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_mont_jpoint(point, P) *
      store_mont_jpoint(result, sm2_point_double(P)) *
      store_sm2_p *
      store_sm2_rhop
 */;

void montg_add_jpoint_and_apoint_ex(
    const JPoint* a, const AFPoint* b, JPoint* result)
/*@ non_alias
    With (P1 P2 : ec_point)
    Require
      store_mont_jpoint(a, P1) *
      store_mont_afpoint(b, P2) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_bn_zero *
      store_montg_one *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_mont_jpoint(a, P1) *
      store_mont_afpoint(b, P2) *
      store_mont_jpoint(result, sm2_point_add(P1, P2)) *
      store_bn_zero *
      store_montg_one *
      store_sm2_p *
      store_sm2_rhop
 */;

int montg_jpoint_to_apoint2(const JPoint* point, AFPoint* result)
/*@ non_alias
    With X Y Z
    Require
      store_mont_jpoint_coords(point, X, Y, Z) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_bn_zero *
      store_montg_one *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists RX RY,
        __return == 1 &&
        ((Z == 0 && RX == 0 && RY == 0) ||
         (Z == 1 && RX == X && RY == Y) ||
         (Z != 0 && Z != 1 &&
          exists ZI,
            0 <= ZI && ZI < SM2_P_Z &&
            Zmod(Z * ZI, SM2_P_Z) == 1 &&
            RX == Zmod(X * ZI * ZI, SM2_P_Z) &&
            RY == Zmod(Y * ZI * ZI * ZI, SM2_P_Z))) &&
        store_mont_jpoint_coords(point, X, Y, Z) *
        store_mont_afpoint_coords(result, RX, RY) *
        store_bn_zero *
        store_montg_one *
        store_sm2_p *
        store_sm2_rhop
 */;

int montg_jpoint_to_apoint2(const JPoint* point, AFPoint* result)
/*@ point_non_alias
    With (P : ec_point)
    Require
      store_mont_jpoint(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_bn_zero *
      store_montg_one *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      __return == 1 &&
      store_mont_jpoint(point, P) *
      store_mont_afpoint(result, P) *
      store_bn_zero *
      store_montg_one *
      store_sm2_p *
      store_sm2_rhop
 */;

void montg_pre_compute_naf_w3(const AFPoint* apoint, AFPoint PT[4], AFPoint NT[4])
/*@ non_alias
    With (BasePoint : ec_point)
    Require
      BasePoint != ECInfinity &&
      store_afpoint(apoint, BasePoint) *
      wnaf3_precomp_undef(PT, NT) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop *
      store_bn_zero *
      store_montg_one
    Ensure
      store_afpoint(apoint, BasePoint) *
      store_mont_wnaf3_precomp(PT, NT, BasePoint) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop *
      store_bn_zero *
      store_montg_one
 */
{
	JPoint r, dr;

	/*@ do wnaf3_precomp_open */

	montg_apoint_to_montg(apoint, PT + 1)
	/*@ where (point_non_alias) P = BasePoint */;
	AFPoint_neg(PT + 1, NT + 1)
	/*@ where (mont_point_non_alias) P = BasePoint */;

	/*@ do jpoint_undef_to_fields */
	montg_apoint_to_jpoint2(PT + 1, &r)
	/*@ where (point_non_alias) P = BasePoint */;
	/*@ do jpoint_undef_to_fields */
	montg_double_jpoint_ex(&r, &dr)
	/*@ where (non_alias) P = BasePoint */;

	montg_add_jpoint_and_apoint_ex(&dr, PT + 1, &r)
	/*@ where (non_alias)
	      P1 = sm2_point_double(BasePoint), P2 = BasePoint */;
	/*@ store_mont_jpoint(&r,
	      sm2_point_add(sm2_point_double(BasePoint), BasePoint))
	    which implies
	      store_mont_jpoint(&r, sm2_point_mul(3, BasePoint))
	 */
	montg_jpoint_to_apoint2(&r, PT + 3)
	/*@ where (point_non_alias)
	      P = sm2_point_mul(3, BasePoint) */;
	/*@ BasePoint != ECInfinity
	    which implies sm2_point_mul(3, BasePoint) != ECInfinity
	 */
	AFPoint_neg(PT + 3, NT + 3)
	/*@ where (mont_point_non_alias)
	      P = sm2_point_mul(3, BasePoint) */;
	/*@ do wnaf3_precomp_close */
}
