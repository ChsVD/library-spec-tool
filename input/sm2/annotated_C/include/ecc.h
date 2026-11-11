#ifndef ECC_H
#define ECC_H

#include "basicOp.h"

/* Canonical Jacobian representation of the point at infinity. */
static const JPoint JPoint_ZERO = {
    { 1, 0, 0, 0 },
    { 1, 0, 0, 0 },
    { 0, 0, 0, 0 }
};

/*@ Import Coq Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul
 */

/*@ Extern Coq (ec_point :: *) */

/*@ Extern Coq
      (ECInfinity : ec_point)
      (SM2_A_Z : Z)
      (SM2_B_Z : Z)
      (SM2_P_INV2_Z : Z)
      (MONTG_ONE_Z : Z)
      (mont_p : Z -> Z)
      (store_sm2_a : Assertion)
      (store_sm2_b : Assertion)
      (store_jpoint_zero : Assertion)
      (store_sm2_inv2p : Assertion)
      (store_bn_zero : Assertion)
      (store_montg_one : Assertion)
      (store_afpoint_fields : Z -> Z -> Z -> Assertion)
      (store_jpoint_fields : Z -> Z -> Z -> Z -> Assertion)
      (store_mont_afpoint_coords : Z -> Z -> Z -> Assertion)
      (store_mont_jpoint_coords : Z -> Z -> Z -> Z -> Assertion)
      (store_afpoint : Z -> ec_point -> Assertion)
      (store_jpoint : Z -> ec_point -> Assertion)
      (store_jpoint_with_canonical_infinity : Z -> ec_point -> Assertion)
      (store_mont_afpoint : Z -> ec_point -> Assertion)
      (store_mont_jpoint : Z -> ec_point -> Assertion)
      (afpoint_infinity : Z -> Z -> Prop)
      (jpoint_infinity : Z -> Prop)
      (canonical_jpoint_infinity : Z -> Z -> Z -> Prop)
      (jpoint_canonical_infinity_encoding : Z -> Z -> Z -> ec_point -> Prop)
      (afpoint_to_jpoint_coordinates : Z -> Z -> Z -> Z -> Z -> Prop)
      (jpoint_to_afpoint_coordinates : Z -> Z -> Z -> Z -> Z -> Prop)
      (valid_afpoint : Z -> Z -> Prop)
      (valid_jpoint : Z -> Z -> Z -> Prop)
      (afpoint_represents : Z -> Z -> ec_point -> Prop)
      (jpoint_represents : Z -> Z -> Z -> ec_point -> Prop)
      (sm2_point_add : ec_point -> ec_point -> ec_point)
      (sm2_point_double : ec_point -> ec_point)
      (sm2_point_mul : Z -> ec_point -> ec_point)
      (sm2_point_negate : ec_point -> ec_point)
      (WNAF3_LENGTH : Z)
      (wnaf3_digit : Z -> Prop)
      (wnaf3_value : list Z -> Z)
      (wnaf3_representation : Z -> list Z -> Prop)
      (store_wnaf3 : Z -> Z -> Assertion)
      (wnaf3_positive_array_undef : Z -> Assertion)
      (wnaf3_negative_array_undef : Z -> Assertion)
      (wnaf3_precomp_undef : Z -> Z -> Assertion)
      (store_mont_wnaf3_precomp : Z -> Z -> ec_point -> Assertion)
      (wnaf3_precomp_unused : Z -> Z -> Assertion)
      (store_mont_wnaf3_precomp_rest :
        Z -> Z -> ec_point -> Z -> Assertion)
 */

#endif
