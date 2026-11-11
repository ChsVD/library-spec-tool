/* Verification copy of YCrypt/sm2/ecc_montg.c::montg_double_jpoint_ex. */

#include "../include/ecc.h"
#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement */

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
 */;

void montg_double_jpoint_ex(const JPoint* a, JPoint* r)
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
    montg_double_jpoint(a, r)
    /*@ where (non_alias) P = P_non_alias $ non_alias
        where (in_place) P = P_in_place $ in_place */;
}
