/* Verification copy of YCrypt/sm2/ecc.c::AFPoint_neg. */

#include "../include/ecc.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_point_copy_steps.strategies" */

void u32_sub(const u32* a, const u32* b, u32* result)
/*@ non_alias
    With A B
    Require
      store_u256(a, A) *
      store_u256(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4)
    Ensure
      exists S borrow,
        0 <= S && S < U256_MOD &&
        0 <= borrow && borrow <= 1 &&
        A - B == S - borrow * U256_MOD &&
        store_u256(a, A) *
        store_u256(b, B) *
        store_u256(result, S)
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
 */
;

void AFPoint_neg(const AFPoint* point, AFPoint* result)
/*@ point_non_alias <= non_alias
    With (P : ec_point)
    Require
      P != ECInfinity &&
      store_afpoint(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_sm2_p
    Ensure
      store_afpoint(point, P) *
      store_afpoint(result, sm2_point_negate(P)) *
      store_sm2_p
 */
;

void AFPoint_neg(const AFPoint* point, AFPoint* result)
/*@ mont_point_non_alias <= non_alias
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
 */
;

void AFPoint_neg(const AFPoint* point, AFPoint* result)
/*@ non_alias */
{
	/*@ do afpoint_undef_fields */
	/*@ do materialize_afpoint_record */
	result->x = point->x;
	/*@ do open_sm2_p */
	u32_sub(&SM2_P, &point->y, &result->y)
	/*@
	  where (non_alias) A = SM2_P_Z, B = Y_non_alias
	    $ non_alias
	 */;
}
