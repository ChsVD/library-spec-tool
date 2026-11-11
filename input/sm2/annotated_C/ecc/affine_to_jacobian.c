/* Verification copy of YCrypt/sm2/ecc.c::affine_to_jacobian. */

#include "../include/ecc.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */
/*@ include strategies "../strategy/ecc_point_copy_steps.strategies" */

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
 */
;

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
 */
;

void affine_to_jacobian(const AFPoint* point, JPoint* result)
/*@ non_alias */
{
	if (!equ_to_AFPoint_one(point) /*@ where (base) */)
	{
		/*@ do jpoint_xy_undef_fields */
		/*@ do materialize_afpoint_record */
		result->x = point->x;
		result->y = point->y;
		result->z.v[0] = 1;
		result->z.v[1] = 0;
		result->z.v[2] = 0;
		result->z.v[3] = 0;
		return;
	}

	/*@ do jpoint_undef_fields */
	/*@ do open_jpoint_zero */
	/*@ do materialize_jpoint_record */
	*result = JPoint_ZERO;
}
