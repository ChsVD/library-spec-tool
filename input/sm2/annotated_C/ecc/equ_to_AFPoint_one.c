/* Verification copy of YCrypt/sm2/ecc.c::equ_to_AFPoint_one. */

#include "../include/ecc.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */

bool u32_eq_zero(const u32 *a)
/*@ With (A : Z)
    Require
      store_u256(a, A)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == 0) ||
       (__return == 0 && A != 0)) &&
      store_u256(a, A)
 */
;

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
;

bool equ_to_AFPoint_one(const AFPoint* point)
/*@ point <= base
    With (P : ec_point)
    Require
      store_afpoint(point, P)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && P == ECInfinity) ||
       (__return == 0 && P != ECInfinity)) &&
      store_afpoint(point, P)
 */
;

bool equ_to_AFPoint_one(const AFPoint* point)
/*@ base */
{
	return u32_eq_zero(&point->x) && u32_eq_zero(&point->y);
}
