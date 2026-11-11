/* Verification copy of YCrypt/sm2/ecc.c::equ_to_JPoint_one. */

#include "../include/ecc.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */

bool u32_eq_one(const u32 *a)
/*@ With (A : Z)
    Require
      store_u256(a, A)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == 1) ||
       (__return == 0 && A != 1)) &&
      store_u256(a, A)
 */
;

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
;

bool equ_to_JPoint_one(const JPoint* point)
/*@ point <= base
    With (P : ec_point)
    Require
      store_jpoint_with_canonical_infinity(point, P)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && P == ECInfinity) ||
       (__return == 0 && P != ECInfinity)) &&
      store_jpoint_with_canonical_infinity(point, P)
 */
;

bool equ_to_JPoint_one(const JPoint* point)
/*@ base */
{
	return u32_eq_one(&point->x) && u32_eq_one(&point->y) && u32_eq_zero(&point->z);
}
