/* Verification copy of YCrypt/sm2/basicOp.c::u32_eq_one. */

#include "../include/basicOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */

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
{
	/*@ do open_store_u256 */
  return !((a->v[0] ^ 1) | a->v[1] | a->v[2] | a->v[3]);
}
