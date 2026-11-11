/* Verification copy of YCrypt/sm2/basicOp.c::u32_ge. */

#include "../include/basicOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */

bool u32_ge(const u32 *a, const u32 *b)
/*@ With (A B : Z)
    Require
      store_u256(a, A) *
      store_u256(b, B)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A >= B) ||
       (__return == 0 && A < B)) &&
      store_u256(a, A) *
      store_u256(b, B)
 */
{
	/*@ do open_store_u256 */
  if (a->v[3] != b->v[3])
    return (a->v[3] > b->v[3]);
  if (a->v[2] != b->v[2])
    return (a->v[2] > b->v[2]);
  if (a->v[1] != b->v[1])
    return (a->v[1] > b->v[1]);
  return (a->v[0] >= b->v[0]);
}
