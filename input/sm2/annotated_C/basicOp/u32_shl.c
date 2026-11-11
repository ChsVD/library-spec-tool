/* Verification copy of YCrypt/sm2/basicOp.c::u32_shl. */

#include "../include/basicOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */

u1 u32_shl(u32 *input)
/*@ With (X : Z)
    Require
      store_u256(input, X)
    Ensure
      exists Y,
      u256_shl_result(X, Y, __return) &&
      store_u256(input, Y)
 */
{
	/*@ do open_store_u256 */
  u1 carry = (input->v[3] >> 63);
  input->v[3] = (input->v[3] << 1) | (input->v[2] >> 63);
  input->v[2] = (input->v[2] << 1) | (input->v[1] >> 63);
  input->v[1] = (input->v[1] << 1) | (input->v[0] >> 63);
  input->v[0] <<= 1;
  return carry;
}
