/* Verification copy of YCrypt/sm2/basicOp.c::u32_shr. */

#include "../include/basicOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */

void u32_shr(u32 *input)
/*@ With (X : Z)
    Require
      store_u256(input, X)
    Ensure
      store_u256(input, X / 2)
 */
{
	/*@ do open_store_u256 */
  input->v[0] = (input->v[0] >> 1) | (input->v[1] << 63);
  input->v[1] = (input->v[1] >> 1) | (input->v[2] << 63);
  input->v[2] = (input->v[2] >> 1) | (input->v[3] << 63);
  input->v[3] >>= 1;
}
