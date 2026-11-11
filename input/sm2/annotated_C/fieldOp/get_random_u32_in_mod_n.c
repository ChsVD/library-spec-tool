/* Verification copy of YCrypt/sm2/fieldOp.c::get_random_u32_in_mod_n. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */

void u32_rand(u32* result)
/*@ Require
      UInt64Array::undef_full(&(result->v[0]), 4)
    Ensure
      exists R,
        0 <= R && R < U256_MOD &&
        store_u256(result, R)
 */;

void mod_n(const u32 *a, u32 *result)
/*@ in_place
    With A
    Require
      result == a &&
      store_u256(a, A) *
      store_sm2_n *
      store_sm2_rhon
    Ensure
      result == a &&
      store_fn(result, Zmod(A, SM2_N_Z)) *
      store_sm2_n *
      store_sm2_rhon
 */;

void get_random_u32_in_mod_n(u32* k)
/*@ Require
      UInt64Array::undef_full(&(k->v[0]), 4) *
      store_sm2_n *
      store_sm2_rhon
    Ensure
      exists K,
        store_fn(k, K) *
        store_sm2_n *
        store_sm2_rhon
 */
{
	u32_rand(k);
	mod_n(k, k) /*@ where (in_place) */;
}
