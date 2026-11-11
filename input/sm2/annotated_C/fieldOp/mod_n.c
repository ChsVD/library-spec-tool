/* Verification copy of YCrypt/sm2/fieldOp.c::mod_n. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */

bool u32_ge(const u32* a, const u32* b)
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
 */;

u1 u32_add(const u32* a, const u32* b, u32* result)
/*@ r_eq_a
    With A B
    Require
      result == a &&
      store_u256(a, A) *
      store_u256(b, B)
    Ensure
      exists S,
        0 <= S && S < U256_MOD &&
        0 <= __return && __return <= 1 &&
        A + B == S + __return * U256_MOD &&
        result == a &&
        store_u256(result, S) *
        store_u256(b, B)
 */;

// result = a mod N
void mod_n(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      result != a &&
      store_u256(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_n *
      store_sm2_rhon
    Ensure
      store_u256(a, A) *
      store_fn(result, Zmod(A, SM2_N_Z)) *
      store_sm2_n *
      store_sm2_rhon
 */
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
 */
/*@ non_alias */
/*@ in_place */
{
	/*@ do open_store_u256 */
	if (result != a) {
		/*@ Assert
		      a == a@pre &&
		      result == result@pre &&
		      result != a &&
		      store_u256(a, A_non_alias) *
		      UndefStructPredu32(result) *
		      store_sm2_n *
			      store_sm2_rhon
			      $ non_alias
		 */
		/*@ do open_store_u256 */
		*result = *a;
	}
	/*@ Assert
	      a == a@pre &&
	      result == result@pre &&
	      result != a &&
	      0 <= A_non_alias &&
	      A_non_alias < U256_MOD &&
	      store_u256(a, A_non_alias) *
	      store_u256(result, A_non_alias) *
	      store_sm2_n *
	      store_sm2_rhon
	      $ non_alias
	 */
	/*@ Assert
	      a == a@pre &&
	      result == result@pre &&
	      result == a &&
	      0 <= A_in_place &&
	      A_in_place < U256_MOD &&
	      store_u256(result, A_in_place) *
	      store_sm2_n *
	      store_sm2_rhon
	      $ in_place
	 */
	/*@ do open_sm2_n */
	/*@ do open_sm2_rhon */
	/*@ do open_store_u256 */
	if (u32_ge(result, &SM2_N)) {
		u32_add(result, &SM2_rhoN, result) /*@ where (r_eq_a) */;
	}
}
