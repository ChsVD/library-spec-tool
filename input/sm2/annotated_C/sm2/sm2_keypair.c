/* Verification copy of YCrypt/sm2/sm2.c::sm2_keypair. */

#include "../include/sm2_protocol.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/sm2_protocol_views.strategies" */

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
 */;

void add_mod_n(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias
    With A B
    Require
      store_fn(a, A) *
      store_fn(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_n
    Ensure
      store_fn(a, A) *
      store_fn(b, B) *
      store_fn(result, Zmod(A + B, SM2_N_Z)) *
      store_sm2_n
 */;

bool u32_eq_zero(const u32 *a)
/*@ With (A : Z)
    Require
      store_u256(a, A)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == 0) ||
       (__return == 0 && A != 0)) &&
      store_u256(a, A)
 */;

void sm2_get_public_key(const PrivKey *privkey, PubKey *pubkey)
/*@ With D
    Require
      store_sm2_private_key(privkey, D) *
      UndefStructPredAFPoint(pubkey) *
      store_sm2_get_public_key_globals
    Ensure
      store_sm2_private_key(privkey, D) *
      store_sm2_public_key(
        pubkey, sm2_point_mul(D, SM2_G_POINT)) *
      store_sm2_get_public_key_globals
 */;

void sm2_keypair(PubKey *pubkey, PrivKey *privkey)
/*@ Require
      UndefStructPredAFPoint(pubkey) *
      undef_sm2_private_key(privkey) *
      store_sm2_keypair_globals
    Ensure
      exists D,
        store_sm2_private_key(privkey, D) *
        store_sm2_public_key(
          pubkey, sm2_point_mul(D, SM2_G_POINT)) *
        store_sm2_keypair_globals
 */
{
	u32 one = { 1, 0, 0, 0 };
	u32 d_plus_one;

	/*@ do open_sm2_keypair_globals */
	do {
		get_random_u32_in_mod_n(&(privkey->da));
		add_mod_n(&(privkey->da), &one, &d_plus_one)
		/*@ where (non_alias) */;
	} /*@ Inv Assert
	       exists D DPlus,
	         privkey == privkey@pre && pubkey == pubkey@pre &&
	         0 <= D && D < SM2_N_Z &&
	         0 <= DPlus && DPlus < SM2_N_Z &&
	         DPlus == Zmod(D + 1, SM2_N_Z) &&
	         store_u256(&(privkey->da), D) *
	         store_fn(&one, 1) *
	         store_u256(&d_plus_one, DPlus) *
	         UndefStructPredAFPoint(pubkey) *
	         store_sm2_n * store_sm2_rhon *
	         store_sm2_get_public_key_globals
	   */ while (u32_eq_zero(&(privkey->da)) ||
	              u32_eq_zero(&d_plus_one));

	sm2_get_public_key(privkey, pubkey);
}
