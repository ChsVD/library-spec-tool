/* Verification copy of YCrypt/sm2/sm2.c::sm2_get_public_key. */

#include "../include/sm2_protocol.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */
/*@ include strategies "../strategy/ecc_point_copy_steps.strategies" */
/*@ include strategies "../strategy/sm2_protocol_views.strategies" */

void ML_mul_basepoint(const u32* k, JPoint* result)
/*@ non_alias
    With K
    Require
      store_fn(k, K) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_base_point_table *
      store_sm2_p * store_sm2_rhop *
      store_jpoint_zero * store_sm2_inv2p
    Ensure
      store_fn(k, K) *
      store_jpoint_with_canonical_infinity(
        result, sm2_point_mul(K, SM2_G_POINT)) *
      store_sm2_base_point_table *
      store_sm2_p * store_sm2_rhop *
      store_jpoint_zero * store_sm2_inv2p
 */;

void jacobian_to_affine(const JPoint* point, AFPoint* result)
/*@ point_non_alias
    With (P : ec_point)
    Require
      store_jpoint_with_canonical_infinity(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_jpoint_with_canonical_infinity(point, P) *
      store_afpoint(result, P) *
      store_sm2_p *
      store_sm2_rhop
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
 */
{
	JPoint rst_jacobian;
	/*@ do open_sm2_get_public_key_globals */
	/*@ do jpoint_undef_to_fields */
	ML_mul_basepoint(&(privkey->da), &rst_jacobian)
	/*@ where (non_alias) */;
	jacobian_to_affine(&rst_jacobian, pubkey)
	/*@
	  where (point_non_alias)
	    P = sm2_point_mul(D, SM2_G_POINT)
	 */;
}
