/* Verification copy of YCrypt/sm2/sm2.c::sm2_sign_dgst. */

#include "../include/sm2_protocol.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */
/*@ include strategies "../strategy/ecc_point_overwrite.strategies" */
/*@ include strategies "../strategy/ecc_montg_helper_views.strategies" */
/*@ include strategies "../strategy/sm2_protocol_views.strategies" */

#define NULL 0

void u1_to_u32(const u1 input[32], u32 *result)
/*@ With bytes
    Require
      store_bytes(input, 32, bytes) *
      UndefStructPredu32(result)
    Ensure
      store_bytes(input, 32, bytes) *
      store_u256(result, be_u8_list_value(bytes))
 */;

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
 */;

void get_random_u32_in_mod_n(u32 *k)
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

bool u32_eq_zero(const u32 *a)
/*@ With A
    Require
      store_u256(a, A)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == 0) ||
       (__return == 0 && A != 0)) &&
      store_u256(a, A)
 */;

void montg_times_base_point(const u32 *k, JPoint *result)
/*@ non_alias
    With K
    Require
      store_fn(k, K) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_mont_base_point_table *
      store_sm2_p * store_sm2_rhop *
      store_bn_zero * store_montg_one
    Ensure
      store_fn(k, K) *
      store_mont_jpoint(
        result, sm2_point_mul(K, SM2_G_POINT)) *
      store_sm2_mont_base_point_table *
      store_sm2_p * store_sm2_rhop *
      store_bn_zero * store_montg_one
 */;

int montg_jpoint_to_apoint(
    const JPoint *point, UINT64 *result_x, UINT64 *result_y)
/*@ point_x_only
    With (P : ec_point)
    Require
      result_x != 0 && result_y == 0 &&
      store_mont_jpoint(point, P) *
      UInt64Array::undef_full(result_x, 4) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
    Ensure
      exists RX RY,
        __return == 1 && result_y == 0 &&
        afpoint_represents(RX, RY, P) &&
        store_mont_jpoint(point, P) *
        store_u256_limbs(result_x, RX) *
        store_bn_zero * store_montg_one *
        store_sm2_p * store_sm2_rhop
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
 */
/*@ r_eq_b
    With A B
    Require
      result == b &&
      store_fn(a, A) *
      store_fn(b, B) *
      store_sm2_n
    Ensure
      result == b &&
      store_fn(a, A) *
      store_fn(result, Zmod(A + B, SM2_N_Z)) *
      store_sm2_n
 */;

void inv_for_mul_mod_n(const u32 *input, u32 *result)
/*@ in_place
    With A
    Require
      result == input &&
      A != 0 &&
      store_fn(input, A) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists Ainv,
        result == input &&
        0 <= Ainv && Ainv < SM2_N_Z &&
        Zmod(A * Ainv, SM2_N_Z) == 1 &&
        store_fn(result, Ainv) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */;

void mul_mod_n(const u32 *x, const u32 *y, u32 *result)
/*@ non_alias
    With X Y
    Require
      store_fn(x, X) *
      store_fn(y, Y) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_nh *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      store_fn(x, X) *
      store_fn(y, Y) *
      store_fn(result, Zmod(X * Y, SM2_N_Z)) *
      store_sm2_nh *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
 */;

void sub_mod_n(const u32 *a, const u32 *b, u32 *result)
/*@ r_eq_b
    With A B
    Require
      result == b &&
      store_fn(a, A) *
      store_fn(b, B) *
      store_sm2_n
    Ensure
      result == b &&
      store_fn(a, A) *
      store_fn(result, Zmod(A - B, SM2_N_Z)) *
      store_sm2_n
 */;

int sm2_sign_dgst(SM2SIG *sig, u1 dgst[32], const PrivKey *privkey)
/*@ With DigestBytes D
    Require
      store_bytes(dgst, 32, DigestBytes) *
      store_sm2_private_key(privkey, D) *
      undef_sm2_signature(sig) *
      store_sm2_sign_dgst_globals
    Ensure
      __return == 1 &&
      (exists R S,
         sm2_signature_generated(
           be_u8_list_value(DigestBytes), D, R, S) &&
         store_bytes(dgst, 32, DigestBytes) *
         store_sm2_private_key(privkey, D) *
         store_sm2_signature(sig, R, S) *
         store_sm2_sign_dgst_globals)
 */
{
	u32 r = { 0, 0, 0, 0 };
	u32 s = { 0, 0, 0, 0 };
	u32 k;

	u32 e, tmp, inversion_da_and_1, k_subtract_rda;
	JPoint rand_JPoint;
	AFPoint rand_AFPoint;

	/*@ do open_sm2_sign_dgst_globals */
	u1_to_u32(dgst, &e);
	mod_n(&e, &e) /*@ where (in_place) */;

	/*@ Inv Assert
	      exists R S,
	        sig == sig@pre && dgst == dgst@pre &&
	        privkey == privkey@pre &&
	        0 <= R && R < SM2_N_Z &&
	        0 <= S && S < SM2_N_Z &&
	        (S != 0 =>
	          sm2_signature_generated(
	            be_u8_list_value(DigestBytes), D, R, S)) &&
	        store_bytes(dgst, 32, DigestBytes) *
	        store_sm2_private_key(privkey, D) *
	        undef_sm2_signature(sig) *
	        store_fn(&e,
	          Zmod(be_u8_list_value(DigestBytes), SM2_N_Z)) *
	        store_u256(&r, R) *
	        store_u256(&s, S) *
	        UInt64Array::undef_full(&(k.v[0]), 4) *
	        UInt64Array::undef_full(&(tmp.v[0]), 4) *
	        UInt64Array::undef_full(&(inversion_da_and_1.v[0]), 4) *
	        UInt64Array::undef_full(&(k_subtract_rda.v[0]), 4) *
	        UInt64Array::undef_full(&(rand_JPoint.x.v[0]), 4) *
	        UInt64Array::undef_full(&(rand_JPoint.y.v[0]), 4) *
	        UInt64Array::undef_full(&(rand_JPoint.z.v[0]), 4) *
	        UInt64Array::undef_full(&(rand_AFPoint.x.v[0]), 4) *
	        UInt64Array::undef_full(&(rand_AFPoint.y.v[0]), 4) *
	        store_sm2_n * store_sm2_rhon * store_sm2_nh *
	        store_sm2_neg_inv_n *
	        store_sm2_mont_base_point_table *
	        store_sm2_p * store_sm2_rhop *
	        store_bn_zero * store_montg_one
	 */
	while (u32_eq_zero(&s))
	{
		get_random_u32_in_mod_n(&k);
		/*@ Given K */
		if (u32_eq_zero(&k)) {
			continue;
		}

		montg_times_base_point(&k, &rand_JPoint)
		/*@ where (non_alias) */;
		montg_jpoint_to_apoint(
			&rand_JPoint, rand_AFPoint.x.v, NULL)
		/*@
		  where (point_x_only)
		    P = sm2_point_mul(K, SM2_G_POINT)
		 */;
		/*@ do close_store_u256_base0 */

		mod_n(&(rand_AFPoint.x), &tmp)
		/*@ where (non_alias) */;
		add_mod_n(&e, &tmp, &r)
		/*@ where (non_alias) */;
		add_mod_n(&r, &k, &tmp)
		/*@ where (non_alias) */;

		/*@ do open_store_fn */
		if (u32_eq_zero(&r) || u32_eq_zero(&tmp)) {
			continue;
		}

		inversion_da_and_1.v[0] = 1;
		inversion_da_and_1.v[1] = 0;
		inversion_da_and_1.v[2] = 0;
		inversion_da_and_1.v[3] = 0;
		add_mod_n(
			&(privkey->da), &inversion_da_and_1,
			&inversion_da_and_1)
		/*@ where (r_eq_b) */;
		inv_for_mul_mod_n(
			&inversion_da_and_1, &inversion_da_and_1)
		/*@ where (in_place) */;

		mul_mod_n(&r, &(privkey->da), &k_subtract_rda)
		/*@ where (non_alias) */;
		sub_mod_n(&k, &k_subtract_rda, &k_subtract_rda)
		/*@ where (r_eq_b) */;
		mul_mod_n(&inversion_da_and_1, &k_subtract_rda, &s)
		/*@ where (non_alias) */;
	}

	/*@ do open_undef_sm2_signature */
	/*@ do materialize_u256_record */
	sig->r = r;
	sig->s = s;

	return 1;
}
