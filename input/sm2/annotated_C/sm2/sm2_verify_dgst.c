/* Verification copy of YCrypt/sm2/sm2.c::sm2_verify_dgst. */

#include "../include/sm2_protocol.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */
/*@ include strategies "../strategy/ecc_point_facts.strategies" */
/*@ include strategies "../strategy/ecc_point_overwrite.strategies" */
/*@ include strategies "../strategy/ecc_montg_helper_views.strategies" */
/*@ include strategies "../strategy/byte_memory_views.strategies" */
/*@ include strategies "../strategy/sm2_protocol_views.strategies" */

#define NULL 0

int printf(const char *message)
/*@ Require emp
    Ensure emp
 */;

bool is_on_curve(const AFPoint *point)
/*@ With X Y
    Require
      store_afpoint_fields(point, X, Y) *
      store_sm2_a * store_sm2_b *
      store_sm2_p * store_sm2_rhop
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && valid_afpoint(X, Y)) ||
       (__return == 0 && (! valid_afpoint(X, Y)))) &&
      store_afpoint_fields(point, X, Y) *
      store_sm2_a * store_sm2_b *
      store_sm2_p * store_sm2_rhop
 */;

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

void u1_to_u32(const u1 input[32], u32 *result)
/*@ With bytes
    Require
      store_bytes(input, 32, bytes) *
      UndefStructPredu32(result)
    Ensure
      store_bytes(input, 32, bytes) *
      store_u256(result, be_u8_list_value(bytes))
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

void montg_times_point_naf_w3(
    const AFPoint *point, const u32 *k, JPoint *result)
/*@ non_alias
    With (Point : ec_point) (K : Z)
    Require
      Point != ECInfinity &&
      store_afpoint(point, Point) *
      store_fn(k, K) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_h * store_sm2_p * store_sm2_rhop *
      store_bn_zero * store_montg_one
    Ensure
      store_afpoint(point, Point) *
      store_fn(k, K) *
      store_mont_jpoint(result, sm2_point_mul(K, Point)) *
      store_sm2_h * store_sm2_p * store_sm2_rhop *
      store_bn_zero * store_montg_one
 */;

int montg_add_jpoint(const JPoint *a, const JPoint *b, JPoint *result)
/*@ r_eq_b
    With (Left Right : ec_point)
    Require
      result == b &&
      store_mont_jpoint(a, Left) * store_mont_jpoint(b, Right) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
    Ensure
      __return == 1 && result == b &&
      store_mont_jpoint(a, Left) *
      store_mont_jpoint(result, sm2_point_add(Left, Right)) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
 */;

static inline bool montg_is_jpoint_zero(const JPoint *point)
/*@ point
    With (Point : ec_point)
    Require
      store_mont_jpoint(point, Point) *
      store_bn_zero
    Ensure
      ((__return == 1 && Point == ECInfinity) ||
       (__return == 0 && Point != ECInfinity)) &&
      store_mont_jpoint(point, Point) *
      store_bn_zero
 */;

int montg_jpoint_to_apoint(
    const JPoint *point, UINT64 *result_x, UINT64 *result_y)
/*@ point_x_only
    With (Point : ec_point)
    Require
      result_x != 0 && result_y == 0 &&
      store_mont_jpoint(point, Point) *
      UInt64Array::undef_full(result_x, 4) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
    Ensure
      exists RX RY,
        __return == 1 && result_y == 0 &&
        afpoint_represents(RX, RY, Point) &&
        store_mont_jpoint(point, Point) *
        store_u256_limbs(result_x, RX) *
        store_bn_zero * store_montg_one *
        store_sm2_p * store_sm2_rhop
 */;

void mod_n(const u32 *a, u32 *result)
/*@ in_place
    With A
    Require
      result == a &&
      store_u256(a, A) *
      store_sm2_n * store_sm2_rhon
    Ensure
      result == a &&
      store_fn(result, Zmod(A, SM2_N_Z)) *
      store_sm2_n * store_sm2_rhon
 */;

bool u32_eq(const u32 *a, const u32 *b)
/*@ With (A B : Z)
    Require
      store_u256(a, A) *
      store_u256(b, B)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == B) ||
       (__return == 0 && A != B)) &&
      store_u256(a, A) *
      store_u256(b, B)
 */;

int sm2_verify_dgst(
    const SM2SIG *signature, const u1 dgst[32], const AFPoint *pubkey)
/*@ verifies
    With DigestBytes (P : ec_point) SigR SigS
    Require
      P != ECInfinity &&
      store_sm2_signature(signature, SigR, SigS) *
      store_bytes(dgst, 32, DigestBytes) *
      store_afpoint(pubkey, P) *
      store_sm2_verify_dgst_globals
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 &&
        sm2_signature_verifies(
          be_u8_list_value(DigestBytes), P, SigR, SigS)) ||
       (__return == 0 &&
        (! sm2_signature_verifies(
          be_u8_list_value(DigestBytes), P, SigR, SigS)))) &&
      store_sm2_signature(signature, SigR, SigS) *
      store_bytes(dgst, 32, DigestBytes) *
      store_afpoint(pubkey, P) *
      store_sm2_verify_dgst_globals
 */;

int sm2_verify_dgst(
    const SM2SIG *signature, const u1 dgst[32], const AFPoint *pubkey)
/*@ generated <= verifies
    With DigestBytes (P : ec_point) SigR SigS
    Require
      store_sm2_signature(signature, SigR, SigS) *
      store_bytes(dgst, 32, DigestBytes) *
      store_sm2_public_key(pubkey, P) *
      store_sm2_verify_dgst_globals
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 &&
        (exists D,
           valid_sm2_keypair(D, P) &&
           sm2_signature_generated(
             be_u8_list_value(DigestBytes), D, SigR, SigS))) ||
       (__return == 0 &&
        (! (exists D,
             valid_sm2_keypair(D, P) &&
             sm2_signature_generated(
               be_u8_list_value(DigestBytes), D, SigR, SigS))))) &&
      store_sm2_signature(signature, SigR, SigS) *
      store_bytes(dgst, 32, DigestBytes) *
      store_sm2_public_key(pubkey, P) *
      store_sm2_verify_dgst_globals
 */;

int sm2_verify_dgst(
    const SM2SIG *signature, const u1 dgst[32], const AFPoint *pubkey)
/*@ verifies */
{
	/*@ do open_sm2_verify_dgst_globals */
	/*@ do open_jpoint_zero */
	/*@ do materialize_jpoint_record */
	u32 e, t, R;
	JPoint tmp1 = JPoint_ZERO, point1_jacobian = JPoint_ZERO;

	/*@ do open_afpoint */
	/*@ do afpoint_valid */
	if (!is_on_curve(pubkey))
	{
		printf("Public key not on curve!\n");
		return 0;
	}

	const u32 *r = &(signature->r);
	const u32 *s = &(signature->s);

	/*@ do open_sm2_n */
	if (u32_ge(r, &SM2_N) || u32_eq_zero(r) ||
	    u32_ge(s, &SM2_N) || u32_eq_zero(s))
		return 0;

	add_mod_n(r, s, &t) /*@ where (non_alias) */;
	if (u32_eq_zero(&t))
		return 0;

	u1_to_u32(dgst, &e);

	montg_times_base_point(s, &tmp1) /*@ where (non_alias) */;
	montg_times_point_naf_w3(pubkey, &t, &point1_jacobian)
	/*@ where (non_alias) Point = P */;

	montg_add_jpoint(&tmp1, &point1_jacobian, &point1_jacobian)
	/*@ where (r_eq_b)
	      Left = sm2_point_mul(SigS, SM2_G_POINT),
	      Right = sm2_point_mul(
	        Zmod(SigR + SigS, SM2_N_Z), P) */;
	if (montg_is_jpoint_zero(&point1_jacobian)
	    /*@ where (point)
	          Point = sm2_point_add(
	            sm2_point_mul(SigS, SM2_G_POINT),
	            sm2_point_mul(
	              Zmod(SigR + SigS, SM2_N_Z), P)) */)
		return 0;
	montg_jpoint_to_apoint(&point1_jacobian, t.v, NULL)
	/*@ where (point_x_only)
	      Point = sm2_point_add(
	        sm2_point_mul(SigS, SM2_G_POINT),
	        sm2_point_mul(
	          Zmod(SigR + SigS, SM2_N_Z), P)) */;
	/*@ do close_store_u256_base0 */

	mod_n(&e, &e) /*@ where (in_place) */;
	mod_n(&t, &t) /*@ where (in_place) */;
	add_mod_n(&e, &t, &R) /*@ where (non_alias) */;

	return u32_eq(&R, r);
}
