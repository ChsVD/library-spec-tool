/* Verification copy of YCrypt/sm2/sm2.c::sm2_sign. */

#include "../include/sm2_protocol.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */
/*@ include strategies "../strategy/ecc_point_facts.strategies" */
/*@ include strategies "../strategy/byte_memory_views.strategies" */
/*@ include strategies "../strategy/sm2_protocol_views.strategies" */

int printf(const char *message)
/*@ Require emp
    Ensure emp
 */;

void alignas_uint32_t(const void *address)
/*@ Require emp
    Ensure aligned_4(address) && emp
 */;

bool is_on_curve(const AFPoint* point)
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

int sm2_get_id_digest(
    u1 result[32], const u1 *id, size_t id_len, const PubKey *pubkey)
/*@ With ID (P : ec_point)
    Require
      sm2_id_digest_output_aligned(result, id_len) &&
      store_bytes(id, id_len, ID) *
      store_afpoint(pubkey, P) *
      UCharArray::undef_full(result, 32) *
      store_sm2_za_globals
    Ensure
      (id_len <= 50 && __return == 0 &&
       store_bytes(id, id_len, ID) *
       store_afpoint(pubkey, P) *
       store_sm2_za(
         result, ID, P, sm2_za_digest(ID, P)) *
       store_sm2_za_globals)
      ||
      (id_len > 50 && __return == -1 &&
       store_bytes(id, id_len, ID) *
       store_afpoint(pubkey, P) *
       UCharArray::undef_full(result, 32) *
       store_sm2_za_globals)
 */;

int sm2_get_message_digest(
    u1 result[32], const u1 ZA[32], const u1 *msg, size_t msg_len)
/*@ With ZABytes Message
    Require
      sm2_message_input_aligned(msg, msg_len) &&
      aligned_4(result) &&
      store_bytes(ZA, 32, ZABytes) *
      store_bytes(msg, msg_len, Message) *
      UCharArray::undef_full(result, 32) *
      store_sm3_ti
    Ensure
      __return == 0 &&
      store_bytes(ZA, 32, ZABytes) *
      store_bytes(msg, msg_len, Message) *
      store_bytes(result, 32, sm3_digest_bytes(app(ZABytes, Message))) *
      store_sm3_ti
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
 */;

int sm2_sign(
    SM2SIG *sig, const u1 *msg, size_t msg_len,
    const u1 *id, size_t id_len,
    const PubKey *pubkey, const PrivKey *privkey)
/*@ generated
    With Message ID D (P : ec_point)
    Require
      id_len <= 50 &&
      sm2_message_input_aligned(msg, msg_len) &&
      store_bytes(msg, msg_len, Message) *
      store_bytes(id, id_len, ID) *
      store_sm2_public_key(pubkey, P) *
      store_sm2_private_key(privkey, D) *
      undef_sm2_signature(sig) *
      store_sm2_sign_globals
    Ensure
      __return == 1 &&
      (exists R S,
         sm2_signature_generated(
           be_u8_list_value(
             sm2_message_digest(ID, P, Message)),
           D, R, S) &&
         store_bytes(msg, msg_len, Message) *
         store_bytes(id, id_len, ID) *
         store_sm2_public_key(pubkey, P) *
         store_sm2_private_key(privkey, D) *
         store_sm2_signature(sig, R, S) *
         store_sm2_sign_globals)
 */;

int sm2_sign(
    SM2SIG *sig, const u1 *msg, size_t msg_len,
    const u1 *id, size_t id_len,
    const PubKey *pubkey, const PrivKey *privkey)
/*@ verifies <= generated
    With Message ID D (P : ec_point)
    Require
      id_len <= 50 &&
      sm2_message_input_aligned(msg, msg_len) &&
      valid_sm2_keypair(D, P) &&
      store_bytes(msg, msg_len, Message) *
      store_bytes(id, id_len, ID) *
      store_sm2_public_key(pubkey, P) *
      store_sm2_private_key(privkey, D) *
      undef_sm2_signature(sig) *
      store_sm2_sign_globals
    Ensure
      __return == 1 &&
      (exists R S,
         sm2_signature_generated(
           be_u8_list_value(
             sm2_message_digest(ID, P, Message)),
           D, R, S) &&
         sm2_signature_verifies(
           be_u8_list_value(
             sm2_message_digest(ID, P, Message)),
           P, R, S) &&
         store_bytes(msg, msg_len, Message) *
         store_bytes(id, id_len, ID) *
         store_sm2_public_key(pubkey, P) *
         store_sm2_private_key(privkey, D) *
         store_sm2_signature(sig, R, S) *
         store_sm2_sign_globals)
 */;

int sm2_sign(
    SM2SIG *sig, const u1 *msg, size_t msg_len,
    const u1 *id, size_t id_len,
    const PubKey *pubkey, const PrivKey *privkey)
/*@ generated */
{
	u1 ZA[32], dgst[32];
	alignas_uint32_t(ZA);
	alignas_uint32_t(dgst);
	/*@ do open_sm2_sign_globals */
	/*@ do open_sm2_public_key */
	/*@ do open_afpoint */
	/*@ do afpoint_valid */
	if (!is_on_curve(pubkey))
	{
		printf("public key is not on the curve!");
		return 0;
	}
	sm2_get_id_digest(ZA, id, id_len, pubkey);
	/*@ do open_sm2_za_globals */
	sm2_get_message_digest(dgst, ZA, msg, msg_len);

	return sm2_sign_dgst(sig, dgst, privkey);
}
