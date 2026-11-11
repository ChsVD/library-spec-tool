/* Verification copy of YCrypt/sm2/sm2.c::sm2_verify. */

#include "../include/sm2_protocol.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */
/*@ include strategies "../strategy/byte_memory_views.strategies" */
/*@ include strategies "../strategy/sm2_protocol_views.strategies" */

void alignas_uint32_t(const void *address)
/*@ Require emp
    Ensure aligned_4(address) && emp
 */;

int sm2_get_id_digest(
    u1 result[32], const u1 *id, size_t id_len, const PubKey *pubkey)
/*@ With ID (Point : ec_point)
    Require
      sm2_id_digest_output_aligned(result, id_len) &&
      store_bytes(id, id_len, ID) *
      store_afpoint(pubkey, Point) *
      UCharArray::undef_full(result, 32) *
      store_sm2_za_globals
    Ensure
      (id_len <= 50 && __return == 0 &&
       store_bytes(id, id_len, ID) *
       store_afpoint(pubkey, Point) *
       store_sm2_za(
         result, ID, Point, sm2_za_digest(ID, Point)) *
       store_sm2_za_globals)
      ||
      (id_len > 50 && __return == -1 &&
       store_bytes(id, id_len, ID) *
       store_afpoint(pubkey, Point) *
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

int sm2_verify_dgst(
    const SM2SIG *signature, const u1 dgst[32], const AFPoint *pubkey)
/*@ verifies
    With DigestBytes (Point : ec_point) SigR SigS
    Require
      Point != ECInfinity &&
      store_sm2_signature(signature, SigR, SigS) *
      store_bytes(dgst, 32, DigestBytes) *
      store_afpoint(pubkey, Point) *
      store_sm2_verify_dgst_globals
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 &&
        sm2_signature_verifies(
          be_u8_list_value(DigestBytes), Point, SigR, SigS)) ||
       (__return == 0 &&
        (! sm2_signature_verifies(
          be_u8_list_value(DigestBytes), Point, SigR, SigS)))) &&
      store_sm2_signature(signature, SigR, SigS) *
      store_bytes(dgst, 32, DigestBytes) *
      store_afpoint(pubkey, Point) *
      store_sm2_verify_dgst_globals
 */;

int sm2_verify(
    const SM2SIG *sig, const u1 *msg, size_t msg_len,
    const u1 *id, size_t id_len, const PubKey *pubkey)
/*@ verifies
    With Message ID (P : ec_point) SigR SigS
    Require
      id_len <= 50 &&
      P != ECInfinity &&
      sm2_message_input_aligned(msg, msg_len) &&
      store_sm2_signature(sig, SigR, SigS) *
      store_bytes(msg, msg_len, Message) *
      store_bytes(id, id_len, ID) *
      store_afpoint(pubkey, P) *
      store_sm2_verify_globals
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 &&
        sm2_signature_verifies(
          be_u8_list_value(
            sm2_message_digest(ID, P, Message)),
          P, SigR, SigS)) ||
       (__return == 0 &&
        (! sm2_signature_verifies(
          be_u8_list_value(
            sm2_message_digest(ID, P, Message)),
          P, SigR, SigS)))) &&
      store_sm2_signature(sig, SigR, SigS) *
      store_bytes(msg, msg_len, Message) *
      store_bytes(id, id_len, ID) *
      store_afpoint(pubkey, P) *
      store_sm2_verify_globals
 */;

int sm2_verify(
    const SM2SIG *sig, const u1 *msg, size_t msg_len,
    const u1 *id, size_t id_len, const PubKey *pubkey)
/*@ generated <= verifies
    With Message ID (P : ec_point) SigR SigS
    Require
      id_len <= 50 &&
      sm2_message_input_aligned(msg, msg_len) &&
      store_sm2_signature(sig, SigR, SigS) *
      store_bytes(msg, msg_len, Message) *
      store_bytes(id, id_len, ID) *
      store_sm2_public_key(pubkey, P) *
      store_sm2_verify_globals
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 &&
        (exists D,
           valid_sm2_keypair(D, P) &&
           sm2_signature_generated(
             be_u8_list_value(
               sm2_message_digest(ID, P, Message)),
             D, SigR, SigS))) ||
       (__return == 0 &&
        (! (exists D,
             valid_sm2_keypair(D, P) &&
             sm2_signature_generated(
               be_u8_list_value(
                 sm2_message_digest(ID, P, Message)),
               D, SigR, SigS))))) &&
      store_sm2_signature(sig, SigR, SigS) *
      store_bytes(msg, msg_len, Message) *
      store_bytes(id, id_len, ID) *
      store_sm2_public_key(pubkey, P) *
      store_sm2_verify_globals
 */;

int sm2_verify(
    const SM2SIG *sig, const u1 *msg, size_t msg_len,
    const u1 *id, size_t id_len, const PubKey *pubkey)
/*@ verifies */
{
	u1 ZA[32], dgst[32];
	alignas_uint32_t(ZA);
	alignas_uint32_t(dgst);
	/*@ do open_sm2_verify_globals */

	sm2_get_id_digest(ZA, id, id_len, pubkey)
	/*@ where Point = P */;
	/*@ do open_sm2_za_globals */
	sm2_get_message_digest(dgst, ZA, msg, msg_len);

	return sm2_verify_dgst(sig, dgst, pubkey)
	/*@ where (verifies) Point = P */;
}
