/* Verification copy of YCrypt/sm2/sm2.c::sm2_get_message_digest. */

#include "../include/sm2_protocol.h"
/*@ include strategies "../strategy/byte_memory_views.strategies" */
/*@ include strategies "../strategy/sm3_ctx_views.strategies" */
/*@ include strategies "../strategy/sm2_protocol_views.strategies" */

void sm3_init(SM3_CTX *ctx)
/*@ Require
      undef_sm3_ctx(ctx)
    Ensure
      store_sm3_ctx(ctx, nil)
 */;

void sm3_update(SM3_CTX *ctx, const u1 *data, size_t data_len)
/*@ With Prefix Chunk
    Require
      Zlength(Prefix) + data_len < SM3_MAX_BYTES &&
      sm3_update_data_aligned(
        data, data_len, Zlength(sm3_tail(Prefix))) &&
      store_sm3_ctx(ctx, Prefix) *
      store_bytes(data, data_len, Chunk) *
      store_sm3_ti
    Ensure
      store_sm3_ctx(ctx, app(Prefix, Chunk)) *
      store_bytes(data, data_len, Chunk) *
      store_sm3_ti
 */;

void sm3_final(SM3_CTX *ctx, u1 digest[32])
/*@ With Message
    Require
      aligned_4(digest) &&
      store_sm3_ctx(ctx, Message) *
      UCharArray::undef_full(digest, 32) *
      store_sm3_ti
    Ensure
      sm3_ctx_full_shape(ctx) *
      store_bytes(digest, 32, sm3_digest_bytes(Message)) *
      store_sm3_ti
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
 */
{
	SM3_CTX ctx;
	sm3_init(&ctx);
	sm3_update(&ctx, ZA, 32);
	sm3_update(&ctx, msg, msg_len);
	sm3_final(&ctx, result);
	return 0;
}
