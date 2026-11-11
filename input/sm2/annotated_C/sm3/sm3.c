/* Verification copy of YCrypt/sm3/sm3.c::sm3. */

#include "sm3.h"
/*@ include strategies "../strategy/byte_memory_views.strategies" */
/*@ include strategies "../strategy/sm3_ctx_views.strategies" */

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

void *memset(void *dest, int value, size_t count)
/*@ Require
      count == sizeof(struct _SM3_CTX) &&
      sm3_ctx_full_shape(dest)
    Ensure
      __return == dest &&
      sm3_ctx_full_shape(dest)
 */;

size_t sm3(const u1 *data, size_t datalen, u1 dgst[32])
/*@ With Message
    Require
      sm3_digest_input_aligned(data, datalen) &&
      aligned_4(dgst) &&
      store_bytes(data, datalen, Message) *
      UCharArray::undef_full(dgst, 32) *
      store_sm3_ti
    Ensure
      __return == 32 &&
      store_bytes(data, datalen, Message) *
      store_bytes(dgst, 32, sm3_digest_bytes(Message)) *
      store_sm3_ti
 */
{
	SM3_CTX ctx;

	sm3_init(&ctx);
	sm3_update(&ctx, data, datalen);
	sm3_final(&ctx, dgst);

	memset(&ctx, 0, sizeof(SM3_CTX));
	return 32;
}
