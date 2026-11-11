/* Verification copy of YCrypt/sm3/sm3.c::sm3_update. */

#include "sm3.h"
/*@ include strategies "../strategy/byte_memory_views.strategies" */
/*@ include strategies "../strategy/sm3_ctx_views.strategies" */
/*@ include strategies "../strategy/sm3_streaming_memory_views.strategies" */
/*@ Import Coq Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_update_lib
 */

void *memcpy(void *dest, const void *src, size_t count)
/*@ With Bytes
    Require
      0 <= count &&
      UCharArray::undef_full(dest, count) *
      store_bytes(src, count, Bytes)
    Ensure
      __return == dest &&
      store_bytes(dest, count, Bytes) *
      store_bytes(src, count, Bytes)
 */;

void sm3_compress(u4 digest[8], const u1 *block, size_t nblocks)
/*@ With State Blocks
    Require
      sm3_compress_input_aligned(block, nblocks) &&
      store_u32_words(digest, 8, State) *
      store_bytes(block, 64 * nblocks, Blocks) *
      store_sm3_ti
    Ensure
      store_u32_words(digest, 8, sm3_compress_bytes(State, Blocks)) *
      store_bytes(block, 64 * nblocks, Blocks) *
      store_sm3_ti
 */;

void sm3_update(SM3_CTX *ctx, const u1 *data, size_t data_len)
/*@ With Prefix Chunk
    Require
      Zlength(Prefix) + data_len < SM3_MAX_BYTES &&
      sm3_update_data_aligned(data, data_len, Zlength(sm3_tail(Prefix))) &&
      store_sm3_ctx(ctx, Prefix) *
      store_bytes(data, data_len, Chunk) *
      store_sm3_ti
    Ensure
      store_sm3_ctx(ctx, app(Prefix, Chunk)) *
      store_bytes(data, data_len, Chunk) *
      store_sm3_ti
 */
{
	size_t nblock = 0, offset = 0;
	size_t left = 0;

	/*@ do sm3_ctx_alignment */
	/*@ do open_store_sm3_ctx */
	/*@ do open_store_byte_prefix */
	if (ctx->num)
	{
		left = SM3_BLOCK_SIZE - ctx->num;
		if (data_len < left)
		{
			/*@ do focus_undef_prefix */
			memcpy(ctx->block + ctx->num, data, data_len);
			ctx->num += data_len;
			return;
		}
		else
		{
			/*@ do focus_store_bytes_prefix */
			memcpy(ctx->block + ctx->num, data, left);
			/*@ do open_store_bytes */
			/*@ do open_store_u32_words */
			/*@ do merge_full_byte_regions */
			sm3_compress(ctx->digest, ctx->block, 1);
			ctx->nblocks++;
			data += left;
			data_len -= left;
			ctx->num = 0;
		}
	}
	nblock = data_len / SM3_BLOCK_SIZE;
	left = data_len % SM3_BLOCK_SIZE;
	offset = data_len - left;
	ctx->num = left;
	/*@ do open_store_bytes */
	/*@ Assert
	      exists State BlockBytes NBlocks ConsumedBytes BulkBytes TailBytes,
		        offset == 64 * nblock &&
		        data_len == 64 * nblock + left &&
		        0 <= left && left < 64 &&
		        0 <= offset && offset <= data_len &&
		        0 <= data_len@pre - data_len &&
		        (data_len@pre - data_len) + 64 * nblock <= data_len@pre &&
		        data == data@pre + (data_len@pre - data_len) &&
		        ctx == ctx@pre &&
		        u8_list_bounded(Prefix) &&
		        Zlength(app(Prefix, Chunk)) < SM3_MAX_BYTES &&
		        sm3_compress_input_aligned(data, nblock) &&
		        sm3_compress_input_aligned(
		          data@pre + (data_len@pre - (64 * nblock + left)),
		          nblock) &&
		        Zlength(ConsumedBytes) == data_len@pre - data_len &&
		        Zlength(BulkBytes) == 64 * nblock &&
		        Zlength(TailBytes) == left &&
		        Chunk == app(ConsumedBytes, app(BulkBytes, TailBytes)) &&
		        State == sm3_compress_bytes(SM3_IV,
		          sm3_full_bytes(app(Prefix, ConsumedBytes))) &&
		        NBlocks == Zlength(app(Prefix, ConsumedBytes)) / 64 &&
		        sm3_tail(app(Prefix, ConsumedBytes)) == nil &&
	        store_u32_words(&(ctx->digest), 8, State) *
		        store_uint64(&(ctx->num), left) *
		        store_uint64(&(ctx->nblocks), NBlocks) *
	        store_byte_prefix(&(ctx->block), 64, BlockBytes) *
	        UCharArray::seg(data@pre, 0,
	          data_len@pre - data_len, ConsumedBytes) *
	        UCharArray::seg(data@pre, data_len@pre - data_len,
	          (data_len@pre - data_len) + 64 * nblock, BulkBytes) *
	        UCharArray::seg(data@pre,
	          (data_len@pre - data_len) + 64 * nblock,
	          data_len@pre, TailBytes) *
	        store_sm3_ti
	 */
	if (nblock > 0)
	{
		/*@ do open_store_u32_words */
		sm3_compress(ctx->digest, data, nblock);
		ctx->nblocks += nblock;
	}
	/*@ Assert
	      exists State NBlocks ConsumedBytes BulkBytes TailBytes,
		        offset == 64 * nblock &&
		        data_len == 64 * nblock + left &&
		        0 <= left && left < 64 &&
		        left - left == 0 &&
		        0 <= data_len@pre - data_len &&
		        data == data@pre + (data_len@pre - data_len) &&
		        ctx == ctx@pre &&
		        u8_list_bounded(Prefix) &&
		        Zlength(app(Prefix, Chunk)) < SM3_MAX_BYTES &&
		        Zlength(ConsumedBytes) == data_len@pre - data_len &&
		        Zlength(BulkBytes) == 64 * nblock &&
		        Zlength(TailBytes) == left &&
		        Chunk == app(ConsumedBytes, app(BulkBytes, TailBytes)) &&
		        State == sm3_compress_bytes(SM3_IV,
		          sm3_full_bytes(app(Prefix, Chunk))) &&
		        NBlocks == Zlength(app(Prefix, Chunk)) / 64 &&
		        TailBytes == sm3_tail(app(Prefix, Chunk)) &&
	        store_u32_words(&(ctx->digest), 8, State) *
		        store_uint64(&(ctx->num), left) *
		        store_uint64(&(ctx->nblocks), NBlocks) *
		        UCharArray::undef_full(&(ctx->block[left - left]), left) *
		        UCharArray::undef_full(&(ctx->block[left]), 64 - left) *
	        UCharArray::seg(data@pre, 0,
	          data_len@pre - data_len, ConsumedBytes) *
	        UCharArray::seg(data@pre, data_len@pre - data_len,
	          (data_len@pre - data_len) + 64 * nblock, BulkBytes) *
	        UCharArray::seg(data@pre,
	          (data_len@pre - data_len) + 64 * nblock,
	          data_len@pre, TailBytes) *
	        store_sm3_ti
	 */
	memcpy(ctx->block, data + offset, left);
	/*@ do restore_uchar_segment */
	/*@ do merge_uchar_segments */
	/*@ do merge_uchar_segments */
	/*@ do close_uchar_seg0 */
}
