/* Verification copy of YCrypt/sm3/sm3.c::sm3_final. */

#include "sm3.h"
/*@ include strategies "../strategy/byte_memory_views.strategies" */
/*@ include strategies "../strategy/sm3_ctx_views.strategies" */
/*@ include strategies "../strategy/sm3_word_views.strategies" */
/*@ include strategies "../strategy/sm3_streaming_memory_views.strategies" */
/*@ Import Coq Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_final_lib
 */

void *memset(void *dest, int value, size_t count)
/*@ Require
      0 <= count &&
      UCharArray::undef_full(dest, count)
    Ensure
      __return == dest &&
      store_bytes(
        dest, count,
        repeat_Z(unsigned_last_nbits(value, 8), count))
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
 */
{
	uint32_t i = 0;
	uint32_t * pdigest = (uint32_t *)digest;
	uint32_t * count = (uint32_t *)(ctx->block + SM3_BLOCK_SIZE - 8);

	/*@ do sm3_ctx_alignment */
	/*@ do open_store_sm3_ctx */
	/*@ do open_store_byte_prefix */
	/*@ Assert
	      exists State Tail,
	        u8_list_bounded(Message) &&
	        Zlength(Message) < SM3_MAX_BYTES &&
	        Tail == sm3_tail(Message) &&
	        0 <= Zlength(Tail) && Zlength(Tail) < 64 &&
	        ctx == ctx@pre && digest == digest@pre &&
	        i == 0 && pdigest == digest@pre && aligned_4(pdigest) &&
	        count == &(ctx->block[56]) &&
	        State == sm3_compress_bytes(SM3_IV, sm3_full_bytes(Message)) &&
	        aligned_4(&(ctx->block)) &&
	        store_u32_words(&(ctx->digest), 8, State) *
	        store_uint64(&(ctx->nblocks), Zlength(Message) / 64) *
	        UCharArray::full(&(ctx->block), Zlength(Tail), Tail) *
	        UCharArray::undef_seg(
	          &(ctx->block), Zlength(Tail), 64) *
	        store_uint64(&(ctx->num), Zlength(Tail)) *
	        UCharArray::undef_full(digest, 32) *
	        store_sm3_ti
	 */
	ctx->block[ctx->num] = 0x80;

	if (ctx->num + 9 <= SM3_BLOCK_SIZE)
	{
		/*@ Assert
		      exists State Tail,
		        u8_list_bounded(Message) &&
		        Zlength(Message) < SM3_MAX_BYTES &&
		        Tail == sm3_tail(Message) &&
		        0 <= Zlength(Tail) && Zlength(Tail) <= 55 &&
		        ctx == ctx@pre && digest == digest@pre &&
		        i == 0 && pdigest == digest@pre && aligned_4(pdigest) &&
		        count == &(ctx->block[56]) &&
		        State == sm3_compress_bytes(SM3_IV, sm3_full_bytes(Message)) &&
		        aligned_4(&(ctx->block)) &&
		        store_u32_words(&(ctx->digest), 8, State) *
		        store_uint64(&(ctx->nblocks), Zlength(Message) / 64) *
		        UCharArray::full(
		          &(ctx->block), Zlength(Tail) + 1, app(Tail, cons(128, nil))) *
		        UCharArray::undef_full(
		          &(ctx->block[Zlength(Tail) + 1]), 55 - Zlength(Tail)) *
		        UCharArray::undef_full(&(ctx->block[56]), 8) *
		        store_uint64(&(ctx->num), Zlength(Tail)) *
		        UCharArray::undef_full(digest, 32) *
		        store_sm3_ti
		 */
		memset(ctx->block + ctx->num + 1, 0, SM3_BLOCK_SIZE - ctx->num - 9);
		/*@ do open_store_bytes */
		/*@ do merge_full_byte_regions */
	}
	else
	{
		/*@ Assert
		      exists State Tail,
		        u8_list_bounded(Message) &&
		        Zlength(Message) < SM3_MAX_BYTES &&
		        Tail == sm3_tail(Message) &&
		        56 <= Zlength(Tail) && Zlength(Tail) < 64 &&
		        ctx == ctx@pre && digest == digest@pre &&
		        i == 0 && pdigest == digest@pre && aligned_4(pdigest) &&
		        count == &(ctx->block[56]) &&
		        State == sm3_compress_bytes(SM3_IV, sm3_full_bytes(Message)) &&
		        aligned_4(&(ctx->block)) &&
		        store_u32_words(&(ctx->digest), 8, State) *
		        store_uint64(&(ctx->nblocks), Zlength(Message) / 64) *
		        UCharArray::full(
		          &(ctx->block), Zlength(Tail) + 1, app(Tail, cons(128, nil))) *
		        UCharArray::undef_full(
		          &(ctx->block[Zlength(Tail) + 1]), 63 - Zlength(Tail)) *
		        store_uint64(&(ctx->num), Zlength(Tail)) *
		        UCharArray::undef_full(digest, 32) *
		        store_sm3_ti
		 */
		memset(ctx->block + ctx->num + 1, 0, SM3_BLOCK_SIZE - ctx->num - 1);
		/*@ do open_store_bytes */
		/*@ Assert
		      exists State Tail BlockBytes,
		        u8_list_bounded(Message) &&
		        Zlength(Message) < SM3_MAX_BYTES &&
		        Tail == sm3_tail(Message) &&
		        56 <= Zlength(Tail) && Zlength(Tail) < 64 &&
		        BlockBytes == app(Tail,
		          app(cons(128, nil), repeat_Z(0, 63 - Zlength(Tail)))) &&
		        Zlength(BlockBytes) == 64 && u8_list_bounded(BlockBytes) &&
		        ctx == ctx@pre && digest == digest@pre &&
		        i == 0 && pdigest == digest@pre && aligned_4(pdigest) &&
		        count == &(ctx->block[56]) &&
		        State == sm3_compress_bytes(SM3_IV, sm3_full_bytes(Message)) &&
		        aligned_4(&(ctx->block)) &&
		        sm3_compress_input_aligned(&(ctx->block), 1) &&
		        store_u32_words(&(ctx->digest), 8, State) *
		        store_uint64(&(ctx->nblocks), Zlength(Message) / 64) *
		        UCharArray::full(&(ctx->block), 64, BlockBytes) *
		        store_uint64(&(ctx->num), Zlength(Tail)) *
			        UCharArray::undef_full(digest, 32) *
			        store_sm3_ti
		 */
			/*@ do open_store_u32_words */
			sm3_compress(ctx->digest, ctx->block, 1);
			/*@ do open_store_bytes */
			/*@ Assert
		      exists State BlockBytes Tail,
		        u8_list_bounded(Message) &&
		        Zlength(Message) < SM3_MAX_BYTES &&
		        Tail == sm3_tail(Message) &&
		        56 <= Zlength(Tail) && Zlength(Tail) < 64 &&
		        BlockBytes == sublist(
		          0, Zlength(sm3_final_bytes(Message)) - 64,
		          sm3_final_bytes(Message)) &&
		        ctx == ctx@pre && digest == digest@pre &&
		        i == 0 && pdigest == digest@pre && aligned_4(pdigest) &&
		        count == &(ctx->block[56]) &&
		        Zlength(BlockBytes) == 64 && u8_list_bounded(BlockBytes) &&
		        State == sm3_compress_bytes(
		          SM3_IV, app(sm3_full_bytes(Message), BlockBytes)) &&
		        aligned_4(&(ctx->block)) &&
		        store_u32_words(&(ctx->digest), 8, State) *
		        store_uint64(&(ctx->nblocks), Zlength(Message) / 64) *
		        UCharArray::undef_full(
		          &(ctx->block[Zlength(Tail) - Zlength(Tail)]), 56) *
		        UCharArray::full(
		          &(ctx->block[56]), 8, sublist(56, 64, BlockBytes)) *
		        store_uint64(&(ctx->num), Zlength(Tail)) *
		        UCharArray::undef_full(digest, 32) *
		        store_sm3_ti
		 */
		memset(ctx->block, 0, SM3_BLOCK_SIZE - 8);
		/*@ do open_store_bytes */
		/*@ do merge_full_byte_regions */
	}

	/*@ Assert
	      exists State Prefix56 Tail,
	        u8_list_bounded(Message) &&
	        Zlength(Message) < SM3_MAX_BYTES &&
	        Tail == sm3_tail(Message) &&
	        0 <= Zlength(Tail) && Zlength(Tail) < 64 &&
	        Zlength(Prefix56) == 56 && u8_list_bounded(Prefix56) &&
	        Prefix56 == sublist(
	          Zlength(sm3_final_bytes(Message)) - 64,
	          Zlength(sm3_final_bytes(Message)) - 8,
	          sm3_final_bytes(Message)) &&
	        State == sm3_compress_bytes(SM3_IV,
	          app(sm3_full_bytes(Message),
	            sublist(0, Zlength(sm3_final_bytes(Message)) - 64,
	              sm3_final_bytes(Message)))) &&
	        ctx == ctx@pre && digest == digest@pre &&
	        i == 0 && pdigest == digest@pre && aligned_4(pdigest) &&
	        count == &(ctx->block[56]) &&
	        aligned_4(count) &&
	        store_u32_words(&(ctx->digest), 8, State) *
	        store_uint64(&(ctx->nblocks), Zlength(Message) / 64) *
	        UCharArray::full(&(ctx->block), 56, Prefix56) *
	        UIntArray::undef_full(count, 2) *
	        store_uint64(&(ctx->num), Zlength(Tail)) *
	        UCharArray::undef_full(digest, 32) *
	        store_sm3_ti
	 */
	count[0] = (uint32_t)(cpu_to_be32((ctx->nblocks) >> 23));
	count[1] = (uint32_t)(cpu_to_be32((uint32_t)((ctx->nblocks << 9) + (ctx->num << 3))));

	/*@ Assert
	      exists State BlockBytes Tail,
	        u8_list_bounded(Message) &&
	        Zlength(Message) < SM3_MAX_BYTES &&
	        Tail == sm3_tail(Message) &&
	        0 <= Zlength(Tail) && Zlength(Tail) < 64 &&
	        BlockBytes == sublist(
	          Zlength(sm3_final_bytes(Message)) - 64,
	          Zlength(sm3_final_bytes(Message)), sm3_final_bytes(Message)) &&
	        Zlength(BlockBytes) == 64 && u8_list_bounded(BlockBytes) &&
	        State == sm3_compress_bytes(SM3_IV,
	          app(sm3_full_bytes(Message),
	            sublist(0, Zlength(sm3_final_bytes(Message)) - 64,
	              sm3_final_bytes(Message)))) &&
	        ctx == ctx@pre && digest == digest@pre &&
	        i == 0 && pdigest == digest@pre && aligned_4(pdigest) &&
	        count == &(ctx->block[56]) && aligned_4(count) &&
	        sm3_compress_input_aligned(&(ctx->block), 1) &&
	        store_u32_words(&(ctx->digest), 8, State) *
	        store_uint64(&(ctx->nblocks), Zlength(Message) / 64) *
	        UCharArray::full(&(ctx->block), 64, BlockBytes) *
	        store_uint64(&(ctx->num), Zlength(Tail)) *
	        UCharArray::undef_full(digest, 32) *
	        store_sm3_ti
	 */
		/*@ do open_store_u32_words */
		sm3_compress(ctx->digest, ctx->block, 1);
		/*@ do open_store_bytes */
		/*@ Assert
	      exists FinalState BlockBytes Tail,
	        Tail == sm3_tail(Message) &&
	        0 <= Zlength(Tail) && Zlength(Tail) < 64 &&
	        FinalState == sm3_digest_words(Message) &&
	        Zlength(FinalState) == 8 &&
	        limb_list_bounded(SM3_WORD_MODULUS, FinalState) &&
	        Zlength(BlockBytes) == 64 && u8_list_bounded(BlockBytes) &&
	        ctx == ctx@pre && digest == digest@pre &&
	        i == 0 && pdigest == digest@pre && aligned_4(pdigest) &&
	        count == &(ctx->block[56]) &&
	        store_u32_words(&(ctx->digest), 8, FinalState) *
	        store_uint64(&(ctx->nblocks), Zlength(Message) / 64) *
	        UCharArray::full(&(ctx->block), 64, BlockBytes) *
	        store_uint64(&(ctx->num), Zlength(Tail)) *
	        UCharArray::undef_full(digest, 32) *
	        store_sm3_ti
	 */
	/*@ do start_store_byte_prefix */

	/*@ Inv Assert
	      exists FinalState BlockBytes OutputBytes Tail,
	        Tail == sm3_tail(Message) &&
	        0 <= Zlength(Tail) && Zlength(Tail) < 64 &&
	        FinalState == sm3_digest_words(Message) &&
	        Zlength(FinalState) == 8 &&
	        limb_list_bounded(SM3_WORD_MODULUS, FinalState) &&
	        Zlength(BlockBytes) == 64 && u8_list_bounded(BlockBytes) &&
	        0 <= i && i <= 8 &&
	        OutputBytes == sublist(0, 4 * i, sm3_digest_bytes(Message)) &&
	        Zlength(OutputBytes) == 4 * i && u8_list_bounded(OutputBytes) &&
	        ctx == ctx@pre && digest == digest@pre &&
	        pdigest == digest@pre && aligned_4(pdigest) &&
	        count == &(ctx->block[56]) &&
	        store_u32_words(&(ctx->digest), 8, FinalState) *
	        store_uint64(&(ctx->nblocks), Zlength(Message) / 64) *
	        UCharArray::full(&(ctx->block), 64, BlockBytes) *
	        store_uint64(&(ctx->num), Zlength(Tail)) *
	        store_byte_prefix(digest, 32, OutputBytes) *
	        store_sm3_ti
	 */
	for (i = 0; i < 8; ++i)
	{
		pdigest[i] = cpu_to_be32(ctx->digest[i]);
	}
	/*@ Assert
	      exists FinalState BlockBytes Tail,
	        Tail == sm3_tail(Message) &&
	        FinalState == sm3_digest_words(Message) &&
	        Zlength(BlockBytes) == 64 && u8_list_bounded(BlockBytes) &&
	        ctx == ctx@pre && digest == digest@pre && i == 8 &&
	        pdigest == digest@pre && count == &(ctx->block[56]) &&
	        store_u32_words(&(ctx->digest), 8, FinalState) *
	        store_uint64(&(ctx->nblocks), Zlength(Message) / 64) *
	        UCharArray::full(&(ctx->block), 64, BlockBytes) *
	        store_uint64(&(ctx->num), Zlength(Tail)) *
	        store_bytes(digest, 32, sm3_digest_bytes(Message)) *
	        store_sm3_ti
	 */
	/*@ do close_sm3_ctx_shape */
}
