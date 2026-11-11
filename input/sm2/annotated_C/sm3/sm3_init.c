#include "sm3.h"
/*@ include strategies "../strategy/byte_memory_views.strategies" */
/*@ include strategies "../strategy/sm3_ctx_views.strategies" */


void sm3_init(SM3_CTX *ctx)
/*@ Require
      undef_sm3_ctx(ctx)
    Ensure
      store_sm3_ctx(ctx, nil)
 */
{
	/*@ undef_sm3_ctx(ctx)
	    which implies
	      UIntArray::undef_full(&(ctx->digest), 8) *
	      undef_data_at(&(ctx->nblocks), unsigned long long) *
	      UCharArray::undef_full(&(ctx->block), 64) *
	      undef_data_at(&(ctx->num), unsigned long long)
	    by open_undef_sm3_ctx
	 */
	ctx->digest[0] = 0x7380166F;
	ctx->digest[1] = 0x4914B2B9;
	ctx->digest[2] = 0x172442D7;
	ctx->digest[3] = 0xDA8A0600;
	ctx->digest[4] = 0xA96F30BC;
	ctx->digest[5] = 0x163138AA;
	ctx->digest[6] = 0xE38DEE4D;
	ctx->digest[7] = 0xB0FB0E4E;

	ctx->nblocks = 0;
	ctx->num = 0;
}
