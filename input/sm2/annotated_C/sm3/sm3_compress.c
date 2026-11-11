/* Verification copy of YCrypt/sm3/sm3.c::sm3_compress. */

#include "sm3.h"
/*@ include strategies "../strategy/byte_memory_views.strategies" */
/*@ include strategies "../strategy/sm3_word_views.strategies" */
/*@ Extern Coq
      (sm3_rounds_aux : nat -> Z -> list Z -> list Z -> list Z)
      (Z::to_nat : Z -> nat)
 */

#ifndef NULL
#define NULL 0
#endif

#ifndef AVX_SM3

#define ROTL32(X,n)  (((X)<<(n%32)) | ((X)>>(32-(n%32))))

#define P0(x) ((x) ^  ROTL32((x),9)  ^ ROTL32((x),17))
#define P1(x) ((x) ^  ROTL32((x),15) ^ ROTL32((x),23))

#define FF0(x,y,z) ( (x) ^ (y) ^ (z) )
#define FF1(x,y,z) (((x) & (y)) | ( (x) & (z)) | ( (y) & (z)))

#define GG0(x,y,z) ( (x) ^ (y) ^ (z) )
#define GG1(x,y,z) (((x) & (y)) | ( (~(x)) & (z)) )

/* Ti table, T[i] = ROT(T, i). */
static uint32_t Ti[64] =
{
	0x79CC4519, 0xF3988A32, 0xE7311465, 0xCE6228CB,
	0x9CC45197, 0x3988A32F, 0x7311465E, 0xE6228CBC,
	0xCC451979, 0x988A32F3, 0x311465E7, 0x6228CBCE,
	0xC451979C, 0x88A32F39, 0x11465E73, 0x228CBCE6,
	0x9D8A7A87, 0x3B14F50F, 0x7629EA1E, 0xEC53D43C,
	0xD8A7A879, 0xB14F50F3, 0x629EA1E7, 0xC53D43CE,
	0x8A7A879D, 0x14F50F3B, 0x29EA1E76, 0x53D43CEC,
	0xA7A879D8, 0x4F50F3B1, 0x9EA1E762, 0x3D43CEC5,
	0x7A879D8A, 0xF50F3B14, 0xEA1E7629, 0xD43CEC53,
	0xA879D8A7, 0x50F3B14F, 0xA1E7629E, 0x43CEC53D,
	0x879D8A7A, 0x0F3B14F5, 0x1E7629EA, 0x3CEC53D4,
	0x79D8A7A8, 0xF3B14F50, 0xE7629EA1, 0xCEC53D43,
	0x9D8A7A87, 0x3B14F50F, 0x7629EA1E, 0xEC53D43C,
	0xD8A7A879, 0xB14F50F3, 0x629EA1E7, 0xC53D43CE,
	0x8A7A879D, 0x14F50F3B, 0x29EA1E76, 0x53D43CEC,
	0xA7A879D8, 0x4F50F3B1, 0x9EA1E762, 0x3D43CEC5
};

/*
 * The A-H, k, SS1 and SS2 pointers refer to the distinct local variables
 * used by sm3_compress.  Keeping k/SS1/SS2 as explicit output parameters
 * preserves the complete local-state effect of the original macro.
 */
static inline void ONE_ROUND_16(
	uint32_t *A, uint32_t *B, uint32_t *C, uint32_t *D,
	uint32_t *E, uint32_t *F, uint32_t *G, uint32_t *H,
	size_t idx, const uint32_t W[68],
	uint32_t *k, uint32_t *SS1, uint32_t *SS2)
/*@ With a b c d e f g h Words
    Require
      0 <= idx && idx < 16 &&
      Zlength(Words) == 68 &&
      data_at(A, unsigned int, a) * data_at(B, unsigned int, b) *
      data_at(C, unsigned int, c) * data_at(D, unsigned int, d) *
      data_at(E, unsigned int, e) * data_at(F, unsigned int, f) *
      data_at(G, unsigned int, g) * data_at(H, unsigned int, h) *
      UIntArray::full(W, 68, Words) *
      UIntArray::full(Ti, 64, SM3_TI_VALUES) *
      undef_data_at(k, unsigned int) * undef_data_at(SS1, unsigned int) *
      undef_data_at(SS2, unsigned int)
    Ensure
      exists ao bo co dout eo fo go ho kval ss1v ss2v,
        cons(dout, cons(ao, cons(bo, cons(co,
          cons(ho, cons(eo, cons(fo, cons(go, nil)))))))) ==
          sm3_rounds_aux(Z::to_nat(1), idx, Words,
            cons(a, cons(b, cons(c, cons(d,
              cons(e, cons(f, cons(g, cons(h, nil))))))))) &&
        data_at(A, unsigned int, ao) * data_at(B, unsigned int, bo) *
        data_at(C, unsigned int, co) * data_at(D, unsigned int, dout) *
        data_at(E, unsigned int, eo) * data_at(F, unsigned int, fo) *
        data_at(G, unsigned int, go) * data_at(H, unsigned int, ho) *
        UIntArray::full(W, 68, Words) *
        UIntArray::full(Ti, 64, SM3_TI_VALUES) *
        data_at(k, unsigned int, kval) * data_at(SS1, unsigned int, ss1v) *
        data_at(SS2, unsigned int, ss2v)
 */
{
	*SS1 = ROTL32(*A, 12) + *E + Ti[idx];
	*SS1 = ROTL32(*SS1, 7);
	*SS2 = *SS1 ^ ROTL32(*A, 12);
	*k = W[idx];
	*D = FF0(*A, *B, *C) + *D + *SS2 + (*k ^ W[idx + 4]);
	*H = GG0(*E, *F, *G) + *H + *SS1 + *k;
	*H = P0(*H);
	*B = ROTL32(*B, 9);
	*F = ROTL32(*F, 19);
}

static inline void ONE_ROUNDS_16(
	uint32_t *A, uint32_t *B, uint32_t *C, uint32_t *D,
	uint32_t *E, uint32_t *F, uint32_t *G, uint32_t *H,
	size_t idx, const uint32_t W[68],
	uint32_t *k, uint32_t *SS1, uint32_t *SS2)
/*@ With a b c d e f g h Words
    Require
      0 <= idx && idx <= 12 && idx % 4 == 0 &&
      Zlength(Words) == 68 &&
      data_at(A, unsigned int, a) * data_at(B, unsigned int, b) *
      data_at(C, unsigned int, c) * data_at(D, unsigned int, d) *
      data_at(E, unsigned int, e) * data_at(F, unsigned int, f) *
      data_at(G, unsigned int, g) * data_at(H, unsigned int, h) *
      UIntArray::full(W, 68, Words) *
      UIntArray::full(Ti, 64, SM3_TI_VALUES) *
      undef_data_at(k, unsigned int) * undef_data_at(SS1, unsigned int) *
      undef_data_at(SS2, unsigned int)
    Ensure
      exists ao bo co dout eo fo go ho kval ss1v ss2v,
        cons(ao, cons(bo, cons(co, cons(dout,
          cons(eo, cons(fo, cons(go, cons(ho, nil)))))))) ==
          sm3_rounds_aux(Z::to_nat(4), idx, Words,
            cons(a, cons(b, cons(c, cons(d,
              cons(e, cons(f, cons(g, cons(h, nil))))))))) &&
        data_at(A, unsigned int, ao) * data_at(B, unsigned int, bo) *
        data_at(C, unsigned int, co) * data_at(D, unsigned int, dout) *
        data_at(E, unsigned int, eo) * data_at(F, unsigned int, fo) *
        data_at(G, unsigned int, go) * data_at(H, unsigned int, ho) *
        UIntArray::full(W, 68, Words) *
        UIntArray::full(Ti, 64, SM3_TI_VALUES) *
        data_at(k, unsigned int, kval) * data_at(SS1, unsigned int, ss1v) *
        data_at(SS2, unsigned int, ss2v)
 */
{
	ONE_ROUND_16(A, B, C, D, E, F, G, H,
		idx, W, k, SS1, SS2);
	ONE_ROUND_16(D, A, B, C, H, E, F, G,
		idx + 1, W, k, SS1, SS2);
	ONE_ROUND_16(C, D, A, B, G, H, E, F,
		idx + 2, W, k, SS1, SS2);
	ONE_ROUND_16(B, C, D, A, F, G, H, E,
		idx + 3, W, k, SS1, SS2);
}

static inline void ONE_ROUND_64(
	uint32_t *A, uint32_t *B, uint32_t *C, uint32_t *D,
	uint32_t *E, uint32_t *F, uint32_t *G, uint32_t *H,
	size_t idx, const uint32_t W[68],
	uint32_t *k, uint32_t *SS1, uint32_t *SS2)
/*@ With a b c d e f g h Words
    Require
      16 <= idx && idx < 64 &&
      Zlength(Words) == 68 &&
      data_at(A, unsigned int, a) * data_at(B, unsigned int, b) *
      data_at(C, unsigned int, c) * data_at(D, unsigned int, d) *
      data_at(E, unsigned int, e) * data_at(F, unsigned int, f) *
      data_at(G, unsigned int, g) * data_at(H, unsigned int, h) *
      UIntArray::full(W, 68, Words) *
      UIntArray::full(Ti, 64, SM3_TI_VALUES) *
      undef_data_at(k, unsigned int) * undef_data_at(SS1, unsigned int) *
      undef_data_at(SS2, unsigned int)
    Ensure
      exists ao bo co dout eo fo go ho kval ss1v ss2v,
        cons(dout, cons(ao, cons(bo, cons(co,
          cons(ho, cons(eo, cons(fo, cons(go, nil)))))))) ==
          sm3_rounds_aux(Z::to_nat(1), idx, Words,
            cons(a, cons(b, cons(c, cons(d,
              cons(e, cons(f, cons(g, cons(h, nil))))))))) &&
        data_at(A, unsigned int, ao) * data_at(B, unsigned int, bo) *
        data_at(C, unsigned int, co) * data_at(D, unsigned int, dout) *
        data_at(E, unsigned int, eo) * data_at(F, unsigned int, fo) *
        data_at(G, unsigned int, go) * data_at(H, unsigned int, ho) *
        UIntArray::full(W, 68, Words) *
        UIntArray::full(Ti, 64, SM3_TI_VALUES) *
        data_at(k, unsigned int, kval) * data_at(SS1, unsigned int, ss1v) *
        data_at(SS2, unsigned int, ss2v)
 */
{
	*SS1 = ROTL32(*A, 12) + *E + Ti[idx];
	*SS1 = ROTL32(*SS1, 7);
	*SS2 = *SS1 ^ ROTL32(*A, 12);
	*k = W[idx];
	*D = FF1(*A, *B, *C) + *D + *SS2 + (*k ^ W[idx + 4]);
	*H = GG1(*E, *F, *G) + *H + *SS1 + *k;
	*H = P0(*H);
	*B = ROTL32(*B, 9);
	*F = ROTL32(*F, 19);
}

static inline void ONE_ROUNDS_64(
	uint32_t *A, uint32_t *B, uint32_t *C, uint32_t *D,
	uint32_t *E, uint32_t *F, uint32_t *G, uint32_t *H,
	size_t idx, const uint32_t W[68],
	uint32_t *k, uint32_t *SS1, uint32_t *SS2)
/*@ With a b c d e f g h Words
    Require
      16 <= idx && idx <= 60 && idx % 4 == 0 &&
      Zlength(Words) == 68 &&
      data_at(A, unsigned int, a) * data_at(B, unsigned int, b) *
      data_at(C, unsigned int, c) * data_at(D, unsigned int, d) *
      data_at(E, unsigned int, e) * data_at(F, unsigned int, f) *
      data_at(G, unsigned int, g) * data_at(H, unsigned int, h) *
      UIntArray::full(W, 68, Words) *
      UIntArray::full(Ti, 64, SM3_TI_VALUES) *
      undef_data_at(k, unsigned int) * undef_data_at(SS1, unsigned int) *
      undef_data_at(SS2, unsigned int)
    Ensure
      exists ao bo co dout eo fo go ho kval ss1v ss2v,
        cons(ao, cons(bo, cons(co, cons(dout,
          cons(eo, cons(fo, cons(go, cons(ho, nil)))))))) ==
          sm3_rounds_aux(Z::to_nat(4), idx, Words,
            cons(a, cons(b, cons(c, cons(d,
              cons(e, cons(f, cons(g, cons(h, nil))))))))) &&
        data_at(A, unsigned int, ao) * data_at(B, unsigned int, bo) *
        data_at(C, unsigned int, co) * data_at(D, unsigned int, dout) *
        data_at(E, unsigned int, eo) * data_at(F, unsigned int, fo) *
        data_at(G, unsigned int, go) * data_at(H, unsigned int, ho) *
        UIntArray::full(W, 68, Words) *
        UIntArray::full(Ti, 64, SM3_TI_VALUES) *
        data_at(k, unsigned int, kval) * data_at(SS1, unsigned int, ss1v) *
        data_at(SS2, unsigned int, ss2v)
 */
{
	ONE_ROUND_64(A, B, C, D, E, F, G, H,
		idx, W, k, SS1, SS2);
	ONE_ROUND_64(D, A, B, C, H, E, F, G,
		idx + 1, W, k, SS1, SS2);
	ONE_ROUND_64(C, D, A, B, G, H, E, F,
		idx + 2, W, k, SS1, SS2);
	ONE_ROUND_64(B, C, D, A, F, G, H, E,
		idx + 3, W, k, SS1, SS2);
}

void sm3_compress(u4 digest[8], const u1* block, size_t nblocks)
/*@ With State Blocks
    Require
      sm3_compress_input_aligned(block, nblocks) &&
      store_u32_words(digest, 8, State) *
      store_bytes(block, 64 * nblocks, Blocks) *
      store_sm3_ti
    Ensure
      store_u32_words(
        digest, 8, sm3_compress_bytes(State, Blocks)) *
      store_bytes(block, 64 * nblocks, Blocks) *
      store_sm3_ti
 */
{
	size_t i = 0, j = 0;
	uint32_t k;
	uint32_t W[68] = { 0 };
	uint32_t *pblock = NULL;
	uint32_t A, B, C, D, E, F, G, H;
	uint32_t SS1, SS2;

	/*@ store_u32_words(digest, 8, State)
	    which implies
	      Zlength(State) == 8 &&
	      limb_list_bounded(SM3_WORD_MODULUS, State) &&
	      UIntArray::full(digest, 8, State)
	    by open_store_u32_words
	 */
	/*@ do open_store_bytes */
	A = digest[0]; B = digest[1]; C = digest[2]; D = digest[3];
	E = digest[4]; F = digest[5]; G = digest[6]; H = digest[7];
	/*@ store_sm3_ti
	    which implies
	      Zlength(SM3_TI_VALUES) == 64 &&
	      limb_list_bounded(SM3_WORD_MODULUS, SM3_TI_VALUES) &&
	      UIntArray::full(Ti, 64, SM3_TI_VALUES)
	 */

	/*@ Inv
	    exists Words CurState,
	      0 <= i && i <= nblocks@pre &&
	      nblocks == nblocks@pre &&
	      block == block@pre + 64 * i &&
	      digest == digest@pre &&
	      CurState == sm3_compress_bytes(State,
	        sublist(0, 64 * i, Blocks)) &&
	      Zlength(CurState) == 8 &&
	      limb_list_bounded(SM3_WORD_MODULUS, CurState) &&
	      Zlength(State) == 8 &&
	      limb_list_bounded(SM3_WORD_MODULUS, State) &&
	      Zlength(Blocks) == 64 * nblocks@pre &&
	      u8_list_bounded(Blocks) &&
	      (nblocks@pre != 0 => aligned_4(block@pre)) &&
	      Zlength(SM3_TI_VALUES) == 64 &&
	      limb_list_bounded(SM3_WORD_MODULUS, SM3_TI_VALUES) &&
	      Zlength(Words) == 68 &&
	      cons(A, cons(B, cons(C, cons(D,
	        cons(E, cons(F, cons(G, cons(H, nil)))))))) == CurState &&
	      UIntArray::full(W, 68, Words) *
	      UIntArray::full(Ti, 64, SM3_TI_VALUES) *
	      UIntArray::full(digest@pre, 8, CurState) *
	      UCharArray::full(block@pre, 64 * nblocks@pre, Blocks) *
	      has_permission(&k) * has_permission(&pblock) *
	      has_permission(&j) * has_permission(&SS1) * has_permission(&SS2)
	 */
	for (i = 0; i < nblocks; i++)
	{
		pblock = (uint32_t *)block;
		block += SM3_BLOCK_SIZE;

		/*@ (nblocks@pre != 0 => aligned_4(block@pre)) &&
		    0 <= i && i < nblocks@pre &&
		    pblock == block@pre + 64 * i &&
		    UCharArray::full(block@pre, 64 * nblocks@pre, Blocks)
		    which implies
		      pblock == block@pre + 64 * i && aligned_4(pblock) &&
		      UCharArray::full(block@pre, 64 * i,
		        sublist(0, 64 * i, Blocks)) *
		      UCharArray::full(block@pre + 64 * i, 64,
		        sublist(64 * i, 64 * i + 64, Blocks)) *
		      UCharArray::full(block@pre + 64 * i + 64,
		        64 * nblocks@pre - 64 * i - 64,
		        sublist(64 * i + 64, 64 * nblocks@pre, Blocks))
		 */
		/*@ Inv
		    exists Words CurState BlockIndex,
		      0 <= j && j <= 16 && i == BlockIndex &&
		      0 <= BlockIndex && BlockIndex < nblocks@pre &&
		      nblocks == nblocks@pre &&
		      Zlength(Blocks) == 64 * nblocks@pre && u8_list_bounded(Blocks) &&
		      pblock == block@pre + 64 * BlockIndex && block == pblock + 16 &&
		      aligned_4(pblock) &&
		      CurState == sm3_compress_bytes(State,
		        sublist(0, 64 * BlockIndex, Blocks)) &&
		      Zlength(CurState) == 8 &&
		      limb_list_bounded(SM3_WORD_MODULUS, CurState) &&
		      cons(A, cons(B, cons(C, cons(D,
		        cons(E, cons(F, cons(G, cons(H, nil)))))))) == CurState &&
		      Zlength(sublist(64 * BlockIndex,
		        64 * BlockIndex + 64, Blocks)) == 64 &&
		      u8_list_bounded(sublist(64 * BlockIndex,
		        64 * BlockIndex + 64, Blocks)) &&
		      Zlength(Words) == 68 &&
		      sublist(0, j, Words) == sublist(0, j,
		        sm3_block_words(sublist(64 * BlockIndex,
		          64 * BlockIndex + 64, Blocks))) &&
		      UIntArray::full(W, 68, Words) *
		      UIntArray::full(digest@pre, 8, CurState) *
		      UCharArray::full(block@pre, 64 * BlockIndex,
		        sublist(0, 64 * BlockIndex, Blocks)) *
		      UCharArray::full(block@pre + 64 * BlockIndex, 64,
		        sublist(64 * BlockIndex, 64 * BlockIndex + 64, Blocks)) *
		      UCharArray::full(block@pre + 64 * BlockIndex + 64,
		        64 * nblocks@pre - 64 * BlockIndex - 64,
		        sublist(64 * BlockIndex + 64, 64 * nblocks@pre, Blocks))
		 */
		for (j = 0; j < 16; j++)
		{
			SS2 = pblock[j];
			W[j] = cpu_to_be32(SS2);
		}

		/*@ exists BlockIndex,
		      i == BlockIndex && 0 <= BlockIndex && BlockIndex < nblocks@pre &&
		      nblocks == nblocks@pre && Zlength(Blocks) == 64 * nblocks@pre &&
		      u8_list_bounded(Blocks) && pblock == block@pre + 64 * BlockIndex &&
		      block == pblock + 16 && aligned_4(pblock) &&
		      UCharArray::full(block@pre, 64 * BlockIndex,
		        sublist(0, 64 * BlockIndex, Blocks)) *
		      UCharArray::full(block@pre + 64 * BlockIndex, 64,
		        sublist(64 * BlockIndex, 64 * BlockIndex + 64, Blocks)) *
		      UCharArray::full(block@pre + 64 * BlockIndex + 64,
		        64 * nblocks@pre - 64 * BlockIndex - 64,
		        sublist(64 * BlockIndex + 64, 64 * nblocks@pre, Blocks))
		    which implies
		      exists BlockIndex,
		        i == BlockIndex && 0 <= BlockIndex && BlockIndex < nblocks@pre &&
		        nblocks == nblocks@pre && Zlength(Blocks) == 64 * nblocks@pre &&
		        u8_list_bounded(Blocks) && pblock == block@pre + 64 * BlockIndex &&
		        block == pblock + 16 && aligned_4(pblock) &&
		        UCharArray::full(
		          block@pre, 64 * nblocks@pre, Blocks)
		 */
		/*@ Inv
		    exists Words CurState,
		      16 <= j && j <= 68 && 0 <= i && i < nblocks@pre &&
		      nblocks == nblocks@pre && pblock == block@pre + 64 * i &&
		      block == pblock + 16 && aligned_4(pblock) &&
		      CurState == sm3_compress_bytes(State, sublist(0, 64 * i, Blocks)) &&
		      Zlength(CurState) == 8 &&
		      limb_list_bounded(SM3_WORD_MODULUS, CurState) &&
		      cons(A, cons(B, cons(C, cons(D,
		        cons(E, cons(F, cons(G, cons(H, nil)))))))) == CurState &&
		      Zlength(Blocks) == 64 * nblocks@pre && u8_list_bounded(Blocks) &&
		      Zlength(sublist(64 * i, 64 * i + 64, Blocks)) == 64 &&
		      u8_list_bounded(sublist(64 * i, 64 * i + 64, Blocks)) &&
		      Zlength(Words) == 68 &&
		      sublist(0, j, Words) == sublist(0, j,
		        sm3_expand_words(sublist(64 * i, 64 * i + 64, Blocks))) &&
		      UIntArray::full(W, 68, Words) *
		      UIntArray::full(digest@pre, 8, CurState) *
		      UCharArray::full(
		        block@pre, 64 * nblocks@pre, Blocks)
		 */
		for (j = 16; j < 68; j++)
		{
			SS2 = W[j - 3];
			SS1 = W[j - 16] ^ W[j - 9] ^ ROTL32(SS2, 15);
			SS2 = W[j - 13];
			W[j] = P1(SS1) ^ ROTL32(SS2, 7) ^ W[j - 6];
		}
		ONE_ROUNDS_16(&A, &B, &C, &D, &E, &F, &G, &H,
			0, (const uint32_t *)&W, &k, &SS1, &SS2);
		ONE_ROUNDS_16(&A, &B, &C, &D, &E, &F, &G, &H,
			4, (const uint32_t *)&W, &k, &SS1, &SS2);
		ONE_ROUNDS_16(&A, &B, &C, &D, &E, &F, &G, &H,
			8, (const uint32_t *)&W, &k, &SS1, &SS2);
		ONE_ROUNDS_16(&A, &B, &C, &D, &E, &F, &G, &H,
			12, (const uint32_t *)&W, &k, &SS1, &SS2);

		ONE_ROUNDS_64(&A, &B, &C, &D, &E, &F, &G, &H,
			16, (const uint32_t *)&W, &k, &SS1, &SS2);
		ONE_ROUNDS_64(&A, &B, &C, &D, &E, &F, &G, &H,
			20, (const uint32_t *)&W, &k, &SS1, &SS2);
		ONE_ROUNDS_64(&A, &B, &C, &D, &E, &F, &G, &H,
			24, (const uint32_t *)&W, &k, &SS1, &SS2);
		ONE_ROUNDS_64(&A, &B, &C, &D, &E, &F, &G, &H,
			28, (const uint32_t *)&W, &k, &SS1, &SS2);
		ONE_ROUNDS_64(&A, &B, &C, &D, &E, &F, &G, &H,
			32, (const uint32_t *)&W, &k, &SS1, &SS2);
		ONE_ROUNDS_64(&A, &B, &C, &D, &E, &F, &G, &H,
			36, (const uint32_t *)&W, &k, &SS1, &SS2);
		ONE_ROUNDS_64(&A, &B, &C, &D, &E, &F, &G, &H,
			40, (const uint32_t *)&W, &k, &SS1, &SS2);
		ONE_ROUNDS_64(&A, &B, &C, &D, &E, &F, &G, &H,
			44, (const uint32_t *)&W, &k, &SS1, &SS2);
		ONE_ROUNDS_64(&A, &B, &C, &D, &E, &F, &G, &H,
			48, (const uint32_t *)&W, &k, &SS1, &SS2);
		ONE_ROUNDS_64(&A, &B, &C, &D, &E, &F, &G, &H,
			52, (const uint32_t *)&W, &k, &SS1, &SS2);
		ONE_ROUNDS_64(&A, &B, &C, &D, &E, &F, &G, &H,
			56, (const uint32_t *)&W, &k, &SS1, &SS2);
		ONE_ROUNDS_64(&A, &B, &C, &D, &E, &F, &G, &H,
			60, (const uint32_t *)&W, &k, &SS1, &SS2);

		A = digest[0] ^ A;
		digest[0] = A;
		B = digest[1] ^ B;
		digest[1] = B;
		C = digest[2] ^ C;
		digest[2] = C;
		D = digest[3] ^ D;
		digest[3] = D;
		E = digest[4] ^ E;
		digest[4] = E;
		F = digest[5] ^ F;
		digest[5] = F;
		G = digest[6] ^ G;
		digest[6] = G;
		H = digest[7] ^ H;
		digest[7] = H;
	}
}

#endif /* !AVX_SM3 */
