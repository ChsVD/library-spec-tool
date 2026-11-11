#ifndef SM3_H
#define SM3_H

#include "dataType.h"

#define SM3_DIGEST_LENGTH 32
#define SM3_BLOCK_SIZE 64
#define cpu_to_be32(v) \
	(((v)>>24) | (((v)>>8)&0xff00) | (((v)<<8)&0xff0000) | ((v)<<24))

typedef unsigned int uint32_t;
typedef unsigned char uint8_t;

typedef struct _SM3_CTX
{
	uint32_t digest[8];
	size_t nblocks;
	uint8_t block[SM3_BLOCK_SIZE];
	size_t num;
} SM3_CTX;

/*@ Import Coq Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def
 */

/*@ Extern Coq
      (aligned_4 : Z -> Prop)
      (u8_list_value : list Z -> Z)
      (u8_list_bounded : list Z -> Prop)
      (limb_list_bounded : Z -> list Z -> Prop)
      (store_bytes : Z -> Z -> list Z -> Assertion)
      (byte_reverse_loop_state : list Z -> list Z -> Z -> Prop)
      (SM3_MAX_BYTES : Z)
      (SM3_WORD_MODULUS : Z)
      (SM3_IV : list Z)
      (SM3_TI_VALUES : list Z)
      (valid_sm3_state : list Z -> Prop)
      (byte_swap32 : Z -> Z)
      (sm3_rotl32 : Z -> Z -> Z)
      (sm3_p0 : Z -> Z)
      (sm3_p1 : Z -> Z)
      (sm3_ff : Z -> Z -> Z -> Z -> Z)
      (sm3_gg : Z -> Z -> Z -> Z -> Z)
      (sm3_t : Z -> Z)
      (sm3_round_constant : Z -> Z)
      (sm3_block_word : list Z -> Z -> Z)
      (sm3_block_words : list Z -> list Z)
      (sm3_expand_word : list Z -> Z -> Z)
      (sm3_expand_words : list Z -> list Z)
      (sm3_expanded_word_prime : list Z -> Z -> Z)
      (sm3_round : Z -> list Z -> list Z -> list Z)
      (sm3_rounds : list Z -> list Z -> list Z)
      (sm3_compress_block : list Z -> list Z -> list Z)
      (sm3_compress_bytes : list Z -> list Z -> list Z)
      (u64_to_be_bytes : Z -> list Z)
      (sm3_pad : list Z -> list Z)
      (sm3_digest_words : list Z -> list Z)
      (u32_to_be_bytes : Z -> list Z)
      (sm3_digest_bytes : list Z -> list Z)
      (store_u32_words : Z -> Z -> list Z -> Assertion)
      (store_u32_words_missing_i : Z -> Z -> Z -> list Z -> Assertion)
      (store_byte_prefix : Z -> Z -> list Z -> Assertion)
      (sm3_compress_input_aligned : Z -> Z -> Prop)
      (sm3_digest_input_aligned : Z -> Z -> Prop)
      (sm3_update_data_aligned : Z -> Z -> Z -> Prop)
      (sm3_full_len : list Z -> Z)
      (sm3_full_bytes : list Z -> list Z)
      (sm3_tail : list Z -> list Z)
      (sm3_final_bytes : list Z -> list Z)
      (undef_sm3_ctx : Z -> Assertion)
      (store_sm3_ctx : Z -> list Z -> Assertion)
      (sm3_ctx_full_shape : Z -> Assertion)
      (store_sm3_ti : Assertion)
 */

#endif
