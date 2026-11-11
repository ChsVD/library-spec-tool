Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_update_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_ctx_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_ctx_views_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_streaming_memory_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_streaming_memory_views_strategy_proof.

(*----- Function sm3_update -----*)

Definition sm3_update_safety_wit_1 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH2 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) ,
  ((( &( "offset" ) )) # UInt64  |->_)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ctx ctx_pre Prefix )
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_update_safety_wit_2 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH2 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) ,
  ((( &( "nblock" ) )) # UInt64  |->_)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ctx ctx_pre Prefix )
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_update_safety_wit_3 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH2 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) ,
  ((( &( "left" ) )) # UInt64  |->_)
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ctx ctx_pre Prefix )
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_update_safety_wit_4 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH2 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH3 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH4 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH5 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH6 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH7 : (u8_list_bounded Prefix )) (PreH8 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH9 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH10 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH11 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH12 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> 0)
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition sm3_update_safety_wit_5 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH2 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH3 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH4 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH5 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH6 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH7 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH8 : (u8_list_bounded Prefix )) (PreH9 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH11 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH12 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH13 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) data_len_pre )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_update_safety_wit_6 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH2 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded Chunk )) (PreH4 : ((Zlength (Chunk)) = data_len_pre)) (PreH5 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH6 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH7 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH8 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH9 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH11 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH12 : (u8_list_bounded Prefix )) (PreH13 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH14 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH15 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH16 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH17 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))) (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) (sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)) )
  **  (UCharArray.full data_pre (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_update_safety_wit_7 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH2 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH3 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH4 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH5 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH6 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH9 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH10 : (u8_list_bounded Chunk )) (PreH11 : ((Zlength (Chunk)) = data_len_pre)) (PreH12 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH13 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH15 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH16 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH19 : (u8_list_bounded Prefix )) (PreH20 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH21 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH22 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH23 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_update_safety_wit_8 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH2 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH3 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH4 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH5 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH6 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH9 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH10 : (u8_list_bounded Chunk )) (PreH11 : ((Zlength (Chunk)) = data_len_pre)) (PreH12 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH13 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH15 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH16 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH19 : (u8_list_bounded Prefix )) (PreH20 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH21 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH22 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH23 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_update_safety_wit_9 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH2 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH3 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH4 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH5 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH6 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH9 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH10 : (u8_list_bounded Chunk )) (PreH11 : ((Zlength (Chunk)) = data_len_pre)) (PreH12 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH13 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH15 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH16 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH19 : (u8_list_bounded Prefix )) (PreH20 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH21 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH22 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH23 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sm3_update_safety_wit_10 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH2 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH3 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH4 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH5 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH6 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH9 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH10 : (u8_list_bounded Chunk )) (PreH11 : ((Zlength (Chunk)) = data_len_pre)) (PreH12 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH13 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH15 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH16 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH19 : (u8_list_bounded Prefix )) (PreH20 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH21 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH22 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH23 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix))))) ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) )
  **  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (store_sm3_ti )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> (unsigned_last_nbits ((((Zlength (Prefix)) ÷ 64 ) + 1 )) (64)))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))))
  **  ((( &( "data_len" ) )) # UInt64  |-> (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_update_safety_wit_11 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH2 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH3 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH4 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH5 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH6 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH9 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH10 : (u8_list_bounded Chunk )) (PreH11 : ((Zlength (Chunk)) = data_len_pre)) (PreH12 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH13 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH15 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH16 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH19 : (u8_list_bounded Prefix )) (PreH20 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH21 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH22 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH23 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix))))) ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) )
  **  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (store_sm3_ti )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> 0)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> (unsigned_last_nbits ((((Zlength (Prefix)) ÷ 64 ) + 1 )) (64)))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))))
  **  ((( &( "data_len" ) )) # UInt64  |-> (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ))
|--
  “ (64 <> 0) ”
.

Definition sm3_update_safety_wit_12 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH2 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH3 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH4 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH5 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH6 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH9 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH10 : (u8_list_bounded Chunk )) (PreH11 : ((Zlength (Chunk)) = data_len_pre)) (PreH12 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH13 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH15 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH16 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH19 : (u8_list_bounded Prefix )) (PreH20 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH21 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH22 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH23 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix))))) ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) )
  **  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (store_sm3_ti )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> 0)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> (unsigned_last_nbits ((((Zlength (Prefix)) ÷ 64 ) + 1 )) (64)))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))))
  **  ((( &( "data_len" ) )) # UInt64  |-> (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ))
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition sm3_update_safety_wit_13 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH2 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH3 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH4 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH5 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH6 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH7 : (u8_list_bounded Prefix )) (PreH8 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH9 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH10 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH11 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH12 : ((Zlength ((sm3_tail (Prefix)))) = 0)) ,
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> 0)
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (64 <> 0) ”
.

Definition sm3_update_safety_wit_14 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH2 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH3 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH4 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH5 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH6 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH7 : (u8_list_bounded Prefix )) (PreH8 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH9 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH10 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH11 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH12 : ((Zlength ((sm3_tail (Prefix)))) = 0)) ,
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> 0)
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition sm3_update_safety_wit_15 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH2 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH3 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH4 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH5 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH6 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH9 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH10 : (u8_list_bounded Chunk )) (PreH11 : ((Zlength (Chunk)) = data_len_pre)) (PreH12 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH13 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH15 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH16 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH19 : (u8_list_bounded Prefix )) (PreH20 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH21 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH22 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH23 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix))))) ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) )
  **  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (store_sm3_ti )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> 0)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> (unsigned_last_nbits ((((Zlength (Prefix)) ÷ 64 ) + 1 )) (64)))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ))
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))))
  **  ((( &( "data_len" ) )) # UInt64  |-> (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ))
|--
  “ (64 <> 0) ”
.

Definition sm3_update_safety_wit_16 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH2 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH3 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH4 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH5 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH6 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH9 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH10 : (u8_list_bounded Chunk )) (PreH11 : ((Zlength (Chunk)) = data_len_pre)) (PreH12 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH13 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH15 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH16 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH19 : (u8_list_bounded Prefix )) (PreH20 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH21 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH22 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH23 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix))))) ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) )
  **  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (store_sm3_ti )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> 0)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> (unsigned_last_nbits ((((Zlength (Prefix)) ÷ 64 ) + 1 )) (64)))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ))
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))))
  **  ((( &( "data_len" ) )) # UInt64  |-> (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ))
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition sm3_update_safety_wit_17 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH2 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH3 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH4 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH5 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH6 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH7 : (u8_list_bounded Prefix )) (PreH8 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH9 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH10 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH11 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH12 : ((Zlength ((sm3_tail (Prefix)))) = 0)) ,
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> 0)
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> (data_len_pre ÷ 64 ))
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (64 <> 0) ”
.

Definition sm3_update_safety_wit_18 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH2 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH3 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH4 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH5 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH6 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH7 : (u8_list_bounded Prefix )) (PreH8 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH9 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH10 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH11 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH12 : ((Zlength ((sm3_tail (Prefix)))) = 0)) ,
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> 0)
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> (data_len_pre ÷ 64 ))
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition sm3_update_safety_wit_19 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (offset = (64 * nblock ))) (PreH2 : (data_len = ((64 * nblock ) + left ))) (PreH3 : (0 <= left)) (PreH4 : (left < 64)) (PreH5 : (0 <= offset)) (PreH6 : (offset <= data_len)) (PreH7 : (0 <= (data_len_pre - data_len ))) (PreH8 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH9 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH10 : (u8_list_bounded Prefix )) (PreH11 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH12 : (sm3_compress_input_aligned data nblock )) (PreH13 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH14 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH15 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH16 : ((Zlength (TailBytes)) = left)) (PreH17 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH18 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes)))))))) (PreH19 : (NBlocks = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 ))) (PreH20 : ((sm3_tail ((app (Prefix) (ConsumedBytes)))) = (@nil Z))) ,
  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_update_safety_wit_20 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (nblock > 0)) (PreH4 : (offset = (64 * nblock ))) (PreH5 : (data_len = ((64 * nblock ) + left ))) (PreH6 : (0 <= left)) (PreH7 : (left < 64)) (PreH8 : (0 <= offset)) (PreH9 : (offset <= data_len)) (PreH10 : (0 <= (data_len_pre - data_len ))) (PreH11 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : (sm3_compress_input_aligned data nblock )) (PreH16 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH17 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH18 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH19 : ((Zlength (TailBytes)) = left)) (PreH20 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH21 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes)))))))) (PreH22 : (NBlocks = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 ))) (PreH23 : ((sm3_tail ((app (Prefix) (ConsumedBytes)))) = (@nil Z))) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_update_safety_wit_21 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (offset = (64 * nblock ))) (PreH2 : (data_len = ((64 * nblock ) + left ))) (PreH3 : (0 <= left)) (PreH4 : (left < 64)) (PreH5 : ((left - left ) = 0)) (PreH6 : (0 <= (data_len_pre - data_len ))) (PreH7 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded Prefix )) (PreH9 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH10 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH11 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH12 : ((Zlength (TailBytes)) = left)) (PreH13 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH14 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH15 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH16 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((left - left ) * sizeof(UCHAR))) left )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_update_entail_wit_1 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH2 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) ,
  ((( &( "left" ) )) # UInt64  |-> 0)
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ctx ctx_pre Prefix )
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) ) ”
  &&  ((( &( "left" ) )) # UInt64  |-> 0)
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ctx ctx_pre Prefix )
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
.

Definition sm3_update_entail_wit_2 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH2 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH3 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH4 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) ,
  ((( &( "left" ) )) # UInt64  |-> 0)
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ctx ctx_pre Prefix )
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ ((Zlength (Prefix)) < SM3_MAX_BYTES) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) ) ”
  &&  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> 0)
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
.

Definition sm3_update_entail_wit_3 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH2 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH3 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH4 : (u8_list_bounded Prefix )) (PreH5 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH6 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH7 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH8 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) ,
  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> 0)
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (sm3_tail (Prefix)) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <= 64) ” 
  &&  “ (0 <= (Zlength ((sm3_tail (Prefix))))) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ ((Zlength (Prefix)) < SM3_MAX_BYTES) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) ) ”
  &&  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> 0)
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
.

Definition sm3_update_entail_wit_4 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH2 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH3 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH4 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH5 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH6 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH7 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH8 : (u8_list_bounded Prefix )) (PreH9 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH11 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH12 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH13 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sm3_tail (Prefix)) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <= 64) ” 
  &&  “ (0 <= (Zlength ((sm3_tail (Prefix))))) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ ((Zlength (Prefix)) < SM3_MAX_BYTES) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <> 0) ”
  &&  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) data_len_pre )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
.

Definition sm3_update_entail_wit_5 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH2 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH3 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH4 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH5 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH6 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH7 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH8 : (u8_list_bounded Prefix )) (PreH9 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH11 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH12 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH13 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded Chunk ) ” 
  &&  “ ((Zlength (Chunk)) = data_len_pre) ” 
  &&  “ (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sm3_tail (Prefix)) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <= 64) ” 
  &&  “ (0 <= (Zlength ((sm3_tail (Prefix))))) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ ((Zlength (Prefix)) < SM3_MAX_BYTES) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <> 0) ”
  &&  (UCharArray.full (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))) (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) (sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)) )
  **  (UCharArray.full data_pre (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
.

Definition sm3_update_entail_wit_6 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH2 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH3 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH4 : (u8_list_bounded Chunk )) (PreH5 : ((Zlength (Chunk)) = data_len_pre)) (PreH6 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH8 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH9 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH10 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH12 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH15 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH16 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH17 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH18 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (store_bytes data_pre (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (UCharArray.full (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))) (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) (sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded Chunk ) ” 
  &&  “ ((Zlength (Chunk)) = data_len_pre) ” 
  &&  “ (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sm3_tail (Prefix)) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <= 64) ” 
  &&  “ (0 <= (Zlength ((sm3_tail (Prefix))))) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ ((Zlength (Prefix)) < SM3_MAX_BYTES) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <> 0) ”
  &&  (UCharArray.full data_pre (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (UCharArray.full (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))) (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) (sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
.

Definition sm3_update_entail_wit_7 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH2 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH4 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH6 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH7 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH8 : (u8_list_bounded Chunk )) (PreH9 : ((Zlength (Chunk)) = data_len_pre)) (PreH10 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH11 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH12 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH13 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH14 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH15 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH16 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH17 : (u8_list_bounded Prefix )) (PreH18 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH19 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH20 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH21 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH22 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full data_pre (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (UCharArray.full (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))) (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) (sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
|--
  “ (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) ) ” 
  &&  “ ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded Chunk ) ” 
  &&  “ ((Zlength (Chunk)) = data_len_pre) ” 
  &&  “ (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sm3_tail (Prefix)) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <= 64) ” 
  &&  “ (0 <= (Zlength ((sm3_tail (Prefix))))) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ ((Zlength (Prefix)) < SM3_MAX_BYTES) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <> 0) ”
  &&  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  (UCharArray.full data_pre (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (UCharArray.full (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))) (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) (sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
.

Definition sm3_update_entail_wit_8 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH2 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH3 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH4 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH5 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH6 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH9 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH10 : (u8_list_bounded Chunk )) (PreH11 : ((Zlength (Chunk)) = data_len_pre)) (PreH12 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH13 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH15 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH16 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH19 : (u8_list_bounded Prefix )) (PreH20 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH21 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH22 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH23 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  (UCharArray.full data_pre (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (UCharArray.full (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))) (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) (sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
|--
  “ (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) ) ” 
  &&  “ ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded Chunk ) ” 
  &&  “ ((Zlength (Chunk)) = data_len_pre) ” 
  &&  “ (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sm3_tail (Prefix)) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <= 64) ” 
  &&  “ (0 <= (Zlength ((sm3_tail (Prefix))))) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ ((Zlength (Prefix)) < SM3_MAX_BYTES) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <> 0) ”
  &&  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
.

Definition sm3_update_entail_wit_9_1 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH2 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH3 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH4 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH5 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH6 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH9 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH10 : (u8_list_bounded Chunk )) (PreH11 : ((Zlength (Chunk)) = data_len_pre)) (PreH12 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH13 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH15 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH16 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH19 : (u8_list_bounded Prefix )) (PreH20 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH21 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH22 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH23 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix))))) ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) )
  **  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (store_sm3_ti )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> (unsigned_last_nbits ((((Zlength (Prefix)) ÷ 64 ) + 1 )) (64)))
  **  ((( &( "left" ) )) # UInt64  |-> ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ))
  **  ((( &( "offset" ) )) # UInt64  |-> (unsigned_last_nbits (((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) - ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ) )) (64)))
  **  ((( &( "nblock" ) )) # UInt64  |-> ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ))
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))))
  **  ((( &( "data_len" ) )) # UInt64  |-> (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ))
|--
  “ (u8_list_bounded (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) ) ” 
  &&  “ ((Zlength ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) = (64 * 1 )) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) ) ” 
  &&  “ ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded Chunk ) ” 
  &&  “ ((Zlength (Chunk)) = data_len_pre) ” 
  &&  “ (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sm3_tail (Prefix)) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <= 64) ” 
  &&  “ (0 <= (Zlength ((sm3_tail (Prefix))))) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ ((Zlength (Prefix)) < SM3_MAX_BYTES) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <> 0) ”
  &&  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix))))) ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) )
  **  (store_sm3_ti )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> (unsigned_last_nbits ((((Zlength (Prefix)) ÷ 64 ) + 1 )) (64)))
  **  ((( &( "left" ) )) # UInt64  |-> ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ))
  **  ((( &( "offset" ) )) # UInt64  |-> (unsigned_last_nbits (((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) - ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ) )) (64)))
  **  ((( &( "nblock" ) )) # UInt64  |-> ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ))
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))))
  **  ((( &( "data_len" ) )) # UInt64  |-> (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ))
.

Definition sm3_update_entail_wit_9_2 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH2 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH3 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH4 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH5 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH6 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH7 : (u8_list_bounded Prefix )) (PreH8 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH9 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH10 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH11 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH12 : ((Zlength ((sm3_tail (Prefix)))) = 0)) ,
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (data_len_pre % ( 64 ) ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> (data_len_pre % ( 64 ) ))
  **  ((( &( "offset" ) )) # UInt64  |-> (unsigned_last_nbits ((data_len_pre - (data_len_pre % ( 64 ) ) )) (64)))
  **  ((( &( "nblock" ) )) # UInt64  |-> (data_len_pre ÷ 64 ))
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded Chunk ) ” 
  &&  “ ((Zlength (Chunk)) = data_len_pre) ” 
  &&  “ (u8_list_bounded (sm3_tail (Prefix)) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <= 64) ” 
  &&  “ (0 <= (Zlength ((sm3_tail (Prefix))))) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ ((Zlength (Prefix)) < SM3_MAX_BYTES) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) = 0) ”
  &&  (UCharArray.full data_pre data_len_pre Chunk )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (data_len_pre % ( 64 ) ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> (data_len_pre % ( 64 ) ))
  **  ((( &( "offset" ) )) # UInt64  |-> (unsigned_last_nbits ((data_len_pre - (data_len_pre % ( 64 ) ) )) (64)))
  **  ((( &( "nblock" ) )) # UInt64  |-> (data_len_pre ÷ 64 ))
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
.

Definition sm3_update_entail_wit_10_1 := 
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (u8_list_bounded (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )) (PreH2 : ((Zlength ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) = (64 * 1 ))) (PreH3 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH4 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH5 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH6 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH8 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH9 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH10 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH11 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH12 : (u8_list_bounded Chunk )) (PreH13 : ((Zlength (Chunk)) = data_len_pre)) (PreH14 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH15 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH16 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH17 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH18 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH19 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH20 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH21 : (u8_list_bounded Prefix )) (PreH22 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH23 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH24 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH25 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH26 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix))))) ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) )
  **  (store_sm3_ti )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> (unsigned_last_nbits ((((Zlength (Prefix)) ÷ 64 ) + 1 )) (64)))
|--
  EX (BlockBytes: (@list Z))  (NBlocks: Z)  (State: (@list Z))  (TailBytes: (@list Z))  (BulkBytes: (@list Z))  (ConsumedBytes: (@list Z)) ,
  “ ((unsigned_last_nbits (((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) - ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ) )) (64)) = (64 * ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) )) ” 
  &&  “ ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) = ((64 * ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) ) + ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ) )) ” 
  &&  “ (0 <= ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) )) ” 
  &&  “ (((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ) < 64) ” 
  &&  “ (0 <= (unsigned_last_nbits (((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) - ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ) )) (64))) ” 
  &&  “ ((unsigned_last_nbits (((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) - ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ) )) (64)) <= (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) )) ” 
  &&  “ (0 <= (data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) )) ” 
  &&  “ (((data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ) + (64 * ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) ) ) <= data_len_pre) ” 
  &&  “ ((data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))) = (data_pre + ((data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_compress_input_aligned (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))) ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) ) ” 
  &&  “ (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) ) + ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ) ) ) * sizeof(UCHAR))) ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) ) ” 
  &&  “ ((Zlength (ConsumedBytes)) = (data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) )) ” 
  &&  “ ((Zlength (BulkBytes)) = (64 * ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) )) ” 
  &&  “ ((Zlength (TailBytes)) = ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) )) ” 
  &&  “ (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes))))))) ” 
  &&  “ (NBlocks = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 )) ” 
  &&  “ ((sm3_tail ((app (Prefix) (ConsumedBytes)))) = (@nil Z)) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (UCharArray.seg data_pre 0 (data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ) ((data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ) + (64 * ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ) + (64 * ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
) \/
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (u8_list_bounded (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )) (PreH2 : ((Zlength ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) = (64 * 1 ))) (PreH3 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH4 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH5 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH6 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH8 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH9 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH10 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH11 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH12 : (u8_list_bounded Chunk )) (PreH13 : ((Zlength (Chunk)) = data_len_pre)) (PreH14 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH15 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH16 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH17 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH18 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH19 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH20 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH21 : (u8_list_bounded Prefix )) (PreH22 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH23 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH24 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH25 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH26 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix))))) ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) )
  **  (store_sm3_ti )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
|--
  EX (BlockBytes: (@list Z))  (TailBytes: (@list Z))  (BulkBytes: (@list Z))  (ConsumedBytes: (@list Z)) ,
  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ ((Zlength (BlockBytes)) <= 64) ” 
  &&  “ (0 <= (Zlength (BlockBytes))) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes)))))) ) ” 
  &&  “ ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes)))))))) = 8) ” 
  &&  “ ((unsigned_last_nbits ((((Zlength (Prefix)) ÷ 64 ) + 1 )) (64)) = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 )) ” 
  &&  “ ((unsigned_last_nbits ((((Zlength (Prefix)) ÷ 64 ) + 1 )) (64)) = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 )) ” 
  &&  “ ((unsigned_last_nbits (((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) - ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ) )) (64)) = (64 * ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) )) ” 
  &&  “ ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) = ((64 * ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) ) + ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ) )) ” 
  &&  “ (0 <= ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) )) ” 
  &&  “ (((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ) < 64) ” 
  &&  “ (0 <= (unsigned_last_nbits (((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) - ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ) )) (64))) ” 
  &&  “ ((unsigned_last_nbits (((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) - ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ) )) (64)) <= (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) )) ” 
  &&  “ (0 <= (data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) )) ” 
  &&  “ (((data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ) + (64 * ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) ) ) <= data_len_pre) ” 
  &&  “ ((data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))) = (data_pre + ((data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_compress_input_aligned (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))) ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) ) ” 
  &&  “ (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) ) + ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) ) ) ) * sizeof(UCHAR))) ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) ) ” 
  &&  “ ((Zlength (ConsumedBytes)) = (data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) )) ” 
  &&  “ ((Zlength (BulkBytes)) = (64 * ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) )) ” 
  &&  “ ((Zlength (TailBytes)) = ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) % ( 64 ) )) ” 
  &&  “ (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes))))) ” 
  &&  “ ((sm3_tail ((app (Prefix) (ConsumedBytes)))) = (@nil Z)) ”
  &&  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength (BlockBytes)) ) (64 - (Zlength (BlockBytes)) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength (BlockBytes)) BlockBytes )
  **  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes)))))) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ) ((data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ) + (64 * ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ) + (64 * ((data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) ÷ 64 ) ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
).

Definition sm3_update_entail_wit_10_2 := 
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (u8_list_bounded Chunk )) (PreH2 : ((Zlength (Chunk)) = data_len_pre)) (PreH3 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH4 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH5 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH6 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH7 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH8 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH9 : (u8_list_bounded Prefix )) (PreH10 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH12 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH13 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) = 0)) ,
  (UCharArray.full data_pre data_len_pre Chunk )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (data_len_pre % ( 64 ) ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  (store_sm3_ti )
|--
  EX (BlockBytes: (@list Z))  (NBlocks: Z)  (State: (@list Z))  (TailBytes: (@list Z))  (BulkBytes: (@list Z))  (ConsumedBytes: (@list Z)) ,
  “ ((unsigned_last_nbits ((data_len_pre - (data_len_pre % ( 64 ) ) )) (64)) = (64 * (data_len_pre ÷ 64 ) )) ” 
  &&  “ (data_len_pre = ((64 * (data_len_pre ÷ 64 ) ) + (data_len_pre % ( 64 ) ) )) ” 
  &&  “ (0 <= (data_len_pre % ( 64 ) )) ” 
  &&  “ ((data_len_pre % ( 64 ) ) < 64) ” 
  &&  “ (0 <= (unsigned_last_nbits ((data_len_pre - (data_len_pre % ( 64 ) ) )) (64))) ” 
  &&  “ ((unsigned_last_nbits ((data_len_pre - (data_len_pre % ( 64 ) ) )) (64)) <= data_len_pre) ” 
  &&  “ (0 <= (data_len_pre - data_len_pre )) ” 
  &&  “ (((data_len_pre - data_len_pre ) + (64 * (data_len_pre ÷ 64 ) ) ) <= data_len_pre) ” 
  &&  “ (data_pre = (data_pre + ((data_len_pre - data_len_pre ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_compress_input_aligned data_pre (data_len_pre ÷ 64 ) ) ” 
  &&  “ (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * (data_len_pre ÷ 64 ) ) + (data_len_pre % ( 64 ) ) ) ) * sizeof(UCHAR))) (data_len_pre ÷ 64 ) ) ” 
  &&  “ ((Zlength (ConsumedBytes)) = (data_len_pre - data_len_pre )) ” 
  &&  “ ((Zlength (BulkBytes)) = (64 * (data_len_pre ÷ 64 ) )) ” 
  &&  “ ((Zlength (TailBytes)) = (data_len_pre % ( 64 ) )) ” 
  &&  “ (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes))))))) ” 
  &&  “ (NBlocks = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 )) ” 
  &&  “ ((sm3_tail ((app (Prefix) (ConsumedBytes)))) = (@nil Z)) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (data_len_pre % ( 64 ) ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len_pre ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len_pre ) ((data_len_pre - data_len_pre ) + (64 * (data_len_pre ÷ 64 ) ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len_pre ) + (64 * (data_len_pre ÷ 64 ) ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
) \/
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (u8_list_bounded Chunk )) (PreH2 : ((Zlength (Chunk)) = data_len_pre)) (PreH3 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH4 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH5 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH6 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH7 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH8 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH9 : (u8_list_bounded Prefix )) (PreH10 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH12 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH13 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) = 0)) ,
  (UCharArray.full data_pre data_len_pre Chunk )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  (store_sm3_ti )
|--
  EX (BlockBytes: (@list Z))  (TailBytes: (@list Z))  (BulkBytes: (@list Z))  (ConsumedBytes: (@list Z)) ,
  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ ((Zlength (BlockBytes)) <= 64) ” 
  &&  “ (0 <= (Zlength (BlockBytes))) ” 
  &&  “ (((Zlength (Prefix)) ÷ 64 ) = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 )) ” 
  &&  “ (((Zlength (Prefix)) ÷ 64 ) = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 )) ” 
  &&  “ ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes))))))) ” 
  &&  “ ((unsigned_last_nbits ((data_len_pre - (data_len_pre % ( 64 ) ) )) (64)) = (64 * (data_len_pre ÷ 64 ) )) ” 
  &&  “ (data_len_pre = ((64 * (data_len_pre ÷ 64 ) ) + (data_len_pre % ( 64 ) ) )) ” 
  &&  “ (0 <= (data_len_pre % ( 64 ) )) ” 
  &&  “ ((data_len_pre % ( 64 ) ) < 64) ” 
  &&  “ (0 <= (unsigned_last_nbits ((data_len_pre - (data_len_pre % ( 64 ) ) )) (64))) ” 
  &&  “ ((unsigned_last_nbits ((data_len_pre - (data_len_pre % ( 64 ) ) )) (64)) <= data_len_pre) ” 
  &&  “ (0 <= (data_len_pre - data_len_pre )) ” 
  &&  “ (((data_len_pre - data_len_pre ) + (64 * (data_len_pre ÷ 64 ) ) ) <= data_len_pre) ” 
  &&  “ (data_pre = (data_pre + ((data_len_pre - data_len_pre ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_compress_input_aligned data_pre (data_len_pre ÷ 64 ) ) ” 
  &&  “ (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * (data_len_pre ÷ 64 ) ) + (data_len_pre % ( 64 ) ) ) ) * sizeof(UCHAR))) (data_len_pre ÷ 64 ) ) ” 
  &&  “ ((Zlength (ConsumedBytes)) = (data_len_pre - data_len_pre )) ” 
  &&  “ ((Zlength (BulkBytes)) = (64 * (data_len_pre ÷ 64 ) )) ” 
  &&  “ ((Zlength (TailBytes)) = (data_len_pre % ( 64 ) )) ” 
  &&  “ (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes))))) ” 
  &&  “ ((sm3_tail ((app (Prefix) (ConsumedBytes)))) = (@nil Z)) ”
  &&  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength (BlockBytes)) ) (64 - (Zlength (BlockBytes)) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength (BlockBytes)) BlockBytes )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len_pre ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len_pre ) ((data_len_pre - data_len_pre ) + (64 * (data_len_pre ÷ 64 ) ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len_pre ) + (64 * (data_len_pre ÷ 64 ) ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
).

Definition sm3_update_entail_wit_11 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (nblock > 0)) (PreH2 : (offset = (64 * nblock ))) (PreH3 : (data_len = ((64 * nblock ) + left ))) (PreH4 : (0 <= left)) (PreH5 : (left < 64)) (PreH6 : (0 <= offset)) (PreH7 : (offset <= data_len)) (PreH8 : (0 <= (data_len_pre - data_len ))) (PreH9 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH10 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH11 : (u8_list_bounded Prefix )) (PreH12 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH13 : (sm3_compress_input_aligned data nblock )) (PreH14 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 ))) (PreH21 : ((sm3_tail ((app (Prefix) (ConsumedBytes)))) = (@nil Z))) ,
  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
|--
  “ (limb_list_bounded SM3_WORD_MODULUS State ) ” 
  &&  “ ((Zlength (State)) = 8) ” 
  &&  “ (nblock > 0) ” 
  &&  “ (offset = (64 * nblock )) ” 
  &&  “ (data_len = ((64 * nblock ) + left )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < 64) ” 
  &&  “ (0 <= offset) ” 
  &&  “ (offset <= data_len) ” 
  &&  “ (0 <= (data_len_pre - data_len )) ” 
  &&  “ (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre) ” 
  &&  “ (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_compress_input_aligned data nblock ) ” 
  &&  “ (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock ) ” 
  &&  “ ((Zlength (ConsumedBytes)) = (data_len_pre - data_len )) ” 
  &&  “ ((Zlength (BulkBytes)) = (64 * nblock )) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes))))))) ” 
  &&  “ (NBlocks = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 )) ” 
  &&  “ ((sm3_tail ((app (Prefix) (ConsumedBytes)))) = (@nil Z)) ”
  &&  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
.

Definition sm3_update_entail_wit_12_1 := 
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (NBlocks_2: Z) (ConsumedBytes_2: (@list Z)) (BulkBytes_2: (@list Z)) (TailBytes_2: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State_2 )) (PreH2 : ((Zlength (State_2)) = 8)) (PreH3 : (nblock > 0)) (PreH4 : (offset = (64 * nblock ))) (PreH5 : (data_len = ((64 * nblock ) + left ))) (PreH6 : (0 <= left)) (PreH7 : (left < 64)) (PreH8 : (0 <= offset)) (PreH9 : (offset <= data_len)) (PreH10 : (0 <= (data_len_pre - data_len ))) (PreH11 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : (sm3_compress_input_aligned data nblock )) (PreH16 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH17 : ((Zlength (ConsumedBytes_2)) = (data_len_pre - data_len ))) (PreH18 : ((Zlength (BulkBytes_2)) = (64 * nblock ))) (PreH19 : ((Zlength (TailBytes_2)) = left)) (PreH20 : (Chunk = (app (ConsumedBytes_2) ((app (BulkBytes_2) (TailBytes_2)))))) (PreH21 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes_2)))))))) (PreH22 : (NBlocks_2 = ((Zlength ((app (Prefix) (ConsumedBytes_2)))) ÷ 64 ))) (PreH23 : ((sm3_tail ((app (Prefix) (ConsumedBytes_2)))) = (@nil Z))) ,
  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State_2) (BulkBytes_2)) )
  **  (store_bytes data (64 * nblock ) BulkBytes_2 )
  **  (store_sm3_ti )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> (unsigned_last_nbits ((NBlocks_2 + nblock )) (64)))
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes_2 )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes_2 )
|--
  EX (NBlocks: Z)  (State: (@list Z))  (TailBytes: (@list Z))  (BulkBytes: (@list Z))  (ConsumedBytes: (@list Z)) ,
  “ (offset = (64 * nblock )) ” 
  &&  “ (data_len = ((64 * nblock ) + left )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < 64) ” 
  &&  “ ((left - left ) = 0) ” 
  &&  “ (0 <= (data_len_pre - data_len )) ” 
  &&  “ (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ ((Zlength (ConsumedBytes)) = (data_len_pre - data_len )) ” 
  &&  “ ((Zlength (BulkBytes)) = (64 * nblock )) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk))))))) ” 
  &&  “ (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ” 
  &&  “ (TailBytes = (sm3_tail ((app (Prefix) (Chunk))))) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((left - left ) * sizeof(UCHAR))) left )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
) \/
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (NBlocks_2: Z) (ConsumedBytes_2: (@list Z)) (BulkBytes_2: (@list Z)) (TailBytes_2: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State_2 )) (PreH2 : ((Zlength (State_2)) = 8)) (PreH3 : (nblock > 0)) (PreH4 : (offset = (64 * nblock ))) (PreH5 : (data_len = ((64 * nblock ) + left ))) (PreH6 : (0 <= left)) (PreH7 : (left < 64)) (PreH8 : (0 <= offset)) (PreH9 : (offset <= data_len)) (PreH10 : (0 <= (data_len_pre - data_len ))) (PreH11 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : (sm3_compress_input_aligned data nblock )) (PreH16 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH17 : ((Zlength (ConsumedBytes_2)) = (data_len_pre - data_len ))) (PreH18 : ((Zlength (BulkBytes_2)) = (64 * nblock ))) (PreH19 : ((Zlength (TailBytes_2)) = left)) (PreH20 : (Chunk = (app (ConsumedBytes_2) ((app (BulkBytes_2) (TailBytes_2)))))) (PreH21 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes_2)))))))) (PreH22 : (NBlocks_2 = ((Zlength ((app (Prefix) (ConsumedBytes_2)))) ÷ 64 ))) (PreH23 : ((sm3_tail ((app (Prefix) (ConsumedBytes_2)))) = (@nil Z))) ,
  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State_2) (BulkBytes_2)) )
  **  (store_bytes data (64 * nblock ) BulkBytes_2 )
  **  (store_sm3_ti )
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
|--
  EX (BulkBytes: (@list Z)) ,
  “ (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))) ) ” 
  &&  “ ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) = 8) ” 
  &&  “ (TailBytes_2 = (sm3_tail ((app (Prefix) (Chunk))))) ” 
  &&  “ ((unsigned_last_nbits ((NBlocks_2 + nblock )) (64)) = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ” 
  &&  “ ((unsigned_last_nbits ((NBlocks_2 + nblock )) (64)) = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ” 
  &&  “ (offset = (64 * nblock )) ” 
  &&  “ (data_len = ((64 * nblock ) + left )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < 64) ” 
  &&  “ ((left - left ) = 0) ” 
  &&  “ (0 <= (data_len_pre - data_len )) ” 
  &&  “ (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ ((Zlength (ConsumedBytes_2)) = (data_len_pre - data_len )) ” 
  &&  “ ((Zlength (BulkBytes)) = (64 * nblock )) ” 
  &&  “ ((Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) = left) ” 
  &&  “ (Chunk = (app (ConsumedBytes_2) ((app (BulkBytes) ((sm3_tail ((app (Prefix) (Chunk))))))))) ”
  &&  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((left - left ) * sizeof(UCHAR))) left )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
).

Definition sm3_update_entail_wit_12_2 := 
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (NBlocks_2: Z) (ConsumedBytes_2: (@list Z)) (BulkBytes_2: (@list Z)) (TailBytes_2: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (nblock <= 0)) (PreH2 : (offset = (64 * nblock ))) (PreH3 : (data_len = ((64 * nblock ) + left ))) (PreH4 : (0 <= left)) (PreH5 : (left < 64)) (PreH6 : (0 <= offset)) (PreH7 : (offset <= data_len)) (PreH8 : (0 <= (data_len_pre - data_len ))) (PreH9 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH10 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH11 : (u8_list_bounded Prefix )) (PreH12 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH13 : (sm3_compress_input_aligned data nblock )) (PreH14 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH15 : ((Zlength (ConsumedBytes_2)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes_2)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes_2)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes_2) ((app (BulkBytes_2) (TailBytes_2)))))) (PreH19 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes_2)))))))) (PreH20 : (NBlocks_2 = ((Zlength ((app (Prefix) (ConsumedBytes_2)))) ÷ 64 ))) (PreH21 : ((sm3_tail ((app (Prefix) (ConsumedBytes_2)))) = (@nil Z))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State_2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks_2)
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes_2 )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes_2 )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes_2 )
  **  (store_sm3_ti )
|--
  EX (NBlocks: Z)  (State: (@list Z))  (TailBytes: (@list Z))  (BulkBytes: (@list Z))  (ConsumedBytes: (@list Z)) ,
  “ (offset = (64 * nblock )) ” 
  &&  “ (data_len = ((64 * nblock ) + left )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < 64) ” 
  &&  “ ((left - left ) = 0) ” 
  &&  “ (0 <= (data_len_pre - data_len )) ” 
  &&  “ (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ ((Zlength (ConsumedBytes)) = (data_len_pre - data_len )) ” 
  &&  “ ((Zlength (BulkBytes)) = (64 * nblock )) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk))))))) ” 
  &&  “ (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ” 
  &&  “ (TailBytes = (sm3_tail ((app (Prefix) (Chunk))))) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((left - left ) * sizeof(UCHAR))) left )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
) \/
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (NBlocks_2: Z) (ConsumedBytes_2: (@list Z)) (BulkBytes_2: (@list Z)) (TailBytes_2: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (nblock <= 0)) (PreH2 : (offset = (64 * nblock ))) (PreH3 : (data_len = ((64 * nblock ) + left ))) (PreH4 : (0 <= left)) (PreH5 : (left < 64)) (PreH6 : (0 <= offset)) (PreH7 : (offset <= data_len)) (PreH8 : (0 <= (data_len_pre - data_len ))) (PreH9 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH10 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH11 : (u8_list_bounded Prefix )) (PreH12 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH13 : (sm3_compress_input_aligned data nblock )) (PreH14 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH15 : ((Zlength (ConsumedBytes_2)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes_2)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes_2)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes_2) ((app (BulkBytes_2) (TailBytes_2)))))) (PreH19 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes_2)))))))) (PreH20 : (NBlocks_2 = ((Zlength ((app (Prefix) (ConsumedBytes_2)))) ÷ 64 ))) (PreH21 : ((sm3_tail ((app (Prefix) (ConsumedBytes_2)))) = (@nil Z))) ,
  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (store_sm3_ti )
|--
  “ (Chunk = (app (ConsumedBytes_2) ((app (BulkBytes_2) ((sm3_tail ((app (Prefix) (Chunk))))))))) ” 
  &&  “ ((Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) = left) ” 
  &&  “ (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk))))))) ” 
  &&  “ (NBlocks_2 = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ” 
  &&  “ (NBlocks_2 = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ” 
  &&  “ (TailBytes_2 = (sm3_tail ((app (Prefix) (Chunk))))) ”
  &&  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((left - left ) * sizeof(UCHAR))) left )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (store_sm3_ti )
).

Definition sm3_update_entail_wit_12_2_split_goal_1 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (NBlocks_2: Z) (ConsumedBytes_2: (@list Z)) (BulkBytes_2: (@list Z)) (TailBytes_2: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (nblock <= 0)) (PreH2 : (offset = (64 * nblock ))) (PreH3 : (data_len = ((64 * nblock ) + left ))) (PreH4 : (0 <= left)) (PreH5 : (left < 64)) (PreH6 : (0 <= offset)) (PreH7 : (offset <= data_len)) (PreH8 : (0 <= (data_len_pre - data_len ))) (PreH9 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH10 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH11 : (u8_list_bounded Prefix )) (PreH12 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH13 : (sm3_compress_input_aligned data nblock )) (PreH14 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH15 : ((Zlength (ConsumedBytes_2)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes_2)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes_2)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes_2) ((app (BulkBytes_2) (TailBytes_2)))))) (PreH19 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes_2)))))))) (PreH20 : (NBlocks_2 = ((Zlength ((app (Prefix) (ConsumedBytes_2)))) ÷ 64 ))) (PreH21 : ((sm3_tail ((app (Prefix) (ConsumedBytes_2)))) = (@nil Z))) ,
  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (store_sm3_ti )
|--
  “ (Chunk = (app (ConsumedBytes_2) ((app (BulkBytes_2) ((sm3_tail ((app (Prefix) (Chunk))))))))) ”
.

Definition sm3_update_entail_wit_12_2_split_goal_2 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (NBlocks_2: Z) (ConsumedBytes_2: (@list Z)) (BulkBytes_2: (@list Z)) (TailBytes_2: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (nblock <= 0)) (PreH2 : (offset = (64 * nblock ))) (PreH3 : (data_len = ((64 * nblock ) + left ))) (PreH4 : (0 <= left)) (PreH5 : (left < 64)) (PreH6 : (0 <= offset)) (PreH7 : (offset <= data_len)) (PreH8 : (0 <= (data_len_pre - data_len ))) (PreH9 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH10 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH11 : (u8_list_bounded Prefix )) (PreH12 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH13 : (sm3_compress_input_aligned data nblock )) (PreH14 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH15 : ((Zlength (ConsumedBytes_2)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes_2)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes_2)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes_2) ((app (BulkBytes_2) (TailBytes_2)))))) (PreH19 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes_2)))))))) (PreH20 : (NBlocks_2 = ((Zlength ((app (Prefix) (ConsumedBytes_2)))) ÷ 64 ))) (PreH21 : ((sm3_tail ((app (Prefix) (ConsumedBytes_2)))) = (@nil Z))) ,
  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (store_sm3_ti )
|--
  “ ((Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) = left) ”
.

Definition sm3_update_entail_wit_12_2_split_goal_3 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (NBlocks_2: Z) (ConsumedBytes_2: (@list Z)) (BulkBytes_2: (@list Z)) (TailBytes_2: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (nblock <= 0)) (PreH2 : (offset = (64 * nblock ))) (PreH3 : (data_len = ((64 * nblock ) + left ))) (PreH4 : (0 <= left)) (PreH5 : (left < 64)) (PreH6 : (0 <= offset)) (PreH7 : (offset <= data_len)) (PreH8 : (0 <= (data_len_pre - data_len ))) (PreH9 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH10 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH11 : (u8_list_bounded Prefix )) (PreH12 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH13 : (sm3_compress_input_aligned data nblock )) (PreH14 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH15 : ((Zlength (ConsumedBytes_2)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes_2)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes_2)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes_2) ((app (BulkBytes_2) (TailBytes_2)))))) (PreH19 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes_2)))))))) (PreH20 : (NBlocks_2 = ((Zlength ((app (Prefix) (ConsumedBytes_2)))) ÷ 64 ))) (PreH21 : ((sm3_tail ((app (Prefix) (ConsumedBytes_2)))) = (@nil Z))) ,
  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (store_sm3_ti )
|--
  “ (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk))))))) ”
.

Definition sm3_update_entail_wit_12_2_split_goal_4 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (NBlocks_2: Z) (ConsumedBytes_2: (@list Z)) (BulkBytes_2: (@list Z)) (TailBytes_2: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (nblock <= 0)) (PreH2 : (offset = (64 * nblock ))) (PreH3 : (data_len = ((64 * nblock ) + left ))) (PreH4 : (0 <= left)) (PreH5 : (left < 64)) (PreH6 : (0 <= offset)) (PreH7 : (offset <= data_len)) (PreH8 : (0 <= (data_len_pre - data_len ))) (PreH9 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH10 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH11 : (u8_list_bounded Prefix )) (PreH12 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH13 : (sm3_compress_input_aligned data nblock )) (PreH14 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH15 : ((Zlength (ConsumedBytes_2)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes_2)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes_2)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes_2) ((app (BulkBytes_2) (TailBytes_2)))))) (PreH19 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes_2)))))))) (PreH20 : (NBlocks_2 = ((Zlength ((app (Prefix) (ConsumedBytes_2)))) ÷ 64 ))) (PreH21 : ((sm3_tail ((app (Prefix) (ConsumedBytes_2)))) = (@nil Z))) ,
  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (store_sm3_ti )
|--
  “ (NBlocks_2 = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ”
.

Definition sm3_update_entail_wit_12_2_split_goal_5 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (NBlocks_2: Z) (ConsumedBytes_2: (@list Z)) (BulkBytes_2: (@list Z)) (TailBytes_2: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (nblock <= 0)) (PreH2 : (offset = (64 * nblock ))) (PreH3 : (data_len = ((64 * nblock ) + left ))) (PreH4 : (0 <= left)) (PreH5 : (left < 64)) (PreH6 : (0 <= offset)) (PreH7 : (offset <= data_len)) (PreH8 : (0 <= (data_len_pre - data_len ))) (PreH9 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH10 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH11 : (u8_list_bounded Prefix )) (PreH12 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH13 : (sm3_compress_input_aligned data nblock )) (PreH14 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH15 : ((Zlength (ConsumedBytes_2)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes_2)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes_2)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes_2) ((app (BulkBytes_2) (TailBytes_2)))))) (PreH19 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes_2)))))))) (PreH20 : (NBlocks_2 = ((Zlength ((app (Prefix) (ConsumedBytes_2)))) ÷ 64 ))) (PreH21 : ((sm3_tail ((app (Prefix) (ConsumedBytes_2)))) = (@nil Z))) ,
  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (store_sm3_ti )
|--
  “ (NBlocks_2 = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ”
.

Definition sm3_update_entail_wit_12_2_split_goal_6 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (NBlocks_2: Z) (ConsumedBytes_2: (@list Z)) (BulkBytes_2: (@list Z)) (TailBytes_2: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (nblock <= 0)) (PreH2 : (offset = (64 * nblock ))) (PreH3 : (data_len = ((64 * nblock ) + left ))) (PreH4 : (0 <= left)) (PreH5 : (left < 64)) (PreH6 : (0 <= offset)) (PreH7 : (offset <= data_len)) (PreH8 : (0 <= (data_len_pre - data_len ))) (PreH9 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH10 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH11 : (u8_list_bounded Prefix )) (PreH12 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH13 : (sm3_compress_input_aligned data nblock )) (PreH14 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH15 : ((Zlength (ConsumedBytes_2)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes_2)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes_2)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes_2) ((app (BulkBytes_2) (TailBytes_2)))))) (PreH19 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes_2)))))))) (PreH20 : (NBlocks_2 = ((Zlength ((app (Prefix) (ConsumedBytes_2)))) ÷ 64 ))) (PreH21 : ((sm3_tail ((app (Prefix) (ConsumedBytes_2)))) = (@nil Z))) ,
  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (store_sm3_ti )
|--
  “ (TailBytes_2 = (sm3_tail ((app (Prefix) (Chunk))))) ”
.

Definition sm3_update_entail_wit_12_2_split_goal_spatial := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (NBlocks_2: Z) (ConsumedBytes_2: (@list Z)) (BulkBytes_2: (@list Z)) (TailBytes_2: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (nblock <= 0)) (PreH2 : (offset = (64 * nblock ))) (PreH3 : (data_len = ((64 * nblock ) + left ))) (PreH4 : (0 <= left)) (PreH5 : (left < 64)) (PreH6 : (0 <= offset)) (PreH7 : (offset <= data_len)) (PreH8 : (0 <= (data_len_pre - data_len ))) (PreH9 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH10 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH11 : (u8_list_bounded Prefix )) (PreH12 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH13 : (sm3_compress_input_aligned data nblock )) (PreH14 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH15 : ((Zlength (ConsumedBytes_2)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes_2)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes_2)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes_2) ((app (BulkBytes_2) (TailBytes_2)))))) (PreH19 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes_2)))))))) (PreH20 : (NBlocks_2 = ((Zlength ((app (Prefix) (ConsumedBytes_2)))) ÷ 64 ))) (PreH21 : ((sm3_tail ((app (Prefix) (ConsumedBytes_2)))) = (@nil Z))) ,
  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (store_sm3_ti )
|--
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((left - left ) * sizeof(UCHAR))) left )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (store_sm3_ti )
.

Definition sm3_update_entail_wit_13 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH2 : (offset = (64 * nblock ))) (PreH3 : (data_len = ((64 * nblock ) + left ))) (PreH4 : (0 <= left)) (PreH5 : (left < 64)) (PreH6 : ((left - left ) = 0)) (PreH7 : (0 <= (data_len_pre - data_len ))) (PreH8 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH9 : (u8_list_bounded Prefix )) (PreH10 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH11 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH12 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH13 : ((Zlength (TailBytes)) = left)) (PreH14 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH15 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH16 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH17 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) left TailBytes )
  **  (store_bytes (data + (offset * sizeof(UCHAR))) left TailBytes )
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded TailBytes ) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (u8_list_bounded TailBytes ) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR)))) ” 
  &&  “ (offset = (64 * nblock )) ” 
  &&  “ (data_len = ((64 * nblock ) + left )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < 64) ” 
  &&  “ ((left - left ) = 0) ” 
  &&  “ (0 <= (data_len_pre - data_len )) ” 
  &&  “ (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ ((Zlength (ConsumedBytes)) = (data_len_pre - data_len )) ” 
  &&  “ ((Zlength (BulkBytes)) = (64 * nblock )) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk))))))) ” 
  &&  “ (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ” 
  &&  “ (TailBytes = (sm3_tail ((app (Prefix) (Chunk))))) ”
  &&  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (UCharArray.seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 0 (0 + left ) TailBytes )
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
.

Definition sm3_update_entail_wit_14 := 
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (u8_list_bounded TailBytes )) (PreH2 : ((Zlength (TailBytes)) = left)) (PreH3 : (u8_list_bounded TailBytes )) (PreH4 : ((Zlength (TailBytes)) = left)) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH6 : (offset = (64 * nblock ))) (PreH7 : (data_len = ((64 * nblock ) + left ))) (PreH8 : (0 <= left)) (PreH9 : (left < 64)) (PreH10 : ((left - left ) = 0)) (PreH11 : (0 <= (data_len_pre - data_len ))) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH21 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (UCharArray.seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 0 (0 + left ) TailBytes )
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded TailBytes ) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (u8_list_bounded TailBytes ) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR)))) ” 
  &&  “ (offset = (64 * nblock )) ” 
  &&  “ (data_len = ((64 * nblock ) + left )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < 64) ” 
  &&  “ ((left - left ) = 0) ” 
  &&  “ (0 <= (data_len_pre - data_len )) ” 
  &&  “ (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ ((Zlength (ConsumedBytes)) = (data_len_pre - data_len )) ” 
  &&  “ ((Zlength (BulkBytes)) = (64 * nblock )) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk))))))) ” 
  &&  “ (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ” 
  &&  “ (TailBytes = (sm3_tail ((app (Prefix) (Chunk))))) ”
  &&  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (UCharArray.seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 0 (0 + left ) TailBytes )
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
) \/
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (u8_list_bounded TailBytes )) (PreH2 : ((Zlength (TailBytes)) = left)) (PreH3 : (u8_list_bounded TailBytes )) (PreH4 : ((Zlength (TailBytes)) = left)) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH6 : (offset = (64 * nblock ))) (PreH7 : (data_len = ((64 * nblock ) + left ))) (PreH8 : (0 <= left)) (PreH9 : (left < 64)) (PreH10 : ((left - left ) = 0)) (PreH11 : (0 <= (data_len_pre - data_len ))) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH21 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  TT && emp 
|--
  TT && emp 
).

Definition sm3_update_entail_wit_15 := 
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (u8_list_bounded TailBytes )) (PreH2 : ((Zlength (TailBytes)) = left)) (PreH3 : (u8_list_bounded TailBytes )) (PreH4 : ((Zlength (TailBytes)) = left)) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH6 : (offset = (64 * nblock ))) (PreH7 : (data_len = ((64 * nblock ) + left ))) (PreH8 : (0 <= left)) (PreH9 : (left < 64)) (PreH10 : ((left - left ) = 0)) (PreH11 : (0 <= (data_len_pre - data_len ))) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH21 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (UCharArray.seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 0 (0 + left ) TailBytes )
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded TailBytes ) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (u8_list_bounded TailBytes ) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR)))) ” 
  &&  “ (offset = (64 * nblock )) ” 
  &&  “ (data_len = ((64 * nblock ) + left )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < 64) ” 
  &&  “ ((left - left ) = 0) ” 
  &&  “ (0 <= (data_len_pre - data_len )) ” 
  &&  “ (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ ((Zlength (ConsumedBytes)) = (data_len_pre - data_len )) ” 
  &&  “ ((Zlength (BulkBytes)) = (64 * nblock )) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk))))))) ” 
  &&  “ (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ” 
  &&  “ (TailBytes = (sm3_tail ((app (Prefix) (Chunk))))) ”
  &&  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (UCharArray.seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 0 (0 + left ) TailBytes )
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
) \/
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (u8_list_bounded TailBytes )) (PreH2 : ((Zlength (TailBytes)) = left)) (PreH3 : (u8_list_bounded TailBytes )) (PreH4 : ((Zlength (TailBytes)) = left)) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH6 : (offset = (64 * nblock ))) (PreH7 : (data_len = ((64 * nblock ) + left ))) (PreH8 : (0 <= left)) (PreH9 : (left < 64)) (PreH10 : ((left - left ) = 0)) (PreH11 : (0 <= (data_len_pre - data_len ))) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH21 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  TT && emp 
|--
  TT && emp 
).

Definition sm3_update_entail_wit_16 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (u8_list_bounded TailBytes )) (PreH2 : ((Zlength (TailBytes)) = left)) (PreH3 : (u8_list_bounded TailBytes )) (PreH4 : ((Zlength (TailBytes)) = left)) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH6 : (offset = (64 * nblock ))) (PreH7 : (data_len = ((64 * nblock ) + left ))) (PreH8 : (0 <= left)) (PreH9 : (left < 64)) (PreH10 : ((left - left ) = 0)) (PreH11 : (0 <= (data_len_pre - data_len ))) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH21 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (UCharArray.seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 0 (0 + left ) TailBytes )
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded TailBytes ) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (u8_list_bounded TailBytes ) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR)))) ” 
  &&  “ (offset = (64 * nblock )) ” 
  &&  “ (data_len = ((64 * nblock ) + left )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < 64) ” 
  &&  “ ((left - left ) = 0) ” 
  &&  “ (0 <= (data_len_pre - data_len )) ” 
  &&  “ (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ ((Zlength (ConsumedBytes)) = (data_len_pre - data_len )) ” 
  &&  “ ((Zlength (BulkBytes)) = (64 * nblock )) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk))))))) ” 
  &&  “ (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ” 
  &&  “ (TailBytes = (sm3_tail ((app (Prefix) (Chunk))))) ”
  &&  (UCharArray.full data_pre (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (0 + left ) TailBytes )
  **  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
.

Definition sm3_update_return_wit_1 := 
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH2 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH4 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH5 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH6 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH7 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH8 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH9 : (u8_list_bounded Prefix )) (PreH10 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH12 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH13 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) data_len_pre Chunk )
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> ((Zlength ((sm3_tail (Prefix)))) + data_len_pre ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  (store_sm3_ti )
|--
  (store_sm3_ctx ctx_pre (app (Prefix) (Chunk)) )
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
) \/
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH2 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH4 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH5 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH6 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH7 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH8 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH9 : (u8_list_bounded Prefix )) (PreH10 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH12 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH13 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) data_len_pre Chunk )
  **  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (app (Prefix) (Chunk)) ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk))))))) ” 
  &&  “ (((Zlength ((sm3_tail (Prefix)))) + data_len_pre ) = (Zlength ((sm3_tail ((app (Prefix) (Chunk))))))) ” 
  &&  “ (((Zlength (Prefix)) ÷ 64 ) = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ” 
  &&  “ (0 <= (Zlength ((sm3_tail ((app (Prefix) (Chunk))))))) ” 
  &&  “ ((Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) <= 64) ” 
  &&  “ (u8_list_bounded (sm3_tail ((app (Prefix) (Chunk)))) ) ”
  &&  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) ) (64 - (Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) (sm3_tail ((app (Prefix) (Chunk)))) )
  **  (store_sm3_ti )
).

Definition sm3_update_return_wit_1_split_goal_1 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH2 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH4 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH5 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH6 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH7 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH8 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH9 : (u8_list_bounded Prefix )) (PreH10 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH12 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH13 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) data_len_pre Chunk )
  **  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (app (Prefix) (Chunk)) ) ”
.

Definition sm3_update_return_wit_1_split_goal_2 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH2 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH4 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH5 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH6 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH7 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH8 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH9 : (u8_list_bounded Prefix )) (PreH10 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH12 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH13 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) data_len_pre Chunk )
  **  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  (store_sm3_ti )
|--
  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ”
.

Definition sm3_update_return_wit_1_split_goal_3 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH2 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH4 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH5 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH6 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH7 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH8 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH9 : (u8_list_bounded Prefix )) (PreH10 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH12 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH13 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) data_len_pre Chunk )
  **  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  (store_sm3_ti )
|--
  “ ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk))))))) ”
.

Definition sm3_update_return_wit_1_split_goal_4 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH2 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH4 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH5 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH6 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH7 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH8 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH9 : (u8_list_bounded Prefix )) (PreH10 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH12 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH13 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) data_len_pre Chunk )
  **  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  (store_sm3_ti )
|--
  “ (((Zlength ((sm3_tail (Prefix)))) + data_len_pre ) = (Zlength ((sm3_tail ((app (Prefix) (Chunk))))))) ”
.

Definition sm3_update_return_wit_1_split_goal_5 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH2 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH4 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH5 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH6 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH7 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH8 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH9 : (u8_list_bounded Prefix )) (PreH10 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH12 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH13 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) data_len_pre Chunk )
  **  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  (store_sm3_ti )
|--
  “ (((Zlength (Prefix)) ÷ 64 ) = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ”
.

Definition sm3_update_return_wit_1_split_goal_6 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH2 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH4 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH5 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH6 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH7 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH8 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH9 : (u8_list_bounded Prefix )) (PreH10 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH12 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH13 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) data_len_pre Chunk )
  **  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  (store_sm3_ti )
|--
  “ (0 <= (Zlength ((sm3_tail ((app (Prefix) (Chunk))))))) ”
.

Definition sm3_update_return_wit_1_split_goal_7 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH2 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH4 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH5 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH6 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH7 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH8 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH9 : (u8_list_bounded Prefix )) (PreH10 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH12 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH13 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) data_len_pre Chunk )
  **  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  (store_sm3_ti )
|--
  “ ((Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) <= 64) ”
.

Definition sm3_update_return_wit_1_split_goal_8 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH2 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH4 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH5 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH6 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH7 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH8 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH9 : (u8_list_bounded Prefix )) (PreH10 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH12 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH13 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) data_len_pre Chunk )
  **  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (sm3_tail ((app (Prefix) (Chunk)))) ) ”
.

Definition sm3_update_return_wit_1_split_goal_spatial := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH2 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH4 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH5 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH6 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH7 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH8 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH9 : (u8_list_bounded Prefix )) (PreH10 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH12 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH13 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) data_len_pre Chunk )
  **  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  (store_sm3_ti )
|--
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) ) (64 - (Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) (sm3_tail ((app (Prefix) (Chunk)))) )
  **  (store_sm3_ti )
.

Definition sm3_update_return_wit_2 := 
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (u8_list_bounded TailBytes )) (PreH2 : ((Zlength (TailBytes)) = left)) (PreH3 : (u8_list_bounded TailBytes )) (PreH4 : ((Zlength (TailBytes)) = left)) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH6 : (offset = (64 * nblock ))) (PreH7 : (data_len = ((64 * nblock ) + left ))) (PreH8 : (0 <= left)) (PreH9 : (left < 64)) (PreH10 : ((left - left ) = 0)) (PreH11 : (0 <= (data_len_pre - data_len ))) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH21 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  (UCharArray.full data_pre (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (0 + left ) TailBytes )
  **  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
|--
  (store_sm3_ctx ctx_pre (app (Prefix) (Chunk)) )
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
) \/
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (u8_list_bounded TailBytes )) (PreH2 : ((Zlength (TailBytes)) = left)) (PreH3 : (u8_list_bounded TailBytes )) (PreH4 : ((Zlength (TailBytes)) = left)) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH6 : (offset = (64 * nblock ))) (PreH7 : (data_len = ((64 * nblock ) + left ))) (PreH8 : (0 <= left)) (PreH9 : (left < 64)) (PreH10 : ((left - left ) = 0)) (PreH11 : (0 <= (data_len_pre - data_len ))) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH21 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  (UCharArray.full data_pre (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (0 + left ) TailBytes )
  **  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
|--
  “ ((Zlength (Chunk)) = data_len_pre) ” 
  &&  “ (u8_list_bounded Chunk ) ” 
  &&  “ (u8_list_bounded (app (Prefix) (Chunk)) ) ” 
  &&  “ (left = (Zlength (TailBytes))) ” 
  &&  “ (0 <= (Zlength (TailBytes))) ” 
  &&  “ ((Zlength (TailBytes)) <= 64) ”
  &&  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) ) (64 - (Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) (sm3_tail ((app (Prefix) (Chunk)))) )
  **  (UCharArray.full data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
).

Definition sm3_update_return_wit_2_split_goal_1 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (u8_list_bounded TailBytes )) (PreH2 : ((Zlength (TailBytes)) = left)) (PreH3 : (u8_list_bounded TailBytes )) (PreH4 : ((Zlength (TailBytes)) = left)) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH6 : (offset = (64 * nblock ))) (PreH7 : (data_len = ((64 * nblock ) + left ))) (PreH8 : (0 <= left)) (PreH9 : (left < 64)) (PreH10 : ((left - left ) = 0)) (PreH11 : (0 <= (data_len_pre - data_len ))) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH21 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  (UCharArray.full data_pre (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (0 + left ) TailBytes )
  **  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
|--
  “ ((Zlength (Chunk)) = data_len_pre) ”
.

Definition sm3_update_return_wit_2_split_goal_2 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (u8_list_bounded TailBytes )) (PreH2 : ((Zlength (TailBytes)) = left)) (PreH3 : (u8_list_bounded TailBytes )) (PreH4 : ((Zlength (TailBytes)) = left)) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH6 : (offset = (64 * nblock ))) (PreH7 : (data_len = ((64 * nblock ) + left ))) (PreH8 : (0 <= left)) (PreH9 : (left < 64)) (PreH10 : ((left - left ) = 0)) (PreH11 : (0 <= (data_len_pre - data_len ))) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH21 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  (UCharArray.full data_pre (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (0 + left ) TailBytes )
  **  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded Chunk ) ”
.

Definition sm3_update_return_wit_2_split_goal_3 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (u8_list_bounded TailBytes )) (PreH2 : ((Zlength (TailBytes)) = left)) (PreH3 : (u8_list_bounded TailBytes )) (PreH4 : ((Zlength (TailBytes)) = left)) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH6 : (offset = (64 * nblock ))) (PreH7 : (data_len = ((64 * nblock ) + left ))) (PreH8 : (0 <= left)) (PreH9 : (left < 64)) (PreH10 : ((left - left ) = 0)) (PreH11 : (0 <= (data_len_pre - data_len ))) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH21 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  (UCharArray.full data_pre (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (0 + left ) TailBytes )
  **  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (app (Prefix) (Chunk)) ) ”
.

Definition sm3_update_return_wit_2_split_goal_4 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (u8_list_bounded TailBytes )) (PreH2 : ((Zlength (TailBytes)) = left)) (PreH3 : (u8_list_bounded TailBytes )) (PreH4 : ((Zlength (TailBytes)) = left)) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH6 : (offset = (64 * nblock ))) (PreH7 : (data_len = ((64 * nblock ) + left ))) (PreH8 : (0 <= left)) (PreH9 : (left < 64)) (PreH10 : ((left - left ) = 0)) (PreH11 : (0 <= (data_len_pre - data_len ))) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH21 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  (UCharArray.full data_pre (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (0 + left ) TailBytes )
  **  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
|--
  “ (left = (Zlength (TailBytes))) ”
.

Definition sm3_update_return_wit_2_split_goal_5 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (u8_list_bounded TailBytes )) (PreH2 : ((Zlength (TailBytes)) = left)) (PreH3 : (u8_list_bounded TailBytes )) (PreH4 : ((Zlength (TailBytes)) = left)) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH6 : (offset = (64 * nblock ))) (PreH7 : (data_len = ((64 * nblock ) + left ))) (PreH8 : (0 <= left)) (PreH9 : (left < 64)) (PreH10 : ((left - left ) = 0)) (PreH11 : (0 <= (data_len_pre - data_len ))) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH21 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  (UCharArray.full data_pre (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (0 + left ) TailBytes )
  **  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
|--
  “ (0 <= (Zlength (TailBytes))) ”
.

Definition sm3_update_return_wit_2_split_goal_6 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (u8_list_bounded TailBytes )) (PreH2 : ((Zlength (TailBytes)) = left)) (PreH3 : (u8_list_bounded TailBytes )) (PreH4 : ((Zlength (TailBytes)) = left)) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH6 : (offset = (64 * nblock ))) (PreH7 : (data_len = ((64 * nblock ) + left ))) (PreH8 : (0 <= left)) (PreH9 : (left < 64)) (PreH10 : ((left - left ) = 0)) (PreH11 : (0 <= (data_len_pre - data_len ))) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH21 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  (UCharArray.full data_pre (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (0 + left ) TailBytes )
  **  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
|--
  “ ((Zlength (TailBytes)) <= 64) ”
.

Definition sm3_update_return_wit_2_split_goal_spatial := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (retval: Z) (PreH1 : (u8_list_bounded TailBytes )) (PreH2 : ((Zlength (TailBytes)) = left)) (PreH3 : (u8_list_bounded TailBytes )) (PreH4 : ((Zlength (TailBytes)) = left)) (PreH5 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH6 : (offset = (64 * nblock ))) (PreH7 : (data_len = ((64 * nblock ) + left ))) (PreH8 : (0 <= left)) (PreH9 : (left < 64)) (PreH10 : ((left - left ) = 0)) (PreH11 : (0 <= (data_len_pre - data_len ))) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH16 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH17 : ((Zlength (TailBytes)) = left)) (PreH18 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH19 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH20 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH21 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  (UCharArray.full data_pre (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (0 + left ) TailBytes )
  **  (UCharArray.seg data offset (offset + left ) TailBytes )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
|--
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) ) (64 - (Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail ((app (Prefix) (Chunk)))))) (sm3_tail ((app (Prefix) (Chunk)))) )
  **  (UCharArray.full data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
.

Definition sm3_update_partial_solve_wit_1_pure := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH2 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH3 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH4 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH5 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH6 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH7 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH8 : (u8_list_bounded Prefix )) (PreH9 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH11 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH12 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH13 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) data_len_pre )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (0 <= data_len_pre) ”
.

Definition sm3_update_partial_solve_wit_1_aux := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH2 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH3 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH4 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH5 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH6 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH7 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH8 : (u8_list_bounded Prefix )) (PreH9 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH11 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH12 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH13 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) data_len_pre )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (store_sm3_ti )
|--
  “ (0 <= data_len_pre) ” 
  &&  “ (data_len_pre < (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sm3_tail (Prefix)) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <= 64) ” 
  &&  “ (0 <= (Zlength ((sm3_tail (Prefix))))) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ ((Zlength (Prefix)) < SM3_MAX_BYTES) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <> 0) ”
  &&  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) data_len_pre )
  **  (store_bytes data_pre data_len_pre Chunk )
  **  (UCharArray.undef_full ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) + (data_len_pre * sizeof(UCHAR))) ((64 - (Zlength ((sm3_tail (Prefix)))) ) - data_len_pre ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  (store_sm3_ti )
.

Definition sm3_update_partial_solve_wit_1 := sm3_update_partial_solve_wit_1_pure -> sm3_update_partial_solve_wit_1_aux.

Definition sm3_update_partial_solve_wit_2_pure := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH2 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded Chunk )) (PreH4 : ((Zlength (Chunk)) = data_len_pre)) (PreH5 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH6 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH7 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH8 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH9 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH11 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH12 : (u8_list_bounded Prefix )) (PreH13 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH14 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH15 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH16 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH17 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))) (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) (sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)) )
  **  (UCharArray.full data_pre (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
|--
  “ (0 <= (64 - (Zlength ((sm3_tail (Prefix)))) )) ”
.

Definition sm3_update_partial_solve_wit_2_aux := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (PreH1 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH2 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH3 : (u8_list_bounded Chunk )) (PreH4 : ((Zlength (Chunk)) = data_len_pre)) (PreH5 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH6 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH7 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH8 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH9 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH11 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH12 : (u8_list_bounded Prefix )) (PreH13 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH14 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH15 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH16 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH17 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))) (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) (sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)) )
  **  (UCharArray.full data_pre (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Prefix)))) ) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  (store_sm3_ti )
|--
  “ (0 <= (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded Chunk ) ” 
  &&  “ ((Zlength (Chunk)) = data_len_pre) ” 
  &&  “ (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sm3_tail (Prefix)) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <= 64) ” 
  &&  “ (0 <= (Zlength ((sm3_tail (Prefix))))) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ ((Zlength (Prefix)) < SM3_MAX_BYTES) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <> 0) ”
  &&  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))) (64 - (Zlength ((sm3_tail (Prefix)))) ) )
  **  (store_bytes data_pre (64 - (Zlength ((sm3_tail (Prefix)))) ) (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )
  **  (UCharArray.full (data_pre + ((64 - (Zlength ((sm3_tail (Prefix)))) ) * sizeof(UCHAR))) (data_len_pre - (64 - (Zlength ((sm3_tail (Prefix)))) ) ) (sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Prefix)))) (sm3_tail (Prefix)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  (store_sm3_ti )
.

Definition sm3_update_partial_solve_wit_2 := sm3_update_partial_solve_wit_2_pure -> sm3_update_partial_solve_wit_2_aux.

Definition sm3_update_partial_solve_wit_3_pure := 
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH2 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH3 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH4 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH5 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH6 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH9 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH10 : (u8_list_bounded Chunk )) (PreH11 : ((Zlength (Chunk)) = data_len_pre)) (PreH12 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH13 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH15 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH16 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH19 : (u8_list_bounded Prefix )) (PreH20 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH21 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH22 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH23 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) 1 ) ” 
  &&  “ ((Zlength ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) = (64 * 1 )) ” 
  &&  “ (u8_list_bounded (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) ) ”
) \/
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (data_len_pre <= UINT64_MAX)) (PreH2 : (0 <= UINT64_MAX)) (PreH3 : ((64 - (Zlength ((sm3_tail (Prefix)))) ) <= UINT64_MAX)) (PreH4 : (((Zlength (Prefix)) ÷ 64 ) <= UINT64_MAX)) (PreH5 : ((Zlength ((sm3_tail (Prefix)))) <= UINT64_MAX)) (PreH6 : (data_len_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : ((64 - (Zlength ((sm3_tail (Prefix)))) ) >= 0)) (PreH9 : (((Zlength (Prefix)) ÷ 64 ) >= 0)) (PreH10 : ((Zlength ((sm3_tail (Prefix)))) >= 0)) (PreH11 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH12 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH13 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH14 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH15 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH16 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH17 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH18 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH19 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH20 : (u8_list_bounded Chunk )) (PreH21 : ((Zlength (Chunk)) = data_len_pre)) (PreH22 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH23 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH25 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH26 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH27 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH28 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH29 : (u8_list_bounded Prefix )) (PreH30 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH31 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH32 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH33 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH34 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) ) ” 
  &&  “ ((Zlength ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) = (64 * 1 )) ” 
  &&  “ (sm3_compress_input_aligned (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) 1 ) ”
).

Definition sm3_update_partial_solve_wit_3_pure_split_goal_1 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (data_len_pre <= UINT64_MAX)) (PreH2 : (0 <= UINT64_MAX)) (PreH3 : ((64 - (Zlength ((sm3_tail (Prefix)))) ) <= UINT64_MAX)) (PreH4 : (((Zlength (Prefix)) ÷ 64 ) <= UINT64_MAX)) (PreH5 : ((Zlength ((sm3_tail (Prefix)))) <= UINT64_MAX)) (PreH6 : (data_len_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : ((64 - (Zlength ((sm3_tail (Prefix)))) ) >= 0)) (PreH9 : (((Zlength (Prefix)) ÷ 64 ) >= 0)) (PreH10 : ((Zlength ((sm3_tail (Prefix)))) >= 0)) (PreH11 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH12 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH13 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH14 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH15 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH16 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH17 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH18 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH19 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH20 : (u8_list_bounded Chunk )) (PreH21 : ((Zlength (Chunk)) = data_len_pre)) (PreH22 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH23 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH25 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH26 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH27 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH28 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH29 : (u8_list_bounded Prefix )) (PreH30 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH31 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH32 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH33 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH34 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) ) ”
.

Definition sm3_update_partial_solve_wit_3_pure_split_goal_2 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (data_len_pre <= UINT64_MAX)) (PreH2 : (0 <= UINT64_MAX)) (PreH3 : ((64 - (Zlength ((sm3_tail (Prefix)))) ) <= UINT64_MAX)) (PreH4 : (((Zlength (Prefix)) ÷ 64 ) <= UINT64_MAX)) (PreH5 : ((Zlength ((sm3_tail (Prefix)))) <= UINT64_MAX)) (PreH6 : (data_len_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : ((64 - (Zlength ((sm3_tail (Prefix)))) ) >= 0)) (PreH9 : (((Zlength (Prefix)) ÷ 64 ) >= 0)) (PreH10 : ((Zlength ((sm3_tail (Prefix)))) >= 0)) (PreH11 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH12 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH13 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH14 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH15 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH16 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH17 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH18 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH19 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH20 : (u8_list_bounded Chunk )) (PreH21 : ((Zlength (Chunk)) = data_len_pre)) (PreH22 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH23 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH25 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH26 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH27 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH28 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH29 : (u8_list_bounded Prefix )) (PreH30 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH31 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH32 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH33 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH34 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
|--
  “ ((Zlength ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) = (64 * 1 )) ”
.

Definition sm3_update_partial_solve_wit_3_pure_split_goal_3 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (data_len_pre <= UINT64_MAX)) (PreH2 : (0 <= UINT64_MAX)) (PreH3 : ((64 - (Zlength ((sm3_tail (Prefix)))) ) <= UINT64_MAX)) (PreH4 : (((Zlength (Prefix)) ÷ 64 ) <= UINT64_MAX)) (PreH5 : ((Zlength ((sm3_tail (Prefix)))) <= UINT64_MAX)) (PreH6 : (data_len_pre >= 0)) (PreH7 : (0 >= 0)) (PreH8 : ((64 - (Zlength ((sm3_tail (Prefix)))) ) >= 0)) (PreH9 : (((Zlength (Prefix)) ÷ 64 ) >= 0)) (PreH10 : ((Zlength ((sm3_tail (Prefix)))) >= 0)) (PreH11 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH12 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH13 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH14 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH15 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH16 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH17 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH18 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH19 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH20 : (u8_list_bounded Chunk )) (PreH21 : ((Zlength (Chunk)) = data_len_pre)) (PreH22 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH23 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH25 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH26 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH27 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH28 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH29 : (u8_list_bounded Prefix )) (PreH30 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH31 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH32 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH33 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH34 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  ((( &( "left" ) )) # UInt64  |-> (64 - (Zlength ((sm3_tail (Prefix)))) ))
  **  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "nblock" ) )) # UInt64  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len_pre)
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) 1 ) ”
.

Definition sm3_update_partial_solve_wit_3_aux := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (retval: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )) (PreH2 : ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8)) (PreH3 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH4 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH5 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH6 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH7 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) )) (PreH9 : ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH10 : (u8_list_bounded Chunk )) (PreH11 : ((Zlength (Chunk)) = data_len_pre)) (PreH12 : (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) ))) (PreH13 : (u8_list_bounded (sm3_tail (Prefix)) )) (PreH14 : ((Zlength ((sm3_tail (Prefix)))) <= 64)) (PreH15 : (0 <= (Zlength ((sm3_tail (Prefix)))))) (PreH16 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : ((Zlength (Prefix)) < SM3_MAX_BYTES)) (PreH19 : (u8_list_bounded Prefix )) (PreH20 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH21 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH22 : (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES)) (PreH23 : (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) )) (PreH24 : ((Zlength ((sm3_tail (Prefix)))) <> 0)) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) 1 ) ” 
  &&  “ ((Zlength ((app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))))) = (64 * 1 )) ” 
  &&  “ (u8_list_bounded (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) ) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) ) ” 
  &&  “ ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))))) = 8) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength ((sm3_tail (Prefix)))) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded (sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) = (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded Chunk ) ” 
  &&  “ ((Zlength (Chunk)) = data_len_pre) ” 
  &&  “ (data_len_pre >= (64 - (Zlength ((sm3_tail (Prefix)))) )) ” 
  &&  “ (u8_list_bounded (sm3_tail (Prefix)) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <= 64) ” 
  &&  “ (0 <= (Zlength ((sm3_tail (Prefix))))) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ ((Zlength (Prefix)) < SM3_MAX_BYTES) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (((Zlength (Prefix)) + data_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned data_pre data_len_pre (Zlength ((sm3_tail (Prefix)))) ) ” 
  &&  “ ((Zlength ((sm3_tail (Prefix)))) <> 0) ”
  &&  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Prefix)))) )
  **  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) (app ((sm3_tail (Prefix))) ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk)))) )
  **  (store_sm3_ti )
  **  (UCharArray.full data_pre data_len_pre (app ((sublist (0) ((64 - (Zlength ((sm3_tail (Prefix)))) )) (Chunk))) ((sublist ((64 - (Zlength ((sm3_tail (Prefix)))) )) (data_len_pre) (Chunk)))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Prefix)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Prefix)) ÷ 64 ))
.

Definition sm3_update_partial_solve_wit_3 := sm3_update_partial_solve_wit_3_pure -> sm3_update_partial_solve_wit_3_aux.

Definition sm3_update_partial_solve_wit_4_pure := 
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (nblock > 0)) (PreH4 : (offset = (64 * nblock ))) (PreH5 : (data_len = ((64 * nblock ) + left ))) (PreH6 : (0 <= left)) (PreH7 : (left < 64)) (PreH8 : (0 <= offset)) (PreH9 : (offset <= data_len)) (PreH10 : (0 <= (data_len_pre - data_len ))) (PreH11 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : (sm3_compress_input_aligned data nblock )) (PreH16 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH17 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH18 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH19 : ((Zlength (TailBytes)) = left)) (PreH20 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH21 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes)))))))) (PreH22 : (NBlocks = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 ))) (PreH23 : ((sm3_tail ((app (Prefix) (ConsumedBytes)))) = (@nil Z))) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned data nblock ) ” 
  &&  “ (u8_list_bounded BulkBytes ) ”
) \/
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (NBlocks <= UINT64_MAX)) (PreH2 : (left <= UINT64_MAX)) (PreH3 : (data_len <= UINT64_MAX)) (PreH4 : (nblock <= UINT64_MAX)) (PreH5 : (offset <= UINT64_MAX)) (PreH6 : (NBlocks >= 0)) (PreH7 : (left >= 0)) (PreH8 : (data_len >= 0)) (PreH9 : (nblock >= 0)) (PreH10 : (offset >= 0)) (PreH11 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH12 : ((Zlength (State)) = 8)) (PreH13 : (nblock > 0)) (PreH14 : (offset = (64 * nblock ))) (PreH15 : (data_len = ((64 * nblock ) + left ))) (PreH16 : (0 <= left)) (PreH17 : (left < 64)) (PreH18 : (0 <= offset)) (PreH19 : (offset <= data_len)) (PreH20 : (0 <= (data_len_pre - data_len ))) (PreH21 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH22 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH23 : (u8_list_bounded Prefix )) (PreH24 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH25 : (sm3_compress_input_aligned data nblock )) (PreH26 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH27 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH28 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH29 : ((Zlength (TailBytes)) = left)) (PreH30 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH31 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes)))))))) (PreH32 : (NBlocks = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 ))) (PreH33 : ((sm3_tail ((app (Prefix) (ConsumedBytes)))) = (@nil Z))) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded BulkBytes ) ”
).

Definition sm3_update_partial_solve_wit_4_pure_split_goal_1 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (NBlocks <= UINT64_MAX)) (PreH2 : (left <= UINT64_MAX)) (PreH3 : (data_len <= UINT64_MAX)) (PreH4 : (nblock <= UINT64_MAX)) (PreH5 : (offset <= UINT64_MAX)) (PreH6 : (NBlocks >= 0)) (PreH7 : (left >= 0)) (PreH8 : (data_len >= 0)) (PreH9 : (nblock >= 0)) (PreH10 : (offset >= 0)) (PreH11 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH12 : ((Zlength (State)) = 8)) (PreH13 : (nblock > 0)) (PreH14 : (offset = (64 * nblock ))) (PreH15 : (data_len = ((64 * nblock ) + left ))) (PreH16 : (0 <= left)) (PreH17 : (left < 64)) (PreH18 : (0 <= offset)) (PreH19 : (offset <= data_len)) (PreH20 : (0 <= (data_len_pre - data_len ))) (PreH21 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH22 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH23 : (u8_list_bounded Prefix )) (PreH24 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH25 : (sm3_compress_input_aligned data nblock )) (PreH26 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH27 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH28 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH29 : ((Zlength (TailBytes)) = left)) (PreH30 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH31 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes)))))))) (PreH32 : (NBlocks = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 ))) (PreH33 : ((sm3_tail ((app (Prefix) (ConsumedBytes)))) = (@nil Z))) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded BulkBytes ) ”
.

Definition sm3_update_partial_solve_wit_4_aux := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (nblock > 0)) (PreH4 : (offset = (64 * nblock ))) (PreH5 : (data_len = ((64 * nblock ) + left ))) (PreH6 : (0 <= left)) (PreH7 : (left < 64)) (PreH8 : (0 <= offset)) (PreH9 : (offset <= data_len)) (PreH10 : (0 <= (data_len_pre - data_len ))) (PreH11 : (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre)) (PreH12 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH13 : (u8_list_bounded Prefix )) (PreH14 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH15 : (sm3_compress_input_aligned data nblock )) (PreH16 : (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock )) (PreH17 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH18 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH19 : ((Zlength (TailBytes)) = left)) (PreH20 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH21 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes)))))))) (PreH22 : (NBlocks = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 ))) (PreH23 : ((sm3_tail ((app (Prefix) (ConsumedBytes)))) = (@nil Z))) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned data nblock ) ” 
  &&  “ (u8_list_bounded BulkBytes ) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS State ) ” 
  &&  “ ((Zlength (State)) = 8) ” 
  &&  “ (nblock > 0) ” 
  &&  “ (offset = (64 * nblock )) ” 
  &&  “ (data_len = ((64 * nblock ) + left )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < 64) ” 
  &&  “ (0 <= offset) ” 
  &&  “ (offset <= data_len) ” 
  &&  “ (0 <= (data_len_pre - data_len )) ” 
  &&  “ (((data_len_pre - data_len ) + (64 * nblock ) ) <= data_len_pre) ” 
  &&  “ (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_compress_input_aligned data nblock ) ” 
  &&  “ (sm3_compress_input_aligned (data_pre + ((data_len_pre - ((64 * nblock ) + left ) ) * sizeof(UCHAR))) nblock ) ” 
  &&  “ ((Zlength (ConsumedBytes)) = (data_len_pre - data_len )) ” 
  &&  “ ((Zlength (BulkBytes)) = (64 * nblock )) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (ConsumedBytes))))))) ” 
  &&  “ (NBlocks = ((Zlength ((app (Prefix) (ConsumedBytes)))) ÷ 64 )) ” 
  &&  “ ((sm3_tail ((app (Prefix) (ConsumedBytes)))) = (@nil Z)) ”
  &&  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 State )
  **  (store_bytes data (64 * nblock ) BulkBytes )
  **  (store_sm3_ti )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
.

Definition sm3_update_partial_solve_wit_4 := sm3_update_partial_solve_wit_4_pure -> sm3_update_partial_solve_wit_4_aux.

Definition sm3_update_partial_solve_wit_5_pure := 
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (offset = (64 * nblock ))) (PreH2 : (data_len = ((64 * nblock ) + left ))) (PreH3 : (0 <= left)) (PreH4 : (left < 64)) (PreH5 : ((left - left ) = 0)) (PreH6 : (0 <= (data_len_pre - data_len ))) (PreH7 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded Prefix )) (PreH9 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH10 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH11 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH12 : ((Zlength (TailBytes)) = left)) (PreH13 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH14 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH15 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH16 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((left - left ) * sizeof(UCHAR))) left )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
|--
  “ (0 <= left) ” 
  &&  “ (u8_list_bounded TailBytes ) ”
) \/
(
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (NBlocks <= UINT64_MAX)) (PreH2 : (left <= UINT64_MAX)) (PreH3 : (data_len <= UINT64_MAX)) (PreH4 : (nblock <= UINT64_MAX)) (PreH5 : (offset <= UINT64_MAX)) (PreH6 : (NBlocks >= 0)) (PreH7 : (left >= 0)) (PreH8 : (data_len >= 0)) (PreH9 : (nblock >= 0)) (PreH10 : (offset >= 0)) (PreH11 : (offset = (64 * nblock ))) (PreH12 : (data_len = ((64 * nblock ) + left ))) (PreH13 : (0 <= left)) (PreH14 : (left < 64)) (PreH15 : ((left - left ) = 0)) (PreH16 : (0 <= (data_len_pre - data_len ))) (PreH17 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH18 : (u8_list_bounded Prefix )) (PreH19 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH20 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH21 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH22 : ((Zlength (TailBytes)) = left)) (PreH23 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH24 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH25 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH26 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((left - left ) * sizeof(UCHAR))) left )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded TailBytes ) ”
).

Definition sm3_update_partial_solve_wit_5_pure_split_goal_1 := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (NBlocks <= UINT64_MAX)) (PreH2 : (left <= UINT64_MAX)) (PreH3 : (data_len <= UINT64_MAX)) (PreH4 : (nblock <= UINT64_MAX)) (PreH5 : (offset <= UINT64_MAX)) (PreH6 : (NBlocks >= 0)) (PreH7 : (left >= 0)) (PreH8 : (data_len >= 0)) (PreH9 : (nblock >= 0)) (PreH10 : (offset >= 0)) (PreH11 : (offset = (64 * nblock ))) (PreH12 : (data_len = ((64 * nblock ) + left ))) (PreH13 : (0 <= left)) (PreH14 : (left < 64)) (PreH15 : ((left - left ) = 0)) (PreH16 : (0 <= (data_len_pre - data_len ))) (PreH17 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH18 : (u8_list_bounded Prefix )) (PreH19 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH20 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH21 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH22 : ((Zlength (TailBytes)) = left)) (PreH23 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH24 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH25 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH26 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "nblock" ) )) # UInt64  |-> nblock)
  **  ((( &( "data_len" ) )) # UInt64  |-> data_len)
  **  ((( &( "left" ) )) # UInt64  |-> left)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((left - left ) * sizeof(UCHAR))) left )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded TailBytes ) ”
.

Definition sm3_update_partial_solve_wit_5_aux := 
forall (data_len_pre: Z) (data_pre: Z) (ctx_pre: Z) (Chunk: (@list Z)) (Prefix: (@list Z)) (State: (@list Z)) (NBlocks: Z) (ConsumedBytes: (@list Z)) (BulkBytes: (@list Z)) (TailBytes: (@list Z)) (offset: Z) (nblock: Z) (data_len: Z) (left: Z) (data: Z) (PreH1 : (offset = (64 * nblock ))) (PreH2 : (data_len = ((64 * nblock ) + left ))) (PreH3 : (0 <= left)) (PreH4 : (left < 64)) (PreH5 : ((left - left ) = 0)) (PreH6 : (0 <= (data_len_pre - data_len ))) (PreH7 : (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR))))) (PreH8 : (u8_list_bounded Prefix )) (PreH9 : ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES)) (PreH10 : ((Zlength (ConsumedBytes)) = (data_len_pre - data_len ))) (PreH11 : ((Zlength (BulkBytes)) = (64 * nblock ))) (PreH12 : ((Zlength (TailBytes)) = left)) (PreH13 : (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes)))))) (PreH14 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk)))))))) (PreH15 : (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 ))) (PreH16 : (TailBytes = (sm3_tail ((app (Prefix) (Chunk)))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((left - left ) * sizeof(UCHAR))) left )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (UCharArray.seg data_pre ((data_len_pre - data_len ) + (64 * nblock ) ) data_len_pre TailBytes )
  **  (store_sm3_ti )
|--
  “ (0 <= left) ” 
  &&  “ (u8_list_bounded TailBytes ) ” 
  &&  “ (offset = (64 * nblock )) ” 
  &&  “ (data_len = ((64 * nblock ) + left )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < 64) ” 
  &&  “ ((left - left ) = 0) ” 
  &&  “ (0 <= (data_len_pre - data_len )) ” 
  &&  “ (data = (data_pre + ((data_len_pre - data_len ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Prefix ) ” 
  &&  “ ((Zlength ((app (Prefix) (Chunk)))) < SM3_MAX_BYTES) ” 
  &&  “ ((Zlength (ConsumedBytes)) = (data_len_pre - data_len )) ” 
  &&  “ ((Zlength (BulkBytes)) = (64 * nblock )) ” 
  &&  “ ((Zlength (TailBytes)) = left) ” 
  &&  “ (Chunk = (app (ConsumedBytes) ((app (BulkBytes) (TailBytes))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((app (Prefix) (Chunk))))))) ” 
  &&  “ (NBlocks = ((Zlength ((app (Prefix) (Chunk)))) ÷ 64 )) ” 
  &&  “ (TailBytes = (sm3_tail ((app (Prefix) (Chunk))))) ”
  &&  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) left )
  **  (store_bytes (data + (offset * sizeof(UCHAR))) left TailBytes )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> left)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> NBlocks)
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (left * sizeof(UCHAR))) (64 - left ) )
  **  (UCharArray.seg data_pre 0 (data_len_pre - data_len ) ConsumedBytes )
  **  (UCharArray.seg data_pre (data_len_pre - data_len ) ((data_len_pre - data_len ) + (64 * nblock ) ) BulkBytes )
  **  (store_sm3_ti )
.

Definition sm3_update_partial_solve_wit_5 := sm3_update_partial_solve_wit_5_pure -> sm3_update_partial_solve_wit_5_aux.

Module Type VC_Correct.

Include byte_memory_views_Strategy_Correct.
Include sm3_ctx_views_Strategy_Correct.
Include sm3_streaming_memory_views_Strategy_Correct.

Axiom proof_of_sm3_update_safety_wit_1 : sm3_update_safety_wit_1.
Axiom proof_of_sm3_update_safety_wit_2 : sm3_update_safety_wit_2.
Axiom proof_of_sm3_update_safety_wit_3 : sm3_update_safety_wit_3.
Axiom proof_of_sm3_update_safety_wit_4 : sm3_update_safety_wit_4.
Axiom proof_of_sm3_update_safety_wit_5 : sm3_update_safety_wit_5.
Axiom proof_of_sm3_update_safety_wit_6 : sm3_update_safety_wit_6.
Axiom proof_of_sm3_update_safety_wit_7 : sm3_update_safety_wit_7.
Axiom proof_of_sm3_update_safety_wit_8 : sm3_update_safety_wit_8.
Axiom proof_of_sm3_update_safety_wit_9 : sm3_update_safety_wit_9.
Axiom proof_of_sm3_update_safety_wit_10 : sm3_update_safety_wit_10.
Axiom proof_of_sm3_update_safety_wit_11 : sm3_update_safety_wit_11.
Axiom proof_of_sm3_update_safety_wit_12 : sm3_update_safety_wit_12.
Axiom proof_of_sm3_update_safety_wit_13 : sm3_update_safety_wit_13.
Axiom proof_of_sm3_update_safety_wit_14 : sm3_update_safety_wit_14.
Axiom proof_of_sm3_update_safety_wit_15 : sm3_update_safety_wit_15.
Axiom proof_of_sm3_update_safety_wit_16 : sm3_update_safety_wit_16.
Axiom proof_of_sm3_update_safety_wit_17 : sm3_update_safety_wit_17.
Axiom proof_of_sm3_update_safety_wit_18 : sm3_update_safety_wit_18.
Axiom proof_of_sm3_update_safety_wit_19 : sm3_update_safety_wit_19.
Axiom proof_of_sm3_update_safety_wit_20 : sm3_update_safety_wit_20.
Axiom proof_of_sm3_update_safety_wit_21 : sm3_update_safety_wit_21.
Axiom proof_of_sm3_update_entail_wit_1 : sm3_update_entail_wit_1.
Axiom proof_of_sm3_update_entail_wit_2 : sm3_update_entail_wit_2.
Axiom proof_of_sm3_update_entail_wit_3 : sm3_update_entail_wit_3.
Axiom proof_of_sm3_update_entail_wit_4 : sm3_update_entail_wit_4.
Axiom proof_of_sm3_update_entail_wit_5 : sm3_update_entail_wit_5.
Axiom proof_of_sm3_update_entail_wit_6 : sm3_update_entail_wit_6.
Axiom proof_of_sm3_update_entail_wit_7 : sm3_update_entail_wit_7.
Axiom proof_of_sm3_update_entail_wit_8 : sm3_update_entail_wit_8.
Axiom proof_of_sm3_update_entail_wit_9_1 : sm3_update_entail_wit_9_1.
Axiom proof_of_sm3_update_entail_wit_9_2 : sm3_update_entail_wit_9_2.
Axiom proof_of_sm3_update_entail_wit_10_1 : sm3_update_entail_wit_10_1.
Axiom proof_of_sm3_update_entail_wit_10_2 : sm3_update_entail_wit_10_2.
Axiom proof_of_sm3_update_entail_wit_11 : sm3_update_entail_wit_11.
Axiom proof_of_sm3_update_entail_wit_12_1 : sm3_update_entail_wit_12_1.
Axiom proof_of_sm3_update_entail_wit_12_2 : sm3_update_entail_wit_12_2.
Axiom proof_of_sm3_update_entail_wit_13 : sm3_update_entail_wit_13.
Axiom proof_of_sm3_update_entail_wit_14 : sm3_update_entail_wit_14.
Axiom proof_of_sm3_update_entail_wit_15 : sm3_update_entail_wit_15.
Axiom proof_of_sm3_update_entail_wit_16 : sm3_update_entail_wit_16.
Axiom proof_of_sm3_update_return_wit_1 : sm3_update_return_wit_1.
Axiom proof_of_sm3_update_return_wit_2 : sm3_update_return_wit_2.
Axiom proof_of_sm3_update_partial_solve_wit_1_pure : sm3_update_partial_solve_wit_1_pure.
Axiom proof_of_sm3_update_partial_solve_wit_1 : sm3_update_partial_solve_wit_1.
Axiom proof_of_sm3_update_partial_solve_wit_2_pure : sm3_update_partial_solve_wit_2_pure.
Axiom proof_of_sm3_update_partial_solve_wit_2 : sm3_update_partial_solve_wit_2.
Axiom proof_of_sm3_update_partial_solve_wit_3_pure : sm3_update_partial_solve_wit_3_pure.
Axiom proof_of_sm3_update_partial_solve_wit_3 : sm3_update_partial_solve_wit_3.
Axiom proof_of_sm3_update_partial_solve_wit_4_pure : sm3_update_partial_solve_wit_4_pure.
Axiom proof_of_sm3_update_partial_solve_wit_4 : sm3_update_partial_solve_wit_4.
Axiom proof_of_sm3_update_partial_solve_wit_5_pure : sm3_update_partial_solve_wit_5_pure.
Axiom proof_of_sm3_update_partial_solve_wit_5 : sm3_update_partial_solve_wit_5.

End VC_Correct.
