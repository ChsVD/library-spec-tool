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
      SimpleC.EE.Applications_human.sm2.lib.sm3_final_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_ctx_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_ctx_views_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_word_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_word_views_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_streaming_memory_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_streaming_memory_views_strategy_proof.

(*----- Function sm3_final -----*)

Definition sm3_final_safety_wit_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (PreH1 : (aligned_4 digest_pre )) ,
  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  (store_sm3_ctx ctx_pre Message )
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_final_safety_wit_2 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (PreH1 : (aligned_4 digest_pre )) ,
  ((( &( "count" ) )) # Ptr  |->_)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  (store_sm3_ctx ctx_pre Message )
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_final_safety_wit_3 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (PreH1 : (aligned_4 digest_pre )) ,
  ((( &( "count" ) )) # Ptr  |->_)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  (store_sm3_ctx ctx_pre Message )
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition sm3_final_safety_wit_4 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (PreH1 : (aligned_4 digest_pre )) ,
  ((( &( "count" ) )) # Ptr  |->_)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  (store_sm3_ctx ctx_pre Message )
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sm3_final_safety_wit_5 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength (Tail)) Tail )
  **  (UCharArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength (Tail)) 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (128 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 128) ”
.

Definition sm3_final_safety_wit_6 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) 64 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition sm3_final_safety_wit_7 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) 64 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition sm3_final_safety_wit_8 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) <= 55)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (55 - (Zlength (Tail)) ) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_final_safety_wit_9 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) <= 55)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (55 - (Zlength (Tail)) ) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sm3_final_safety_wit_10 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) <= 55)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (55 - (Zlength (Tail)) ) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_final_safety_wit_11 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) <= 55)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (55 - (Zlength (Tail)) ) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition sm3_final_safety_wit_12 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) <= 55)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (55 - (Zlength (Tail)) ) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition sm3_final_safety_wit_13 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (63 - (Zlength (Tail)) ) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_final_safety_wit_14 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (63 - (Zlength (Tail)) ) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sm3_final_safety_wit_15 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (63 - (Zlength (Tail)) ) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_final_safety_wit_16 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (63 - (Zlength (Tail)) ) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition sm3_final_safety_wit_17 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (63 - (Zlength (Tail)) ) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sm3_final_safety_wit_18 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (BlockBytes: (@list Z)) (i: Z) (count: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (u8_list_bounded Message )) (PreH4 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH5 : (Tail = (sm3_tail (Message)))) (PreH6 : (56 <= (Zlength (Tail)))) (PreH7 : ((Zlength (Tail)) < 64)) (PreH8 : (BlockBytes = (app (Tail) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail)) ))))))))) (PreH9 : ((Zlength (BlockBytes)) = 64)) (PreH10 : (u8_list_bounded BlockBytes )) (PreH11 : (i = 0)) (PreH12 : (aligned_4 digest_pre )) (PreH13 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH14 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH15 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH16 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_final_safety_wit_19 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (BlockBytes: (@list Z)) (i: Z) (count: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (u8_list_bounded Message )) (PreH4 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH5 : (Tail = (sm3_tail (Message)))) (PreH6 : (56 <= (Zlength (Tail)))) (PreH7 : ((Zlength (Tail)) < 64)) (PreH8 : (BlockBytes = (app (Tail) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail)) ))))))))) (PreH9 : ((Zlength (BlockBytes)) = 64)) (PreH10 : (u8_list_bounded BlockBytes )) (PreH11 : (i = 0)) (PreH12 : (aligned_4 digest_pre )) (PreH13 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH14 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH15 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH16 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_final_safety_wit_20 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (BlockBytes: (@list Z)) (i: Z) (count: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (u8_list_bounded Message )) (PreH4 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH5 : (Tail = (sm3_tail (Message)))) (PreH6 : (56 <= (Zlength (Tail)))) (PreH7 : ((Zlength (Tail)) < 64)) (PreH8 : (BlockBytes = (app (Tail) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail)) ))))))))) (PreH9 : ((Zlength (BlockBytes)) = 64)) (PreH10 : (u8_list_bounded BlockBytes )) (PreH11 : (i = 0)) (PreH12 : (aligned_4 digest_pre )) (PreH13 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH14 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH15 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH16 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sm3_final_safety_wit_21 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : ((Zlength (BlockBytes)) = 64)) (PreH11 : (u8_list_bounded BlockBytes )) (PreH12 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) - (Zlength (Tail)) ) * sizeof(UCHAR))) 56 )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ ((64 - 8 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (64 - 8 )) ”
.

Definition sm3_final_safety_wit_22 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : ((Zlength (BlockBytes)) = 64)) (PreH11 : (u8_list_bounded BlockBytes )) (PreH12 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) - (Zlength (Tail)) ) * sizeof(UCHAR))) 56 )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_final_safety_wit_23 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : ((Zlength (BlockBytes)) = 64)) (PreH11 : (u8_list_bounded BlockBytes )) (PreH12 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) - (Zlength (Tail)) ) * sizeof(UCHAR))) 56 )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_final_safety_wit_24 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : ((Zlength (BlockBytes)) = 64)) (PreH11 : (u8_list_bounded BlockBytes )) (PreH12 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) - (Zlength (Tail)) ) * sizeof(UCHAR))) 56 )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition sm3_final_safety_wit_25 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : ((Zlength (BlockBytes)) = 64)) (PreH11 : (u8_list_bounded BlockBytes )) (PreH12 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) - (Zlength (Tail)) ) * sizeof(UCHAR))) 56 )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sm3_final_safety_wit_26 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_final_safety_wit_27 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (24 <= 63) ” 
  &&  “ (0 <= 24) ”
.

Definition sm3_final_safety_wit_28 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (23 <= 63) ” 
  &&  “ (0 <= 23) ”
.

Definition sm3_final_safety_wit_29 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (8 <= 63) ” 
  &&  “ (0 <= 8) ”
.

Definition sm3_final_safety_wit_30 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (23 <= 63) ” 
  &&  “ (0 <= 23) ”
.

Definition sm3_final_safety_wit_31 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (8 <= 63) ” 
  &&  “ (0 <= 8) ”
.

Definition sm3_final_safety_wit_32 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (23 <= 63) ” 
  &&  “ (0 <= 23) ”
.

Definition sm3_final_safety_wit_33 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (24 <= 63) ” 
  &&  “ (0 <= 24) ”
.

Definition sm3_final_safety_wit_34 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (23 <= 63) ” 
  &&  “ (0 <= 23) ”
.

Definition sm3_final_safety_wit_35 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (23 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 23) ”
.

Definition sm3_final_safety_wit_36 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (24 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 24) ”
.

Definition sm3_final_safety_wit_37 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (23 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 23) ”
.

Definition sm3_final_safety_wit_38 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sm3_final_safety_wit_39 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (65280 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65280) ”
.

Definition sm3_final_safety_wit_40 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (23 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 23) ”
.

Definition sm3_final_safety_wit_41 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sm3_final_safety_wit_42 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (16711680 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16711680) ”
.

Definition sm3_final_safety_wit_43 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (23 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 23) ”
.

Definition sm3_final_safety_wit_44 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (24 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 24) ”
.

Definition sm3_final_safety_wit_45 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sm3_final_safety_wit_46 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (24 <= 31) ” 
  &&  “ (0 <= 24) ”
.

Definition sm3_final_safety_wit_47 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (3 <= 63) ” 
  &&  “ (0 <= 3) ”
.

Definition sm3_final_safety_wit_48 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (9 <= 63) ” 
  &&  “ (0 <= 9) ”
.

Definition sm3_final_safety_wit_49 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
.

Definition sm3_final_safety_wit_50 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (3 <= 63) ” 
  &&  “ (0 <= 3) ”
.

Definition sm3_final_safety_wit_51 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (9 <= 63) ” 
  &&  “ (0 <= 9) ”
.

Definition sm3_final_safety_wit_52 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
.

Definition sm3_final_safety_wit_53 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (3 <= 63) ” 
  &&  “ (0 <= 3) ”
.

Definition sm3_final_safety_wit_54 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (9 <= 63) ” 
  &&  “ (0 <= 9) ”
.

Definition sm3_final_safety_wit_55 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (24 <= 31) ” 
  &&  “ (0 <= 24) ”
.

Definition sm3_final_safety_wit_56 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (3 <= 63) ” 
  &&  “ (0 <= 3) ”
.

Definition sm3_final_safety_wit_57 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (9 <= 63) ” 
  &&  “ (0 <= 9) ”
.

Definition sm3_final_safety_wit_58 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition sm3_final_safety_wit_59 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sm3_final_safety_wit_60 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (24 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 24) ”
.

Definition sm3_final_safety_wit_61 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition sm3_final_safety_wit_62 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sm3_final_safety_wit_63 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sm3_final_safety_wit_64 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (65280 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65280) ”
.

Definition sm3_final_safety_wit_65 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition sm3_final_safety_wit_66 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sm3_final_safety_wit_67 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sm3_final_safety_wit_68 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (16711680 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16711680) ”
.

Definition sm3_final_safety_wit_69 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition sm3_final_safety_wit_70 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sm3_final_safety_wit_71 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (24 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 24) ”
.

Definition sm3_final_safety_wit_72 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (u8_list_bounded Message )) (PreH4 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH5 : (Tail = (sm3_tail (Message)))) (PreH6 : (0 <= (Zlength (Tail)))) (PreH7 : ((Zlength (Tail)) < 64)) (PreH8 : (BlockBytes = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))))) (PreH9 : ((Zlength (BlockBytes)) = 64)) (PreH10 : (u8_list_bounded BlockBytes )) (PreH11 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH12 : (i = 0)) (PreH13 : (aligned_4 digest_pre )) (PreH14 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH15 : (aligned_4 count )) (PreH16 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_final_safety_wit_73 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (u8_list_bounded Message )) (PreH4 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH5 : (Tail = (sm3_tail (Message)))) (PreH6 : (0 <= (Zlength (Tail)))) (PreH7 : ((Zlength (Tail)) < 64)) (PreH8 : (BlockBytes = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))))) (PreH9 : ((Zlength (BlockBytes)) = 64)) (PreH10 : (u8_list_bounded BlockBytes )) (PreH11 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH12 : (i = 0)) (PreH13 : (aligned_4 digest_pre )) (PreH14 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH15 : (aligned_4 count )) (PreH16 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_final_safety_wit_74 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (u8_list_bounded Message )) (PreH4 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH5 : (Tail = (sm3_tail (Message)))) (PreH6 : (0 <= (Zlength (Tail)))) (PreH7 : ((Zlength (Tail)) < 64)) (PreH8 : (BlockBytes = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))))) (PreH9 : ((Zlength (BlockBytes)) = 64)) (PreH10 : (u8_list_bounded BlockBytes )) (PreH11 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH12 : (i = 0)) (PreH13 : (aligned_4 digest_pre )) (PreH14 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH15 : (aligned_4 count )) (PreH16 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sm3_final_safety_wit_75 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (FinalState: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (Tail = (sm3_tail (Message)))) (PreH2 : (0 <= (Zlength (Tail)))) (PreH3 : ((Zlength (Tail)) < 64)) (PreH4 : (FinalState = (sm3_digest_words (Message)))) (PreH5 : ((Zlength (FinalState)) = 8)) (PreH6 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH7 : ((Zlength (BlockBytes)) = 64)) (PreH8 : (u8_list_bounded BlockBytes )) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_byte_prefix digest_pre 32 (@nil Z) )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_sm3_ti )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_final_safety_wit_76 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (Tail = (sm3_tail (Message)))) (PreH2 : (0 <= (Zlength (Tail)))) (PreH3 : ((Zlength (Tail)) < 64)) (PreH4 : (FinalState = (sm3_digest_words (Message)))) (PreH5 : ((Zlength (FinalState)) = 8)) (PreH6 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH7 : ((Zlength (BlockBytes)) = 64)) (PreH8 : (u8_list_bounded BlockBytes )) (PreH9 : (0 <= i)) (PreH10 : (i <= 8)) (PreH11 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH12 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH13 : (u8_list_bounded OutputBytes )) (PreH14 : (aligned_4 digest_pre )) (PreH15 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sm3_final_safety_wit_77 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (24 <= 31) ” 
  &&  “ (0 <= 24) ”
.

Definition sm3_final_safety_wit_78 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
.

Definition sm3_final_safety_wit_79 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
.

Definition sm3_final_safety_wit_80 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (24 <= 31) ” 
  &&  “ (0 <= 24) ”
.

Definition sm3_final_safety_wit_81 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (24 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 24) ”
.

Definition sm3_final_safety_wit_82 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sm3_final_safety_wit_83 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (65280 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65280) ”
.

Definition sm3_final_safety_wit_84 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sm3_final_safety_wit_85 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (16711680 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16711680) ”
.

Definition sm3_final_safety_wit_86 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (24 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 24) ”
.

Definition sm3_final_entail_wit_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (PreH1 : (aligned_4 digest_pre )) ,
  ((( &( "count" ) )) # Ptr  |-> (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((64 + (-8) ) * sizeof(UCHAR))))
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  (store_sm3_ctx ctx_pre Message )
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (aligned_4 digest_pre ) ”
  &&  ((( &( "count" ) )) # Ptr  |-> (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((64 + (-8) ) * sizeof(UCHAR))))
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  (store_sm3_ctx ctx_pre Message )
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_2 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (PreH1 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH2 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH3 : (aligned_4 digest_pre )) ,
  ((( &( "count" ) )) # Ptr  |-> (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((64 + (-8) ) * sizeof(UCHAR))))
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  (store_sm3_ctx ctx_pre Message )
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (aligned_4 digest_pre ) ”
  &&  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Message)))))
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (sm3_tail (Message)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))) )
  **  ((( &( "count" ) )) # Ptr  |-> (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((64 + (-8) ) * sizeof(UCHAR))))
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_3 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (PreH1 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH2 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH3 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH4 : (u8_list_bounded Message )) (PreH5 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH6 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH7 : (aligned_4 digest_pre )) ,
  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Message)))))
  **  (store_byte_prefix &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (sm3_tail (Message)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))) )
  **  ((( &( "count" ) )) # Ptr  |-> (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((64 + (-8) ) * sizeof(UCHAR))))
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (sm3_tail (Message)) ) ” 
  &&  “ ((Zlength ((sm3_tail (Message)))) <= 64) ” 
  &&  “ (0 <= (Zlength ((sm3_tail (Message))))) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) ) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (aligned_4 digest_pre ) ”
  &&  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Message)))) ) (64 - (Zlength ((sm3_tail (Message)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Message)))) (sm3_tail (Message)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Message)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))) )
  **  ((( &( "count" ) )) # Ptr  |-> (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((64 + (-8) ) * sizeof(UCHAR))))
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> 0)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_4 := 
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (PreH1 : (u8_list_bounded (sm3_tail (Message)) )) (PreH2 : ((Zlength ((sm3_tail (Message)))) <= 64)) (PreH3 : (0 <= (Zlength ((sm3_tail (Message)))))) (PreH4 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH5 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (u8_list_bounded Message )) (PreH8 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH9 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH10 : (aligned_4 digest_pre )) ,
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Message)))) ) (64 - (Zlength ((sm3_tail (Message)))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Message)))) (sm3_tail (Message)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength ((sm3_tail (Message)))))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))) )
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  EX (State: (@list Z))  (Tail: (@list Z)) ,
  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (0 = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((64 + (-8) ) * sizeof(UCHAR))) = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength (Tail)) Tail )
  **  (UCharArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength (Tail)) 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
) \/
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (PreH1 : (u8_list_bounded (sm3_tail (Message)) )) (PreH2 : ((Zlength ((sm3_tail (Message)))) <= 64)) (PreH3 : (0 <= (Zlength ((sm3_tail (Message)))))) (PreH4 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH5 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (u8_list_bounded Message )) (PreH8 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH9 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH10 : (aligned_4 digest_pre )) ,
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Message)))) ) (64 - (Zlength ((sm3_tail (Message)))) ) )
  **  (store_sm3_ti )
|--
  “ ((Zlength ((sm3_tail (Message)))) < 64) ”
  &&  (UCharArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Message)))) 64 )
  **  (store_sm3_ti )
).

Definition sm3_final_entail_wit_4_split_goal_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (PreH1 : (u8_list_bounded (sm3_tail (Message)) )) (PreH2 : ((Zlength ((sm3_tail (Message)))) <= 64)) (PreH3 : (0 <= (Zlength ((sm3_tail (Message)))))) (PreH4 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH5 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (u8_list_bounded Message )) (PreH8 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH9 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH10 : (aligned_4 digest_pre )) ,
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Message)))) ) (64 - (Zlength ((sm3_tail (Message)))) ) )
  **  (store_sm3_ti )
|--
  “ ((Zlength ((sm3_tail (Message)))) < 64) ”
.

Definition sm3_final_entail_wit_4_split_goal_spatial := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (PreH1 : (u8_list_bounded (sm3_tail (Message)) )) (PreH2 : ((Zlength ((sm3_tail (Message)))) <= 64)) (PreH3 : (0 <= (Zlength ((sm3_tail (Message)))))) (PreH4 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH5 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (u8_list_bounded Message )) (PreH8 : (aligned_4 (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + 56 ) )) (PreH9 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH10 : (aligned_4 digest_pre )) ,
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail (Message)))) ) (64 - (Zlength ((sm3_tail (Message)))) ) )
  **  (store_sm3_ti )
|--
  (UCharArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail (Message)))) 64 )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_5 := 
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (((Zlength (Tail_2)) + 9 ) <= 64)) (PreH2 : (u8_list_bounded Message )) (PreH3 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH4 : (Tail_2 = (sm3_tail (Message)))) (PreH5 : (0 <= (Zlength (Tail_2)))) (PreH6 : ((Zlength (Tail_2)) < 64)) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) 64 )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State_2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail_2)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  EX (State: (@list Z))  (Tail: (@list Z)) ,
  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) <= 55) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (55 - (Zlength (Tail)) ) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
) \/
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (((Zlength (Tail_2)) + 9 ) <= 64)) (PreH2 : (u8_list_bounded Message )) (PreH3 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH4 : (Tail_2 = (sm3_tail (Message)))) (PreH5 : (0 <= (Zlength (Tail_2)))) (PreH6 : ((Zlength (Tail_2)) < 64)) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) 64 )
  **  (store_sm3_ti )
|--
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength ((sm3_tail (Message)))) + 1 ) (app ((sm3_tail (Message))) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength ((sm3_tail (Message)))) + 1 ) * sizeof(UCHAR))) (55 - (Zlength ((sm3_tail (Message)))) ) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  (store_sm3_ti )
).

Definition sm3_final_entail_wit_5_split_goal_spatial := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (((Zlength (Tail_2)) + 9 ) <= 64)) (PreH2 : (u8_list_bounded Message )) (PreH3 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH4 : (Tail_2 = (sm3_tail (Message)))) (PreH5 : (0 <= (Zlength (Tail_2)))) (PreH6 : ((Zlength (Tail_2)) < 64)) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) 64 )
  **  (store_sm3_ti )
|--
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength ((sm3_tail (Message)))) + 1 ) (app ((sm3_tail (Message))) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength ((sm3_tail (Message)))) + 1 ) * sizeof(UCHAR))) (55 - (Zlength ((sm3_tail (Message)))) ) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_6 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))))) (PreH2 : (u8_list_bounded Message )) (PreH3 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH4 : (Tail = (sm3_tail (Message)))) (PreH5 : (0 <= (Zlength (Tail)))) (PreH6 : ((Zlength (Tail)) <= 55)) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail)) ) - 9 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail)) ) - 9 ))) )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail)) ) - 9 ))) ) ” 
  &&  “ ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail)) ) - 9 ))))) = ((64 - (Zlength (Tail)) ) - 9 )) ” 
  &&  “ (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) <= 55) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ”
  &&  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail)) ) - 9 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail)) ) - 9 ))) )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_7 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail)) ) - 9 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail)) ) - 9 ))))) = ((64 - (Zlength (Tail)) ) - 9 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail = (sm3_tail (Message)))) (PreH7 : (0 <= (Zlength (Tail)))) (PreH8 : ((Zlength (Tail)) <= 55)) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail)) ) - 9 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail)) ) - 9 ))) )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail)) ) - 9 ))) ) ” 
  &&  “ ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail)) ) - 9 ))))) = ((64 - (Zlength (Tail)) ) - 9 )) ” 
  &&  “ (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) <= 55) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ”
  &&  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail)) ) - 9 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail)) ) - 9 ))) )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_8 := 
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (((Zlength (Tail_2)) + 9 ) > 64)) (PreH2 : (u8_list_bounded Message )) (PreH3 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH4 : (Tail_2 = (sm3_tail (Message)))) (PreH5 : (0 <= (Zlength (Tail_2)))) (PreH6 : ((Zlength (Tail_2)) < 64)) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) 64 )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State_2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail_2)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  EX (State: (@list Z))  (Tail: (@list Z)) ,
  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (56 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (63 - (Zlength (Tail)) ) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
) \/
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (((Zlength (Tail_2)) + 9 ) > 64)) (PreH2 : (u8_list_bounded Message )) (PreH3 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH4 : (Tail_2 = (sm3_tail (Message)))) (PreH5 : (0 <= (Zlength (Tail_2)))) (PreH6 : ((Zlength (Tail_2)) < 64)) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) 64 )
  **  (store_sm3_ti )
|--
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength ((sm3_tail (Message)))) + 1 ) (app ((sm3_tail (Message))) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength ((sm3_tail (Message)))) + 1 ) * sizeof(UCHAR))) (63 - (Zlength ((sm3_tail (Message)))) ) )
  **  (store_sm3_ti )
).

Definition sm3_final_entail_wit_8_split_goal_spatial := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (((Zlength (Tail_2)) + 9 ) > 64)) (PreH2 : (u8_list_bounded Message )) (PreH3 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH4 : (Tail_2 = (sm3_tail (Message)))) (PreH5 : (0 <= (Zlength (Tail_2)))) (PreH6 : ((Zlength (Tail_2)) < 64)) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) 64 )
  **  (store_sm3_ti )
|--
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength ((sm3_tail (Message)))) + 1 ) (app ((sm3_tail (Message))) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength ((sm3_tail (Message)))) + 1 ) * sizeof(UCHAR))) (63 - (Zlength ((sm3_tail (Message)))) ) )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_9 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))))) (PreH2 : (u8_list_bounded Message )) (PreH3 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH4 : (Tail = (sm3_tail (Message)))) (PreH5 : (56 <= (Zlength (Tail)))) (PreH6 : ((Zlength (Tail)) < 64)) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH11 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail)) ) - 1 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail)) ) - 1 ))) )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail)) ) - 1 ))) ) ” 
  &&  “ ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail)) ) - 1 ))))) = ((64 - (Zlength (Tail)) ) - 1 )) ” 
  &&  “ (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (56 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ”
  &&  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail)) ) - 1 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail)) ) - 1 ))) )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_10 := 
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))))) = ((64 - (Zlength (Tail_2)) ) - 1 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (56 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) < 64)) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail_2)) ) - 1 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))) )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State_2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail_2)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  EX (State: (@list Z))  (BlockBytes: (@list Z))  (Tail: (@list Z)) ,
  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (56 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (BlockBytes = (app (Tail) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail)) )))))))) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 ) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
) \/
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))))) = ((64 - (Zlength (Tail_2)) ) - 1 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (56 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) < 64)) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail_2)) ) - 1 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 ) ” 
  &&  “ (u8_list_bounded (app (Tail_2) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail_2)) ))))))) ) ” 
  &&  “ ((Zlength ((app (Tail_2) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail_2)) ))))))))) = 64) ”
  &&  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (app ((sm3_tail (Message))) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength ((sm3_tail (Message)))) ))))))) )
  **  (store_sm3_ti )
).

Definition sm3_final_entail_wit_10_split_goal_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))))) = ((64 - (Zlength (Tail_2)) ) - 1 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (56 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) < 64)) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail_2)) ) - 1 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 ) ”
.

Definition sm3_final_entail_wit_10_split_goal_2 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))))) = ((64 - (Zlength (Tail_2)) ) - 1 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (56 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) < 64)) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail_2)) ) - 1 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (app (Tail_2) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail_2)) ))))))) ) ”
.

Definition sm3_final_entail_wit_10_split_goal_3 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))))) = ((64 - (Zlength (Tail_2)) ) - 1 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (56 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) < 64)) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail_2)) ) - 1 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (store_sm3_ti )
|--
  “ ((Zlength ((app (Tail_2) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail_2)) ))))))))) = 64) ”
.

Definition sm3_final_entail_wit_10_split_goal_spatial := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))))) = ((64 - (Zlength (Tail_2)) ) - 1 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (56 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) < 64)) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail_2)) ) - 1 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 1 ))) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (store_sm3_ti )
|--
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (app ((sm3_tail (Message))) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength ((sm3_tail (Message)))) ))))))) )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_11 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (BlockBytes: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (BlockBytes = (app (Tail) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail)) ))))))))) (PreH7 : ((Zlength (BlockBytes)) = 64)) (PreH8 : (u8_list_bounded BlockBytes )) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH14 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (limb_list_bounded SM3_WORD_MODULUS State ) ” 
  &&  “ ((Zlength (State)) = 8) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (56 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (BlockBytes = (app (Tail) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail)) )))))))) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 ) ”
  &&  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_12 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (BlockBytes: (@list Z)) (i: Z) (count: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (u8_list_bounded Message )) (PreH4 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH5 : (Tail = (sm3_tail (Message)))) (PreH6 : (56 <= (Zlength (Tail)))) (PreH7 : ((Zlength (Tail)) < 64)) (PreH8 : (BlockBytes = (app (Tail) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail)) ))))))))) (PreH9 : ((Zlength (BlockBytes)) = 64)) (PreH10 : (u8_list_bounded BlockBytes )) (PreH11 : (i = 0)) (PreH12 : (aligned_4 digest_pre )) (PreH13 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH14 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH15 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH16 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State) (BlockBytes)) )
  **  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes )
  **  (store_sm3_ti )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
|--
  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ ((Zlength (BlockBytes)) = (64 * 1 )) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS State ) ” 
  &&  “ ((Zlength (State)) = 8) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (56 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (BlockBytes = (app (Tail) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail)) )))))))) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 ) ”
  &&  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes )
  **  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State) (BlockBytes)) )
  **  (store_sm3_ti )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
.

Definition sm3_final_entail_wit_13 := 
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (BlockBytes_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded BlockBytes_2 )) (PreH2 : ((Zlength (BlockBytes_2)) = (64 * 1 ))) (PreH3 : (limb_list_bounded SM3_WORD_MODULUS State_2 )) (PreH4 : ((Zlength (State_2)) = 8)) (PreH5 : (u8_list_bounded Message )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (Tail_2 = (sm3_tail (Message)))) (PreH8 : (56 <= (Zlength (Tail_2)))) (PreH9 : ((Zlength (Tail_2)) < 64)) (PreH10 : (BlockBytes_2 = (app (Tail_2) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail_2)) ))))))))) (PreH11 : ((Zlength (BlockBytes_2)) = 64)) (PreH12 : (u8_list_bounded BlockBytes_2 )) (PreH13 : (i = 0)) (PreH14 : (aligned_4 digest_pre )) (PreH15 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH16 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes_2 )
  **  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State_2) (BlockBytes_2)) )
  **  (store_sm3_ti )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail_2)))
  **  (UCharArray.undef_full digest_pre 32 )
|--
  EX (State: (@list Z))  (BlockBytes: (@list Z))  (Tail: (@list Z)) ,
  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (56 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message))))) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) - (Zlength (Tail)) ) * sizeof(UCHAR))) 56 )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
) \/
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (BlockBytes_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded BlockBytes_2 )) (PreH2 : ((Zlength (BlockBytes_2)) = (64 * 1 ))) (PreH3 : (limb_list_bounded SM3_WORD_MODULUS State_2 )) (PreH4 : ((Zlength (State_2)) = 8)) (PreH5 : (u8_list_bounded Message )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (Tail_2 = (sm3_tail (Message)))) (PreH8 : (56 <= (Zlength (Tail_2)))) (PreH9 : ((Zlength (Tail_2)) < 64)) (PreH10 : (BlockBytes_2 = (app (Tail_2) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail_2)) ))))))))) (PreH11 : ((Zlength (BlockBytes_2)) = 64)) (PreH12 : (u8_list_bounded BlockBytes_2 )) (PreH13 : (i = 0)) (PreH14 : (aligned_4 digest_pre )) (PreH15 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH16 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes_2 )
  **  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State_2) (BlockBytes_2)) )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))) ) ” 
  &&  “ ((Zlength ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) = 64) ” 
  &&  “ ((Zlength ((sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) = 8) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))) ) ”
  &&  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength ((sm3_tail (Message)))) - (Zlength ((sm3_tail (Message)))) ) * sizeof(UCHAR))) 56 )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) )
  **  (store_sm3_ti )
).

Definition sm3_final_entail_wit_13_split_goal_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (BlockBytes_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded BlockBytes_2 )) (PreH2 : ((Zlength (BlockBytes_2)) = (64 * 1 ))) (PreH3 : (limb_list_bounded SM3_WORD_MODULUS State_2 )) (PreH4 : ((Zlength (State_2)) = 8)) (PreH5 : (u8_list_bounded Message )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (Tail_2 = (sm3_tail (Message)))) (PreH8 : (56 <= (Zlength (Tail_2)))) (PreH9 : ((Zlength (Tail_2)) < 64)) (PreH10 : (BlockBytes_2 = (app (Tail_2) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail_2)) ))))))))) (PreH11 : ((Zlength (BlockBytes_2)) = 64)) (PreH12 : (u8_list_bounded BlockBytes_2 )) (PreH13 : (i = 0)) (PreH14 : (aligned_4 digest_pre )) (PreH15 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH16 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes_2 )
  **  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State_2) (BlockBytes_2)) )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))) ) ”
.

Definition sm3_final_entail_wit_13_split_goal_2 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (BlockBytes_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded BlockBytes_2 )) (PreH2 : ((Zlength (BlockBytes_2)) = (64 * 1 ))) (PreH3 : (limb_list_bounded SM3_WORD_MODULUS State_2 )) (PreH4 : ((Zlength (State_2)) = 8)) (PreH5 : (u8_list_bounded Message )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (Tail_2 = (sm3_tail (Message)))) (PreH8 : (56 <= (Zlength (Tail_2)))) (PreH9 : ((Zlength (Tail_2)) < 64)) (PreH10 : (BlockBytes_2 = (app (Tail_2) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail_2)) ))))))))) (PreH11 : ((Zlength (BlockBytes_2)) = 64)) (PreH12 : (u8_list_bounded BlockBytes_2 )) (PreH13 : (i = 0)) (PreH14 : (aligned_4 digest_pre )) (PreH15 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH16 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes_2 )
  **  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State_2) (BlockBytes_2)) )
  **  (store_sm3_ti )
|--
  “ ((Zlength ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) = 64) ”
.

Definition sm3_final_entail_wit_13_split_goal_3 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (BlockBytes_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded BlockBytes_2 )) (PreH2 : ((Zlength (BlockBytes_2)) = (64 * 1 ))) (PreH3 : (limb_list_bounded SM3_WORD_MODULUS State_2 )) (PreH4 : ((Zlength (State_2)) = 8)) (PreH5 : (u8_list_bounded Message )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (Tail_2 = (sm3_tail (Message)))) (PreH8 : (56 <= (Zlength (Tail_2)))) (PreH9 : ((Zlength (Tail_2)) < 64)) (PreH10 : (BlockBytes_2 = (app (Tail_2) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail_2)) ))))))))) (PreH11 : ((Zlength (BlockBytes_2)) = 64)) (PreH12 : (u8_list_bounded BlockBytes_2 )) (PreH13 : (i = 0)) (PreH14 : (aligned_4 digest_pre )) (PreH15 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH16 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes_2 )
  **  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State_2) (BlockBytes_2)) )
  **  (store_sm3_ti )
|--
  “ ((Zlength ((sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) = 8) ”
.

Definition sm3_final_entail_wit_13_split_goal_4 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (BlockBytes_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded BlockBytes_2 )) (PreH2 : ((Zlength (BlockBytes_2)) = (64 * 1 ))) (PreH3 : (limb_list_bounded SM3_WORD_MODULUS State_2 )) (PreH4 : ((Zlength (State_2)) = 8)) (PreH5 : (u8_list_bounded Message )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (Tail_2 = (sm3_tail (Message)))) (PreH8 : (56 <= (Zlength (Tail_2)))) (PreH9 : ((Zlength (Tail_2)) < 64)) (PreH10 : (BlockBytes_2 = (app (Tail_2) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail_2)) ))))))))) (PreH11 : ((Zlength (BlockBytes_2)) = 64)) (PreH12 : (u8_list_bounded BlockBytes_2 )) (PreH13 : (i = 0)) (PreH14 : (aligned_4 digest_pre )) (PreH15 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH16 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes_2 )
  **  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State_2) (BlockBytes_2)) )
  **  (store_sm3_ti )
|--
  “ (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))) ) ”
.

Definition sm3_final_entail_wit_13_split_goal_spatial := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (BlockBytes_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded BlockBytes_2 )) (PreH2 : ((Zlength (BlockBytes_2)) = (64 * 1 ))) (PreH3 : (limb_list_bounded SM3_WORD_MODULUS State_2 )) (PreH4 : ((Zlength (State_2)) = 8)) (PreH5 : (u8_list_bounded Message )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (Tail_2 = (sm3_tail (Message)))) (PreH8 : (56 <= (Zlength (Tail_2)))) (PreH9 : ((Zlength (Tail_2)) < 64)) (PreH10 : (BlockBytes_2 = (app (Tail_2) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail_2)) ))))))))) (PreH11 : ((Zlength (BlockBytes_2)) = 64)) (PreH12 : (u8_list_bounded BlockBytes_2 )) (PreH13 : (i = 0)) (PreH14 : (aligned_4 digest_pre )) (PreH15 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH16 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH17 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH18 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes_2 )
  **  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State_2) (BlockBytes_2)) )
  **  (store_sm3_ti )
|--
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength ((sm3_tail (Message)))) - (Zlength ((sm3_tail (Message)))) ) * sizeof(UCHAR))) 56 )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_14 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH2 : (u8_list_bounded Message )) (PreH3 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH4 : (Tail = (sm3_tail (Message)))) (PreH5 : (56 <= (Zlength (Tail)))) (PreH6 : ((Zlength (Tail)) < 64)) (PreH7 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH8 : (i = 0)) (PreH9 : (aligned_4 digest_pre )) (PreH10 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH11 : ((Zlength (BlockBytes)) = 64)) (PreH12 : (u8_list_bounded BlockBytes )) (PreH13 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH14 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 - 8 ) (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) ) ” 
  &&  “ ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))))) = (64 - 8 )) ” 
  &&  “ (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (56 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message))))) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ”
  &&  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 - 8 ) (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_15 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))))) = (64 - 8 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail = (sm3_tail (Message)))) (PreH7 : (56 <= (Zlength (Tail)))) (PreH8 : ((Zlength (Tail)) < 64)) (PreH9 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : ((Zlength (BlockBytes)) = 64)) (PreH14 : (u8_list_bounded BlockBytes )) (PreH15 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH16 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 - 8 ) (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) ) ” 
  &&  “ ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))))) = (64 - 8 )) ” 
  &&  “ (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR)))) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (56 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message))))) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ”
  &&  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 - 8 ) (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_16_1 := 
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))))) = ((64 - (Zlength (Tail_2)) ) - 9 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (0 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) <= 55)) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail_2)) ) - 9 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))) )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State_2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail_2)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  EX (State: (@list Z))  (Prefix56: (@list Z))  (Tail: (@list Z)) ,
  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ ((Zlength (Prefix56)) = 56) ” 
  &&  “ (u8_list_bounded Prefix56 ) ” 
  &&  “ (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message))))))))) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (aligned_4 count ) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
) \/
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))))) = ((64 - (Zlength (Tail_2)) ) - 9 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (0 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) <= 55)) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail_2)) ) - 9 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  (store_sm3_ti )
|--
  “ (aligned_4 count ) ” 
  &&  “ (u8_list_bounded (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))) ) ” 
  &&  “ ((Zlength ((sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) = 56) ” 
  &&  “ (State_2 = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message))))))))) ”
  &&  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))) )
  **  (UIntArray.undef_full count 2 )
  **  (store_sm3_ti )
).

Definition sm3_final_entail_wit_16_1_split_goal_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))))) = ((64 - (Zlength (Tail_2)) ) - 9 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (0 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) <= 55)) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail_2)) ) - 9 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  (store_sm3_ti )
|--
  “ (aligned_4 count ) ”
.

Definition sm3_final_entail_wit_16_1_split_goal_2 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))))) = ((64 - (Zlength (Tail_2)) ) - 9 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (0 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) <= 55)) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail_2)) ) - 9 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))) ) ”
.

Definition sm3_final_entail_wit_16_1_split_goal_3 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))))) = ((64 - (Zlength (Tail_2)) ) - 9 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (0 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) <= 55)) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail_2)) ) - 9 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  (store_sm3_ti )
|--
  “ ((Zlength ((sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) = 56) ”
.

Definition sm3_final_entail_wit_16_1_split_goal_4 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))))) = ((64 - (Zlength (Tail_2)) ) - 9 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (0 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) <= 55)) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail_2)) ) - 9 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  (store_sm3_ti )
|--
  “ (State_2 = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message))))))))) ”
.

Definition sm3_final_entail_wit_16_1_split_goal_spatial := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))))) = ((64 - (Zlength (Tail_2)) ) - 9 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (0 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) <= 55)) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH12 : (State_2 = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail_2)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail_2)) ) - 9 ) (repeat_Z ((unsigned_last_nbits (0) (8))) (((64 - (Zlength (Tail_2)) ) - 9 ))) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail_2)) + 1 ) (app (Tail_2) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  (store_sm3_ti )
|--
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))) )
  **  (UIntArray.undef_full count 2 )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_16_2 := 
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))))) = (64 - 8 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (56 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) < 64)) (PreH9 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : ((Zlength (BlockBytes)) = 64)) (PreH14 : (u8_list_bounded BlockBytes )) (PreH15 : (State_2 = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH16 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 - 8 ) (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State_2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail_2)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  EX (State: (@list Z))  (Prefix56: (@list Z))  (Tail: (@list Z)) ,
  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ ((Zlength (Prefix56)) = 56) ” 
  &&  “ (u8_list_bounded Prefix56 ) ” 
  &&  “ (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message))))))))) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (aligned_4 count ) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
) \/
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))))) = (64 - 8 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (56 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) < 64)) (PreH9 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : ((Zlength (BlockBytes)) = 64)) (PreH14 : (u8_list_bounded BlockBytes )) (PreH15 : (State_2 = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH16 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 - 8 ) (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  (store_sm3_ti )
|--
  “ (aligned_4 count ) ” 
  &&  “ (u8_list_bounded (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))) ) ” 
  &&  “ ((Zlength ((sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) = 56) ”
  &&  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))) )
  **  (UIntArray.undef_full count 2 )
  **  (store_sm3_ti )
).

Definition sm3_final_entail_wit_16_2_split_goal_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))))) = (64 - 8 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (56 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) < 64)) (PreH9 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : ((Zlength (BlockBytes)) = 64)) (PreH14 : (u8_list_bounded BlockBytes )) (PreH15 : (State_2 = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH16 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 - 8 ) (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  (store_sm3_ti )
|--
  “ (aligned_4 count ) ”
.

Definition sm3_final_entail_wit_16_2_split_goal_2 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))))) = (64 - 8 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (56 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) < 64)) (PreH9 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : ((Zlength (BlockBytes)) = 64)) (PreH14 : (u8_list_bounded BlockBytes )) (PreH15 : (State_2 = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH16 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 - 8 ) (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))) ) ”
.

Definition sm3_final_entail_wit_16_2_split_goal_3 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))))) = (64 - 8 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (56 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) < 64)) (PreH9 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : ((Zlength (BlockBytes)) = 64)) (PreH14 : (u8_list_bounded BlockBytes )) (PreH15 : (State_2 = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH16 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 - 8 ) (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  (store_sm3_ti )
|--
  “ ((Zlength ((sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) = 56) ”
.

Definition sm3_final_entail_wit_16_2_split_goal_spatial := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (BlockBytes: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (retval: Z) (PreH1 : (u8_list_bounded (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )) (PreH2 : ((Zlength ((repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))))) = (64 - 8 ))) (PreH3 : (retval = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))))) (PreH4 : (u8_list_bounded Message )) (PreH5 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH6 : (Tail_2 = (sm3_tail (Message)))) (PreH7 : (56 <= (Zlength (Tail_2)))) (PreH8 : ((Zlength (Tail_2)) < 64)) (PreH9 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : ((Zlength (BlockBytes)) = 64)) (PreH14 : (u8_list_bounded BlockBytes )) (PreH15 : (State_2 = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH16 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 - 8 ) (repeat_Z ((unsigned_last_nbits (0) (8))) ((64 - 8 ))) )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  (store_sm3_ti )
|--
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))) )
  **  (UIntArray.undef_full count 2 )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_17 := 
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Prefix56: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail_2 = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail_2)))) (PreH5 : ((Zlength (Tail_2)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State_2 = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (1 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))))
  **  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State_2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail_2)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  EX (State: (@list Z))  (BlockBytes: (@list Z))  (Tail: (@list Z)) ,
  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (BlockBytes = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message))))) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message))))))))) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (aligned_4 count ) ” 
  &&  “ (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 ) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
) \/
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Prefix56: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))) <= UINT_MAX)) (PreH2 : ((Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))) <= UINT_MAX)) (PreH3 : ((Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))) >= 0)) (PreH4 : ((Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))) >= 0)) (PreH5 : (u8_list_bounded Message )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (Tail_2 = (sm3_tail (Message)))) (PreH8 : (0 <= (Zlength (Tail_2)))) (PreH9 : ((Zlength (Tail_2)) < 64)) (PreH10 : ((Zlength (Prefix56)) = 56)) (PreH11 : (u8_list_bounded Prefix56 )) (PreH12 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH13 : (State_2 = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH14 : (i = 0)) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH17 : (aligned_4 count )) ,
  (((count + (1 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))))
  **  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 ) ” 
  &&  “ (u8_list_bounded (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))) ) ” 
  &&  “ ((Zlength ((sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))))) = 64) ”
  &&  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))) )
  **  (store_sm3_ti )
).

Definition sm3_final_entail_wit_17_split_goal_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Prefix56: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))) <= UINT_MAX)) (PreH2 : ((Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))) <= UINT_MAX)) (PreH3 : ((Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))) >= 0)) (PreH4 : ((Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))) >= 0)) (PreH5 : (u8_list_bounded Message )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (Tail_2 = (sm3_tail (Message)))) (PreH8 : (0 <= (Zlength (Tail_2)))) (PreH9 : ((Zlength (Tail_2)) < 64)) (PreH10 : ((Zlength (Prefix56)) = 56)) (PreH11 : (u8_list_bounded Prefix56 )) (PreH12 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH13 : (State_2 = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH14 : (i = 0)) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH17 : (aligned_4 count )) ,
  (((count + (1 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))))
  **  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 ) ”
.

Definition sm3_final_entail_wit_17_split_goal_2 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Prefix56: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))) <= UINT_MAX)) (PreH2 : ((Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))) <= UINT_MAX)) (PreH3 : ((Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))) >= 0)) (PreH4 : ((Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))) >= 0)) (PreH5 : (u8_list_bounded Message )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (Tail_2 = (sm3_tail (Message)))) (PreH8 : (0 <= (Zlength (Tail_2)))) (PreH9 : ((Zlength (Tail_2)) < 64)) (PreH10 : ((Zlength (Prefix56)) = 56)) (PreH11 : (u8_list_bounded Prefix56 )) (PreH12 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH13 : (State_2 = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH14 : (i = 0)) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH17 : (aligned_4 count )) ,
  (((count + (1 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))))
  **  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))) ) ”
.

Definition sm3_final_entail_wit_17_split_goal_3 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Prefix56: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))) <= UINT_MAX)) (PreH2 : ((Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))) <= UINT_MAX)) (PreH3 : ((Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))) >= 0)) (PreH4 : ((Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))) >= 0)) (PreH5 : (u8_list_bounded Message )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (Tail_2 = (sm3_tail (Message)))) (PreH8 : (0 <= (Zlength (Tail_2)))) (PreH9 : ((Zlength (Tail_2)) < 64)) (PreH10 : ((Zlength (Prefix56)) = 56)) (PreH11 : (u8_list_bounded Prefix56 )) (PreH12 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH13 : (State_2 = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH14 : (i = 0)) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH17 : (aligned_4 count )) ,
  (((count + (1 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))))
  **  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (store_sm3_ti )
|--
  “ ((Zlength ((sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))))) = 64) ”
.

Definition sm3_final_entail_wit_17_split_goal_spatial := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State_2: (@list Z)) (Prefix56: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))) <= UINT_MAX)) (PreH2 : ((Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))) <= UINT_MAX)) (PreH3 : ((Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))) >= 0)) (PreH4 : ((Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))) >= 0)) (PreH5 : (u8_list_bounded Message )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (Tail_2 = (sm3_tail (Message)))) (PreH8 : (0 <= (Zlength (Tail_2)))) (PreH9 : ((Zlength (Tail_2)) < 64)) (PreH10 : ((Zlength (Prefix56)) = 56)) (PreH11 : (u8_list_bounded Prefix56 )) (PreH12 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH13 : (State_2 = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH14 : (i = 0)) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH17 : (aligned_4 count )) ,
  (((count + (1 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24) (Z.land (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 65280)) (Z.land (Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl ((Zlength (Message)) ÷ 64 ) 9)) (64)) + (unsigned_last_nbits ((Z.shiftl (Zlength (Tail_2)) 3)) (64)) )) (32)) 24)) (32))))
  **  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (store_sm3_ti )
|--
  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))) )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_18 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (BlockBytes = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))))) (PreH7 : ((Zlength (BlockBytes)) = 64)) (PreH8 : (u8_list_bounded BlockBytes )) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) (PreH14 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (limb_list_bounded SM3_WORD_MODULUS State ) ” 
  &&  “ ((Zlength (State)) = 8) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (BlockBytes = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message))))) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message))))))))) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (aligned_4 count ) ” 
  &&  “ (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 ) ”
  &&  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_19 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (u8_list_bounded Message )) (PreH4 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH5 : (Tail = (sm3_tail (Message)))) (PreH6 : (0 <= (Zlength (Tail)))) (PreH7 : ((Zlength (Tail)) < 64)) (PreH8 : (BlockBytes = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))))) (PreH9 : ((Zlength (BlockBytes)) = 64)) (PreH10 : (u8_list_bounded BlockBytes )) (PreH11 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH12 : (i = 0)) (PreH13 : (aligned_4 digest_pre )) (PreH14 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH15 : (aligned_4 count )) (PreH16 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State) (BlockBytes)) )
  **  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes )
  **  (store_sm3_ti )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
|--
  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ ((Zlength (BlockBytes)) = (64 * 1 )) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS State ) ” 
  &&  “ ((Zlength (State)) = 8) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (BlockBytes = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message))))) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message))))))))) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (aligned_4 count ) ” 
  &&  “ (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 ) ”
  &&  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes )
  **  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State) (BlockBytes)) )
  **  (store_sm3_ti )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
.

Definition sm3_final_entail_wit_20 := 
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded BlockBytes_2 )) (PreH2 : ((Zlength (BlockBytes_2)) = (64 * 1 ))) (PreH3 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH4 : ((Zlength (State)) = 8)) (PreH5 : (u8_list_bounded Message )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (Tail_2 = (sm3_tail (Message)))) (PreH8 : (0 <= (Zlength (Tail_2)))) (PreH9 : ((Zlength (Tail_2)) < 64)) (PreH10 : (BlockBytes_2 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))))) (PreH11 : ((Zlength (BlockBytes_2)) = 64)) (PreH12 : (u8_list_bounded BlockBytes_2 )) (PreH13 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH14 : (i = 0)) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH17 : (aligned_4 count )) (PreH18 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes_2 )
  **  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State) (BlockBytes_2)) )
  **  (store_sm3_ti )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail_2)))
  **  (UCharArray.undef_full digest_pre 32 )
|--
  EX (BlockBytes: (@list Z))  (FinalState: (@list Z))  (Tail: (@list Z)) ,
  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (FinalState = (sm3_digest_words (Message))) ” 
  &&  “ ((Zlength (FinalState)) = 8) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS FinalState ) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
) \/
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded BlockBytes_2 )) (PreH2 : ((Zlength (BlockBytes_2)) = (64 * 1 ))) (PreH3 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH4 : ((Zlength (State)) = 8)) (PreH5 : (u8_list_bounded Message )) (PreH6 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH7 : (Tail_2 = (sm3_tail (Message)))) (PreH8 : (0 <= (Zlength (Tail_2)))) (PreH9 : ((Zlength (Tail_2)) < 64)) (PreH10 : (BlockBytes_2 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))))) (PreH11 : ((Zlength (BlockBytes_2)) = 64)) (PreH12 : (u8_list_bounded BlockBytes_2 )) (PreH13 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH14 : (i = 0)) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH17 : (aligned_4 count )) (PreH18 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes_2 )
  **  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 (sm3_compress_bytes (State) (BlockBytes_2)) )
  **  (store_sm3_ti )
|--
  EX (BlockBytes: (@list Z)) ,
  “ (limb_list_bounded SM3_WORD_MODULUS (sm3_digest_words (Message)) ) ” 
  &&  “ ((Zlength ((sm3_digest_words (Message)))) = 8) ” 
  &&  “ ((Zlength (Tail_2)) = (Zlength ((sm3_tail (Message))))) ” 
  &&  “ ((Zlength (Tail_2)) = (Zlength ((sm3_tail (Message))))) ” 
  &&  “ (0 <= (Zlength ((sm3_tail (Message))))) ” 
  &&  “ ((Zlength ((sm3_tail (Message)))) < 64) ” 
  &&  “ ((Zlength ((sm3_digest_words (Message)))) = 8) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS (sm3_digest_words (Message)) ) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ”
  &&  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_digest_words (Message)) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  (store_sm3_ti )
).

Definition sm3_final_entail_wit_21 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (FinalState: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (Tail = (sm3_tail (Message)))) (PreH2 : (0 <= (Zlength (Tail)))) (PreH3 : ((Zlength (Tail)) < 64)) (PreH4 : (FinalState = (sm3_digest_words (Message)))) (PreH5 : ((Zlength (FinalState)) = 8)) (PreH6 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH7 : ((Zlength (BlockBytes)) = 64)) (PreH8 : (u8_list_bounded BlockBytes )) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (FinalState = (sm3_digest_words (Message))) ” 
  &&  “ ((Zlength (FinalState)) = 8) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS FinalState ) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ”
  &&  (store_byte_prefix digest_pre 32 (@nil Z) )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_22 := 
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (FinalState_2: (@list Z)) (BlockBytes_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (Tail_2 = (sm3_tail (Message)))) (PreH2 : (0 <= (Zlength (Tail_2)))) (PreH3 : ((Zlength (Tail_2)) < 64)) (PreH4 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH5 : ((Zlength (FinalState_2)) = 8)) (PreH6 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH7 : ((Zlength (BlockBytes_2)) = 64)) (PreH8 : (u8_list_bounded BlockBytes_2 )) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_byte_prefix digest_pre 32 (@nil Z) )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState_2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes_2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail_2)))
  **  (store_sm3_ti )
|--
  EX (OutputBytes: (@list Z))  (BlockBytes: (@list Z))  (FinalState: (@list Z))  (Tail: (@list Z)) ,
  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (FinalState = (sm3_digest_words (Message))) ” 
  &&  “ ((Zlength (FinalState)) = 8) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS FinalState ) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ (OutputBytes = (sublist (0) ((4 * 0 )) ((sm3_digest_bytes (Message))))) ” 
  &&  “ ((Zlength (OutputBytes)) = (4 * 0 )) ” 
  &&  “ (u8_list_bounded OutputBytes ) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
) \/
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (FinalState_2: (@list Z)) (BlockBytes_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (Tail_2 = (sm3_tail (Message)))) (PreH2 : (0 <= (Zlength (Tail_2)))) (PreH3 : ((Zlength (Tail_2)) < 64)) (PreH4 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH5 : ((Zlength (FinalState_2)) = 8)) (PreH6 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH7 : ((Zlength (BlockBytes_2)) = 64)) (PreH8 : (u8_list_bounded BlockBytes_2 )) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  TT && emp 
|--
  “ (u8_list_bounded (sublist (0) ((4 * 0 )) ((sm3_digest_bytes (Message)))) ) ” 
  &&  “ ((Zlength ((sublist (0) ((4 * 0 )) ((sm3_digest_bytes (Message)))))) = (4 * 0 )) ” 
  &&  “ ((@nil Z) = (sublist (0) ((4 * 0 )) ((sm3_digest_bytes (Message))))) ”
  &&  emp
).

Definition sm3_final_entail_wit_22_split_goal_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (FinalState_2: (@list Z)) (BlockBytes_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (Tail_2 = (sm3_tail (Message)))) (PreH2 : (0 <= (Zlength (Tail_2)))) (PreH3 : ((Zlength (Tail_2)) < 64)) (PreH4 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH5 : ((Zlength (FinalState_2)) = 8)) (PreH6 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH7 : ((Zlength (BlockBytes_2)) = 64)) (PreH8 : (u8_list_bounded BlockBytes_2 )) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (u8_list_bounded (sublist (0) ((4 * 0 )) ((sm3_digest_bytes (Message)))) )
.

Definition sm3_final_entail_wit_22_split_goal_2 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (FinalState_2: (@list Z)) (BlockBytes_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (Tail_2 = (sm3_tail (Message)))) (PreH2 : (0 <= (Zlength (Tail_2)))) (PreH3 : ((Zlength (Tail_2)) < 64)) (PreH4 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH5 : ((Zlength (FinalState_2)) = 8)) (PreH6 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH7 : ((Zlength (BlockBytes_2)) = 64)) (PreH8 : (u8_list_bounded BlockBytes_2 )) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  ((Zlength ((sublist (0) ((4 * 0 )) ((sm3_digest_bytes (Message)))))) = (4 * 0 ))
.

Definition sm3_final_entail_wit_22_split_goal_3 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (FinalState_2: (@list Z)) (BlockBytes_2: (@list Z)) (Tail_2: (@list Z)) (i: Z) (count: Z) (PreH1 : (Tail_2 = (sm3_tail (Message)))) (PreH2 : (0 <= (Zlength (Tail_2)))) (PreH3 : ((Zlength (Tail_2)) < 64)) (PreH4 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH5 : ((Zlength (FinalState_2)) = 8)) (PreH6 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH7 : ((Zlength (BlockBytes_2)) = 64)) (PreH8 : (u8_list_bounded BlockBytes_2 )) (PreH9 : (i = 0)) (PreH10 : (aligned_4 digest_pre )) (PreH11 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  ((@nil Z) = (sublist (0) ((4 * 0 )) ((sm3_digest_bytes (Message)))))
.

Definition sm3_final_entail_wit_23 := 
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes_2: (@list Z)) (i: Z) (BlockBytes_2: (@list Z)) (FinalState_2: (@list Z)) (Tail_2: (@list Z)) (word_bytes: (@list Z)) (PreH1 : ((u8_list_value (word_bytes)) = (Z.lor (Z.lor (Z.lor (Z.shiftr (Znth (i) (FinalState_2) (0)) 24) (Z.land (Z.shiftr (Znth (i) (FinalState_2) (0)) 8) 65280)) (Z.land (Z.shiftl (Znth (i) (FinalState_2) (0)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Znth (i) (FinalState_2) (0)) 24)) (32))))) (PreH2 : (u8_list_bounded word_bytes )) (PreH3 : ((Zlength (word_bytes)) = 4)) (PreH4 : (aligned_4 digest_pre )) (PreH5 : (u8_list_bounded OutputBytes_2 )) (PreH6 : (((Zlength (OutputBytes_2)) + 4 ) <= 32)) (PreH7 : (0 <= (Zlength (OutputBytes_2)))) (PreH8 : (i < 8)) (PreH9 : (Tail_2 = (sm3_tail (Message)))) (PreH10 : (0 <= (Zlength (Tail_2)))) (PreH11 : ((Zlength (Tail_2)) < 64)) (PreH12 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH13 : ((Zlength (FinalState_2)) = 8)) (PreH14 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH15 : ((Zlength (BlockBytes_2)) = 64)) (PreH16 : (u8_list_bounded BlockBytes_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= 8)) (PreH19 : (OutputBytes_2 = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH20 : ((Zlength (OutputBytes_2)) = (4 * i ))) (PreH21 : (u8_list_bounded OutputBytes_2 )) (PreH22 : (aligned_4 digest_pre )) (PreH23 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_byte_prefix digest_pre 32 (app (OutputBytes_2) (word_bytes)) )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState_2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes_2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail_2)))
  **  (store_sm3_ti )
|--
  EX (OutputBytes: (@list Z))  (BlockBytes: (@list Z))  (FinalState: (@list Z))  (Tail: (@list Z)) ,
  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (FinalState = (sm3_digest_words (Message))) ” 
  &&  “ ((Zlength (FinalState)) = 8) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS FinalState ) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (OutputBytes = (sublist (0) ((4 * (i + 1 ) )) ((sm3_digest_bytes (Message))))) ” 
  &&  “ ((Zlength (OutputBytes)) = (4 * (i + 1 ) )) ” 
  &&  “ (u8_list_bounded OutputBytes ) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
) \/
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes_2: (@list Z)) (i: Z) (BlockBytes_2: (@list Z)) (FinalState_2: (@list Z)) (Tail_2: (@list Z)) (word_bytes: (@list Z)) (PreH1 : ((u8_list_value (word_bytes)) = (Z.lor (Z.lor (Z.lor (Z.shiftr (Znth (i) (FinalState_2) (0)) 24) (Z.land (Z.shiftr (Znth (i) (FinalState_2) (0)) 8) 65280)) (Z.land (Z.shiftl (Znth (i) (FinalState_2) (0)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Znth (i) (FinalState_2) (0)) 24)) (32))))) (PreH2 : (u8_list_bounded word_bytes )) (PreH3 : ((Zlength (word_bytes)) = 4)) (PreH4 : (aligned_4 digest_pre )) (PreH5 : (u8_list_bounded OutputBytes_2 )) (PreH6 : (((Zlength (OutputBytes_2)) + 4 ) <= 32)) (PreH7 : (0 <= (Zlength (OutputBytes_2)))) (PreH8 : (i < 8)) (PreH9 : (Tail_2 = (sm3_tail (Message)))) (PreH10 : (0 <= (Zlength (Tail_2)))) (PreH11 : ((Zlength (Tail_2)) < 64)) (PreH12 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH13 : ((Zlength (FinalState_2)) = 8)) (PreH14 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH15 : ((Zlength (BlockBytes_2)) = 64)) (PreH16 : (u8_list_bounded BlockBytes_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= 8)) (PreH19 : (OutputBytes_2 = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH20 : ((Zlength (OutputBytes_2)) = (4 * i ))) (PreH21 : (u8_list_bounded OutputBytes_2 )) (PreH22 : (aligned_4 digest_pre )) (PreH23 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  TT && emp 
|--
  “ (u8_list_bounded (sublist (0) ((4 * (i + 1 ) )) ((sm3_digest_bytes (Message)))) ) ” 
  &&  “ ((Zlength ((sublist (0) ((4 * (i + 1 ) )) ((sm3_digest_bytes (Message)))))) = (4 * (i + 1 ) )) ” 
  &&  “ ((app (OutputBytes_2) (word_bytes)) = (sublist (0) ((4 * (i + 1 ) )) ((sm3_digest_bytes (Message))))) ”
  &&  emp
).

Definition sm3_final_entail_wit_23_split_goal_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes_2: (@list Z)) (i: Z) (BlockBytes_2: (@list Z)) (FinalState_2: (@list Z)) (Tail_2: (@list Z)) (word_bytes: (@list Z)) (PreH1 : ((u8_list_value (word_bytes)) = (Z.lor (Z.lor (Z.lor (Z.shiftr (Znth (i) (FinalState_2) (0)) 24) (Z.land (Z.shiftr (Znth (i) (FinalState_2) (0)) 8) 65280)) (Z.land (Z.shiftl (Znth (i) (FinalState_2) (0)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Znth (i) (FinalState_2) (0)) 24)) (32))))) (PreH2 : (u8_list_bounded word_bytes )) (PreH3 : ((Zlength (word_bytes)) = 4)) (PreH4 : (aligned_4 digest_pre )) (PreH5 : (u8_list_bounded OutputBytes_2 )) (PreH6 : (((Zlength (OutputBytes_2)) + 4 ) <= 32)) (PreH7 : (0 <= (Zlength (OutputBytes_2)))) (PreH8 : (i < 8)) (PreH9 : (Tail_2 = (sm3_tail (Message)))) (PreH10 : (0 <= (Zlength (Tail_2)))) (PreH11 : ((Zlength (Tail_2)) < 64)) (PreH12 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH13 : ((Zlength (FinalState_2)) = 8)) (PreH14 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH15 : ((Zlength (BlockBytes_2)) = 64)) (PreH16 : (u8_list_bounded BlockBytes_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= 8)) (PreH19 : (OutputBytes_2 = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH20 : ((Zlength (OutputBytes_2)) = (4 * i ))) (PreH21 : (u8_list_bounded OutputBytes_2 )) (PreH22 : (aligned_4 digest_pre )) (PreH23 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (u8_list_bounded (sublist (0) ((4 * (i + 1 ) )) ((sm3_digest_bytes (Message)))) )
.

Definition sm3_final_entail_wit_23_split_goal_2 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes_2: (@list Z)) (i: Z) (BlockBytes_2: (@list Z)) (FinalState_2: (@list Z)) (Tail_2: (@list Z)) (word_bytes: (@list Z)) (PreH1 : ((u8_list_value (word_bytes)) = (Z.lor (Z.lor (Z.lor (Z.shiftr (Znth (i) (FinalState_2) (0)) 24) (Z.land (Z.shiftr (Znth (i) (FinalState_2) (0)) 8) 65280)) (Z.land (Z.shiftl (Znth (i) (FinalState_2) (0)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Znth (i) (FinalState_2) (0)) 24)) (32))))) (PreH2 : (u8_list_bounded word_bytes )) (PreH3 : ((Zlength (word_bytes)) = 4)) (PreH4 : (aligned_4 digest_pre )) (PreH5 : (u8_list_bounded OutputBytes_2 )) (PreH6 : (((Zlength (OutputBytes_2)) + 4 ) <= 32)) (PreH7 : (0 <= (Zlength (OutputBytes_2)))) (PreH8 : (i < 8)) (PreH9 : (Tail_2 = (sm3_tail (Message)))) (PreH10 : (0 <= (Zlength (Tail_2)))) (PreH11 : ((Zlength (Tail_2)) < 64)) (PreH12 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH13 : ((Zlength (FinalState_2)) = 8)) (PreH14 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH15 : ((Zlength (BlockBytes_2)) = 64)) (PreH16 : (u8_list_bounded BlockBytes_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= 8)) (PreH19 : (OutputBytes_2 = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH20 : ((Zlength (OutputBytes_2)) = (4 * i ))) (PreH21 : (u8_list_bounded OutputBytes_2 )) (PreH22 : (aligned_4 digest_pre )) (PreH23 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  ((Zlength ((sublist (0) ((4 * (i + 1 ) )) ((sm3_digest_bytes (Message)))))) = (4 * (i + 1 ) ))
.

Definition sm3_final_entail_wit_23_split_goal_3 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes_2: (@list Z)) (i: Z) (BlockBytes_2: (@list Z)) (FinalState_2: (@list Z)) (Tail_2: (@list Z)) (word_bytes: (@list Z)) (PreH1 : ((u8_list_value (word_bytes)) = (Z.lor (Z.lor (Z.lor (Z.shiftr (Znth (i) (FinalState_2) (0)) 24) (Z.land (Z.shiftr (Znth (i) (FinalState_2) (0)) 8) 65280)) (Z.land (Z.shiftl (Znth (i) (FinalState_2) (0)) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Znth (i) (FinalState_2) (0)) 24)) (32))))) (PreH2 : (u8_list_bounded word_bytes )) (PreH3 : ((Zlength (word_bytes)) = 4)) (PreH4 : (aligned_4 digest_pre )) (PreH5 : (u8_list_bounded OutputBytes_2 )) (PreH6 : (((Zlength (OutputBytes_2)) + 4 ) <= 32)) (PreH7 : (0 <= (Zlength (OutputBytes_2)))) (PreH8 : (i < 8)) (PreH9 : (Tail_2 = (sm3_tail (Message)))) (PreH10 : (0 <= (Zlength (Tail_2)))) (PreH11 : ((Zlength (Tail_2)) < 64)) (PreH12 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH13 : ((Zlength (FinalState_2)) = 8)) (PreH14 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH15 : ((Zlength (BlockBytes_2)) = 64)) (PreH16 : (u8_list_bounded BlockBytes_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= 8)) (PreH19 : (OutputBytes_2 = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH20 : ((Zlength (OutputBytes_2)) = (4 * i ))) (PreH21 : (u8_list_bounded OutputBytes_2 )) (PreH22 : (aligned_4 digest_pre )) (PreH23 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  ((app (OutputBytes_2) (word_bytes)) = (sublist (0) ((4 * (i + 1 ) )) ((sm3_digest_bytes (Message)))))
.

Definition sm3_final_entail_wit_24 := 
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes_2: (@list Z)) (FinalState_2: (@list Z)) (Tail_2: (@list Z)) (PreH1 : (i >= 8)) (PreH2 : (Tail_2 = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail_2)))) (PreH4 : ((Zlength (Tail_2)) < 64)) (PreH5 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState_2)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH8 : ((Zlength (BlockBytes_2)) = 64)) (PreH9 : (u8_list_bounded BlockBytes_2 )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState_2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes_2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail_2)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  EX (BlockBytes: (@list Z))  (FinalState: (@list Z))  (Tail: (@list Z)) ,
  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (FinalState = (sm3_digest_words (Message))) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (i = 8) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ”
  &&  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_bytes digest_pre 32 (sm3_digest_bytes (Message)) )
  **  (store_sm3_ti )
) \/
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes_2: (@list Z)) (FinalState_2: (@list Z)) (Tail_2: (@list Z)) (PreH1 : (i >= 8)) (PreH2 : (Tail_2 = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail_2)))) (PreH4 : ((Zlength (Tail_2)) < 64)) (PreH5 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState_2)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH8 : ((Zlength (BlockBytes_2)) = 64)) (PreH9 : (u8_list_bounded BlockBytes_2 )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ ((Zlength ((sm3_digest_bytes (Message)))) = 32) ” 
  &&  “ (u8_list_bounded (sm3_digest_bytes (Message)) ) ”
  &&  (UCharArray.full digest_pre 32 (sm3_digest_bytes (Message)) )
  **  (store_sm3_ti )
).

Definition sm3_final_entail_wit_24_split_goal_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes_2: (@list Z)) (FinalState_2: (@list Z)) (Tail_2: (@list Z)) (PreH1 : (i >= 8)) (PreH2 : (Tail_2 = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail_2)))) (PreH4 : ((Zlength (Tail_2)) < 64)) (PreH5 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState_2)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH8 : ((Zlength (BlockBytes_2)) = 64)) (PreH9 : (u8_list_bounded BlockBytes_2 )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ ((Zlength ((sm3_digest_bytes (Message)))) = 32) ”
.

Definition sm3_final_entail_wit_24_split_goal_2 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes_2: (@list Z)) (FinalState_2: (@list Z)) (Tail_2: (@list Z)) (PreH1 : (i >= 8)) (PreH2 : (Tail_2 = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail_2)))) (PreH4 : ((Zlength (Tail_2)) < 64)) (PreH5 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState_2)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH8 : ((Zlength (BlockBytes_2)) = 64)) (PreH9 : (u8_list_bounded BlockBytes_2 )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded (sm3_digest_bytes (Message)) ) ”
.

Definition sm3_final_entail_wit_24_split_goal_spatial := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes_2: (@list Z)) (FinalState_2: (@list Z)) (Tail_2: (@list Z)) (PreH1 : (i >= 8)) (PreH2 : (Tail_2 = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail_2)))) (PreH4 : ((Zlength (Tail_2)) < 64)) (PreH5 : (FinalState_2 = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState_2)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState_2 )) (PreH8 : ((Zlength (BlockBytes_2)) = 64)) (PreH9 : (u8_list_bounded BlockBytes_2 )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  (UCharArray.full digest_pre 32 (sm3_digest_bytes (Message)) )
  **  (store_sm3_ti )
.

Definition sm3_final_entail_wit_25 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (FinalState: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (Tail = (sm3_tail (Message)))) (PreH2 : (FinalState = (sm3_digest_words (Message)))) (PreH3 : ((Zlength (BlockBytes)) = 64)) (PreH4 : (u8_list_bounded BlockBytes )) (PreH5 : (i = 8)) (PreH6 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_bytes digest_pre 32 (sm3_digest_bytes (Message)) )
  **  (store_sm3_ti )
|--
  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (FinalState = (sm3_digest_words (Message))) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (i = 8) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ”
  &&  (sm3_ctx_full_shape ctx_pre )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_bytes digest_pre 32 (sm3_digest_bytes (Message)) )
  **  (store_sm3_ti )
.

Definition sm3_final_return_wit_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (FinalState: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (Tail = (sm3_tail (Message)))) (PreH2 : (FinalState = (sm3_digest_words (Message)))) (PreH3 : ((Zlength (BlockBytes)) = 64)) (PreH4 : (u8_list_bounded BlockBytes )) (PreH5 : (i = 8)) (PreH6 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (sm3_ctx_full_shape ctx_pre )
  **  (store_bytes digest_pre 32 (sm3_digest_bytes (Message)) )
  **  (store_sm3_ti )
|--
  (sm3_ctx_full_shape ctx_pre )
  **  (store_bytes digest_pre 32 (sm3_digest_bytes (Message)) )
  **  (store_sm3_ti )
.

Definition sm3_final_partial_solve_wit_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength (Tail)) Tail )
  **  (UCharArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength (Tail)) 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ”
  &&  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + ((Zlength (Tail)) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) 64 )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength (Tail)) Tail )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_partial_solve_wit_2_pure := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) <= 55)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (55 - (Zlength (Tail)) ) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= ((64 - (Zlength (Tail)) ) - 9 )) ”
.

Definition sm3_final_partial_solve_wit_2_aux := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) <= 55)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (55 - (Zlength (Tail)) ) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= ((64 - (Zlength (Tail)) ) - 9 )) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) <= 55) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ”
  &&  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail)) ) - 9 ) )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_partial_solve_wit_2 := sm3_final_partial_solve_wit_2_pure -> sm3_final_partial_solve_wit_2_aux.

Definition sm3_final_partial_solve_wit_3_pure := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (63 - (Zlength (Tail)) ) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= ((64 - (Zlength (Tail)) ) - 1 )) ”
.

Definition sm3_final_partial_solve_wit_3_aux := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (i = 0)) (PreH7 : (aligned_4 digest_pre )) (PreH8 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH10 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) (63 - (Zlength (Tail)) ) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= ((64 - (Zlength (Tail)) ) - 1 )) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (56 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ”
  &&  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) + 1 ) * sizeof(UCHAR))) ((64 - (Zlength (Tail)) ) - 1 ) )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ((Zlength (Tail)) + 1 ) (app (Tail) ((cons (128) ((@nil Z))))) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_partial_solve_wit_3 := sm3_final_partial_solve_wit_3_pure -> sm3_final_partial_solve_wit_3_aux.

Definition sm3_final_partial_solve_wit_4_pure := 
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (BlockBytes: (@list Z)) (i: Z) (count: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (u8_list_bounded Message )) (PreH4 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH5 : (Tail = (sm3_tail (Message)))) (PreH6 : (56 <= (Zlength (Tail)))) (PreH7 : ((Zlength (Tail)) < 64)) (PreH8 : (BlockBytes = (app (Tail) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail)) ))))))))) (PreH9 : ((Zlength (BlockBytes)) = 64)) (PreH10 : (u8_list_bounded BlockBytes )) (PreH11 : (i = 0)) (PreH12 : (aligned_4 digest_pre )) (PreH13 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH14 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH15 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH16 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) 1 ) ”
) \/
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (BlockBytes: (@list Z)) (i: Z) (count: Z) (PreH1 : ((Zlength (Tail)) <= UINT64_MAX)) (PreH2 : (((Zlength (Message)) ÷ 64 ) <= UINT64_MAX)) (PreH3 : ((Zlength (Tail)) >= 0)) (PreH4 : (((Zlength (Message)) ÷ 64 ) >= 0)) (PreH5 : (i <= UINT_MAX)) (PreH6 : (i >= 0)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH8 : ((Zlength (State)) = 8)) (PreH9 : (u8_list_bounded Message )) (PreH10 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH11 : (Tail = (sm3_tail (Message)))) (PreH12 : (56 <= (Zlength (Tail)))) (PreH13 : ((Zlength (Tail)) < 64)) (PreH14 : (BlockBytes = (app (Tail) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail)) ))))))))) (PreH15 : ((Zlength (BlockBytes)) = 64)) (PreH16 : (u8_list_bounded BlockBytes )) (PreH17 : (i = 0)) (PreH18 : (aligned_4 digest_pre )) (PreH19 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH20 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH21 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH22 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) 1 ) ”
).

Definition sm3_final_partial_solve_wit_4_pure_split_goal_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (BlockBytes: (@list Z)) (i: Z) (count: Z) (PreH1 : ((Zlength (Tail)) <= UINT64_MAX)) (PreH2 : (((Zlength (Message)) ÷ 64 ) <= UINT64_MAX)) (PreH3 : ((Zlength (Tail)) >= 0)) (PreH4 : (((Zlength (Message)) ÷ 64 ) >= 0)) (PreH5 : (i <= UINT_MAX)) (PreH6 : (i >= 0)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH8 : ((Zlength (State)) = 8)) (PreH9 : (u8_list_bounded Message )) (PreH10 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH11 : (Tail = (sm3_tail (Message)))) (PreH12 : (56 <= (Zlength (Tail)))) (PreH13 : ((Zlength (Tail)) < 64)) (PreH14 : (BlockBytes = (app (Tail) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail)) ))))))))) (PreH15 : ((Zlength (BlockBytes)) = 64)) (PreH16 : (u8_list_bounded BlockBytes )) (PreH17 : (i = 0)) (PreH18 : (aligned_4 digest_pre )) (PreH19 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH20 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH21 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH22 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) 1 ) ”
.

Definition sm3_final_partial_solve_wit_4_aux := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Tail: (@list Z)) (BlockBytes: (@list Z)) (i: Z) (count: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (u8_list_bounded Message )) (PreH4 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH5 : (Tail = (sm3_tail (Message)))) (PreH6 : (56 <= (Zlength (Tail)))) (PreH7 : ((Zlength (Tail)) < 64)) (PreH8 : (BlockBytes = (app (Tail) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail)) ))))))))) (PreH9 : ((Zlength (BlockBytes)) = 64)) (PreH10 : (u8_list_bounded BlockBytes )) (PreH11 : (i = 0)) (PreH12 : (aligned_4 digest_pre )) (PreH13 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH14 : (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message)))))) (PreH15 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) (PreH16 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) 1 ) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS State ) ” 
  &&  “ ((Zlength (State)) = 8) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (56 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (BlockBytes = (app (Tail) ((app ((cons (128) ((@nil Z)))) ((repeat_Z (0) ((63 - (Zlength (Tail)) )))))))) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes (Message))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ” 
  &&  “ (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 ) ”
  &&  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 State )
  **  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes )
  **  (store_sm3_ti )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
.

Definition sm3_final_partial_solve_wit_4 := sm3_final_partial_solve_wit_4_pure -> sm3_final_partial_solve_wit_4_aux.

Definition sm3_final_partial_solve_wit_5_pure := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : ((Zlength (BlockBytes)) = 64)) (PreH11 : (u8_list_bounded BlockBytes )) (PreH12 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) - (Zlength (Tail)) ) * sizeof(UCHAR))) 56 )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= (64 - 8 )) ”
.

Definition sm3_final_partial_solve_wit_5_aux := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (56 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))) (PreH7 : (i = 0)) (PreH8 : (aligned_4 digest_pre )) (PreH9 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH10 : ((Zlength (BlockBytes)) = 64)) (PreH11 : (u8_list_bounded BlockBytes )) (PreH12 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes)))))) (PreH13 : (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") )) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (((Zlength (Tail)) - (Zlength (Tail)) ) * sizeof(UCHAR))) 56 )
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (0 <= (64 - 8 )) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (56 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (BlockBytes = (sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message))))) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) (BlockBytes))))) ” 
  &&  “ (aligned_4 &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") ) ”
  &&  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 - 8 ) )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))) 8 (sublist (56) (64) (BlockBytes)) )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_partial_solve_wit_5 := sm3_final_partial_solve_wit_5_pure -> sm3_final_partial_solve_wit_5_aux.

Definition sm3_final_partial_solve_wit_6 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  (UIntArray.undef_full count 2 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ ((Zlength (Prefix56)) = 56) ” 
  &&  “ (u8_list_bounded Prefix56 ) ” 
  &&  “ (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message))))))))) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (aligned_4 count ) ”
  &&  (((count + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg count 1 2 )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_partial_solve_wit_7 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (Prefix56: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (u8_list_bounded Message )) (PreH2 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH3 : (Tail = (sm3_tail (Message)))) (PreH4 : (0 <= (Zlength (Tail)))) (PreH5 : ((Zlength (Tail)) < 64)) (PreH6 : ((Zlength (Prefix56)) = 56)) (PreH7 : (u8_list_bounded Prefix56 )) (PreH8 : (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message)))))) (PreH9 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH10 : (i = 0)) (PreH11 : (aligned_4 digest_pre )) (PreH12 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH13 : (aligned_4 count )) ,
  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (UIntArray.undef_seg count 1 2 )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ ((Zlength (Prefix56)) = 56) ” 
  &&  “ (u8_list_bounded Prefix56 ) ” 
  &&  “ (Prefix56 = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) (((Zlength ((sm3_final_bytes (Message)))) - 8 )) ((sm3_final_bytes (Message))))) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message))))))))) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (aligned_4 count ) ”
  &&  (((count + (1 * sizeof(UINT)))) # UInt  |->_)
  **  (((count + (0 * sizeof(UINT)))) # UInt  |-> (Z.lor (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32)) (Z.land (Z.shiftr (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 65280)) (Z.land (Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 8) 16711680)) (unsigned_last_nbits ((Z.shiftl (Z.shiftr ((Zlength (Message)) ÷ 64 ) 23) 24)) (32))))
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 56 Prefix56 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_final_partial_solve_wit_8_pure := 
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (u8_list_bounded Message )) (PreH4 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH5 : (Tail = (sm3_tail (Message)))) (PreH6 : (0 <= (Zlength (Tail)))) (PreH7 : ((Zlength (Tail)) < 64)) (PreH8 : (BlockBytes = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))))) (PreH9 : ((Zlength (BlockBytes)) = 64)) (PreH10 : (u8_list_bounded BlockBytes )) (PreH11 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH12 : (i = 0)) (PreH13 : (aligned_4 digest_pre )) (PreH14 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH15 : (aligned_4 count )) (PreH16 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) 1 ) ”
) \/
(
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : ((Zlength (Tail)) <= UINT64_MAX)) (PreH2 : (((Zlength (Message)) ÷ 64 ) <= UINT64_MAX)) (PreH3 : ((Zlength (Tail)) >= 0)) (PreH4 : (((Zlength (Message)) ÷ 64 ) >= 0)) (PreH5 : (i <= UINT_MAX)) (PreH6 : (i >= 0)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH8 : ((Zlength (State)) = 8)) (PreH9 : (u8_list_bounded Message )) (PreH10 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH11 : (Tail = (sm3_tail (Message)))) (PreH12 : (0 <= (Zlength (Tail)))) (PreH13 : ((Zlength (Tail)) < 64)) (PreH14 : (BlockBytes = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))))) (PreH15 : ((Zlength (BlockBytes)) = 64)) (PreH16 : (u8_list_bounded BlockBytes )) (PreH17 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH18 : (i = 0)) (PreH19 : (aligned_4 digest_pre )) (PreH20 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH21 : (aligned_4 count )) (PreH22 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) 1 ) ”
).

Definition sm3_final_partial_solve_wit_8_pure_split_goal_1 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : ((Zlength (Tail)) <= UINT64_MAX)) (PreH2 : (((Zlength (Message)) ÷ 64 ) <= UINT64_MAX)) (PreH3 : ((Zlength (Tail)) >= 0)) (PreH4 : (((Zlength (Message)) ÷ 64 ) >= 0)) (PreH5 : (i <= UINT_MAX)) (PreH6 : (i >= 0)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH8 : ((Zlength (State)) = 8)) (PreH9 : (u8_list_bounded Message )) (PreH10 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH11 : (Tail = (sm3_tail (Message)))) (PreH12 : (0 <= (Zlength (Tail)))) (PreH13 : ((Zlength (Tail)) < 64)) (PreH14 : (BlockBytes = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))))) (PreH15 : ((Zlength (BlockBytes)) = 64)) (PreH16 : (u8_list_bounded BlockBytes )) (PreH17 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH18 : (i = 0)) (PreH19 : (aligned_4 digest_pre )) (PreH20 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH21 : (aligned_4 count )) (PreH22 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((( &( "digest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  ((( &( "pdigest" ) )) # Ptr  |-> digest_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) 1 ) ”
.

Definition sm3_final_partial_solve_wit_8_aux := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (State: (@list Z)) (BlockBytes: (@list Z)) (Tail: (@list Z)) (i: Z) (count: Z) (PreH1 : (limb_list_bounded SM3_WORD_MODULUS State )) (PreH2 : ((Zlength (State)) = 8)) (PreH3 : (u8_list_bounded Message )) (PreH4 : ((Zlength (Message)) < SM3_MAX_BYTES)) (PreH5 : (Tail = (sm3_tail (Message)))) (PreH6 : (0 <= (Zlength (Tail)))) (PreH7 : ((Zlength (Tail)) < 64)) (PreH8 : (BlockBytes = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message)))))) (PreH9 : ((Zlength (BlockBytes)) = 64)) (PreH10 : (u8_list_bounded BlockBytes )) (PreH11 : (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message)))))))))) (PreH12 : (i = 0)) (PreH13 : (aligned_4 digest_pre )) (PreH14 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) (PreH15 : (aligned_4 count )) (PreH16 : (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 )) ,
  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 State )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_compress_input_aligned (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) 1 ) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS State ) ” 
  &&  “ ((Zlength (State)) = 8) ” 
  &&  “ (u8_list_bounded Message ) ” 
  &&  “ ((Zlength (Message)) < SM3_MAX_BYTES) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (BlockBytes = (sublist (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((Zlength ((sm3_final_bytes (Message))))) ((sm3_final_bytes (Message))))) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (State = (sm3_compress_bytes (SM3_IV) ((app ((sm3_full_bytes (Message))) ((sublist (0) (((Zlength ((sm3_final_bytes (Message)))) - 64 )) ((sm3_final_bytes (Message))))))))) ” 
  &&  “ (i = 0) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ” 
  &&  “ (aligned_4 count ) ” 
  &&  “ (sm3_compress_input_aligned &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 1 ) ”
  &&  (store_u32_words (&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT))) 8 State )
  **  (store_bytes (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (0 * sizeof(UCHAR))) (64 * 1 ) BlockBytes )
  **  (store_sm3_ti )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (UCharArray.undef_full digest_pre 32 )
.

Definition sm3_final_partial_solve_wit_8 := sm3_final_partial_solve_wit_8_pure -> sm3_final_partial_solve_wit_8_aux.

Definition sm3_final_partial_solve_wit_9 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (i < 8) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (FinalState = (sm3_digest_words (Message))) ” 
  &&  “ ((Zlength (FinalState)) = 8) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS FinalState ) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message))))) ” 
  &&  “ ((Zlength (OutputBytes)) = (4 * i )) ” 
  &&  “ (u8_list_bounded OutputBytes ) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ”
  &&  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (i * sizeof(UINT)))) # UInt  |-> (Znth (i) (FinalState) (0)))
  **  (store_u32_words_missing_i &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 i FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
.

Definition sm3_final_partial_solve_wit_10 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (i < 8) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (FinalState = (sm3_digest_words (Message))) ” 
  &&  “ ((Zlength (FinalState)) = 8) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS FinalState ) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message))))) ” 
  &&  “ ((Zlength (OutputBytes)) = (4 * i )) ” 
  &&  “ (u8_list_bounded OutputBytes ) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ”
  &&  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (i * sizeof(UINT)))) # UInt  |-> (Znth (i) (FinalState) (0)))
  **  (store_u32_words_missing_i &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 i FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
.

Definition sm3_final_partial_solve_wit_11 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (i < 8) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (FinalState = (sm3_digest_words (Message))) ” 
  &&  “ ((Zlength (FinalState)) = 8) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS FinalState ) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message))))) ” 
  &&  “ ((Zlength (OutputBytes)) = (4 * i )) ” 
  &&  “ (u8_list_bounded OutputBytes ) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ”
  &&  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (i * sizeof(UINT)))) # UInt  |-> (Znth (i) (FinalState) (0)))
  **  (store_u32_words_missing_i &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 i FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
.

Definition sm3_final_partial_solve_wit_12 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (i < 8) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (FinalState = (sm3_digest_words (Message))) ” 
  &&  “ ((Zlength (FinalState)) = 8) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS FinalState ) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message))))) ” 
  &&  “ ((Zlength (OutputBytes)) = (4 * i )) ” 
  &&  “ (u8_list_bounded OutputBytes ) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ”
  &&  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (i * sizeof(UINT)))) # UInt  |-> (Znth (i) (FinalState) (0)))
  **  (store_u32_words_missing_i &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 i FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
.

Definition sm3_final_partial_solve_wit_13 := 
forall (digest_pre: Z) (ctx_pre: Z) (Message: (@list Z)) (count: Z) (OutputBytes: (@list Z)) (i: Z) (BlockBytes: (@list Z)) (FinalState: (@list Z)) (Tail: (@list Z)) (PreH1 : (i < 8)) (PreH2 : (Tail = (sm3_tail (Message)))) (PreH3 : (0 <= (Zlength (Tail)))) (PreH4 : ((Zlength (Tail)) < 64)) (PreH5 : (FinalState = (sm3_digest_words (Message)))) (PreH6 : ((Zlength (FinalState)) = 8)) (PreH7 : (limb_list_bounded SM3_WORD_MODULUS FinalState )) (PreH8 : ((Zlength (BlockBytes)) = 64)) (PreH9 : (u8_list_bounded BlockBytes )) (PreH10 : (0 <= i)) (PreH11 : (i <= 8)) (PreH12 : (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message)))))) (PreH13 : ((Zlength (OutputBytes)) = (4 * i ))) (PreH14 : (u8_list_bounded OutputBytes )) (PreH15 : (aligned_4 digest_pre )) (PreH16 : (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR))))) ,
  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_byte_prefix digest_pre 32 OutputBytes )
  **  (store_sm3_ti )
|--
  “ (aligned_4 digest_pre ) ” 
  &&  “ (((digest_pre + (i * sizeof(UINT))) - digest_pre ) = (Zlength (OutputBytes))) ” 
  &&  “ (u8_list_bounded OutputBytes ) ” 
  &&  “ (((Zlength (OutputBytes)) + 4 ) <= 32) ” 
  &&  “ (0 <= (Zlength (OutputBytes))) ” 
  &&  “ (i < 8) ” 
  &&  “ (Tail = (sm3_tail (Message))) ” 
  &&  “ (0 <= (Zlength (Tail))) ” 
  &&  “ ((Zlength (Tail)) < 64) ” 
  &&  “ (FinalState = (sm3_digest_words (Message))) ” 
  &&  “ ((Zlength (FinalState)) = 8) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS FinalState ) ” 
  &&  “ ((Zlength (BlockBytes)) = 64) ” 
  &&  “ (u8_list_bounded BlockBytes ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (OutputBytes = (sublist (0) ((4 * i )) ((sm3_digest_bytes (Message))))) ” 
  &&  “ ((Zlength (OutputBytes)) = (4 * i )) ” 
  &&  “ (u8_list_bounded OutputBytes ) ” 
  &&  “ (aligned_4 digest_pre ) ” 
  &&  “ (count = (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (56 * sizeof(UCHAR)))) ”
  &&  (((digest_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UCharArray.undef_full (digest_pre + ((i + 1 ) * sizeof(UINT))) ((32 - (Zlength (OutputBytes)) ) - 4 ) )
  **  (UCharArray.full digest_pre (Zlength (OutputBytes)) OutputBytes )
  **  (store_u32_words &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 FinalState )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> ((Zlength (Message)) ÷ 64 ))
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 BlockBytes )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> (Zlength (Tail)))
  **  (store_sm3_ti )
.

Module Type VC_Correct.

Include byte_memory_views_Strategy_Correct.
Include sm3_ctx_views_Strategy_Correct.
Include sm3_word_views_Strategy_Correct.
Include sm3_streaming_memory_views_Strategy_Correct.

Axiom proof_of_sm3_final_safety_wit_1 : sm3_final_safety_wit_1.
Axiom proof_of_sm3_final_safety_wit_2 : sm3_final_safety_wit_2.
Axiom proof_of_sm3_final_safety_wit_3 : sm3_final_safety_wit_3.
Axiom proof_of_sm3_final_safety_wit_4 : sm3_final_safety_wit_4.
Axiom proof_of_sm3_final_safety_wit_5 : sm3_final_safety_wit_5.
Axiom proof_of_sm3_final_safety_wit_6 : sm3_final_safety_wit_6.
Axiom proof_of_sm3_final_safety_wit_7 : sm3_final_safety_wit_7.
Axiom proof_of_sm3_final_safety_wit_8 : sm3_final_safety_wit_8.
Axiom proof_of_sm3_final_safety_wit_9 : sm3_final_safety_wit_9.
Axiom proof_of_sm3_final_safety_wit_10 : sm3_final_safety_wit_10.
Axiom proof_of_sm3_final_safety_wit_11 : sm3_final_safety_wit_11.
Axiom proof_of_sm3_final_safety_wit_12 : sm3_final_safety_wit_12.
Axiom proof_of_sm3_final_safety_wit_13 : sm3_final_safety_wit_13.
Axiom proof_of_sm3_final_safety_wit_14 : sm3_final_safety_wit_14.
Axiom proof_of_sm3_final_safety_wit_15 : sm3_final_safety_wit_15.
Axiom proof_of_sm3_final_safety_wit_16 : sm3_final_safety_wit_16.
Axiom proof_of_sm3_final_safety_wit_17 : sm3_final_safety_wit_17.
Axiom proof_of_sm3_final_safety_wit_18 : sm3_final_safety_wit_18.
Axiom proof_of_sm3_final_safety_wit_19 : sm3_final_safety_wit_19.
Axiom proof_of_sm3_final_safety_wit_20 : sm3_final_safety_wit_20.
Axiom proof_of_sm3_final_safety_wit_21 : sm3_final_safety_wit_21.
Axiom proof_of_sm3_final_safety_wit_22 : sm3_final_safety_wit_22.
Axiom proof_of_sm3_final_safety_wit_23 : sm3_final_safety_wit_23.
Axiom proof_of_sm3_final_safety_wit_24 : sm3_final_safety_wit_24.
Axiom proof_of_sm3_final_safety_wit_25 : sm3_final_safety_wit_25.
Axiom proof_of_sm3_final_safety_wit_26 : sm3_final_safety_wit_26.
Axiom proof_of_sm3_final_safety_wit_27 : sm3_final_safety_wit_27.
Axiom proof_of_sm3_final_safety_wit_28 : sm3_final_safety_wit_28.
Axiom proof_of_sm3_final_safety_wit_29 : sm3_final_safety_wit_29.
Axiom proof_of_sm3_final_safety_wit_30 : sm3_final_safety_wit_30.
Axiom proof_of_sm3_final_safety_wit_31 : sm3_final_safety_wit_31.
Axiom proof_of_sm3_final_safety_wit_32 : sm3_final_safety_wit_32.
Axiom proof_of_sm3_final_safety_wit_33 : sm3_final_safety_wit_33.
Axiom proof_of_sm3_final_safety_wit_34 : sm3_final_safety_wit_34.
Axiom proof_of_sm3_final_safety_wit_35 : sm3_final_safety_wit_35.
Axiom proof_of_sm3_final_safety_wit_36 : sm3_final_safety_wit_36.
Axiom proof_of_sm3_final_safety_wit_37 : sm3_final_safety_wit_37.
Axiom proof_of_sm3_final_safety_wit_38 : sm3_final_safety_wit_38.
Axiom proof_of_sm3_final_safety_wit_39 : sm3_final_safety_wit_39.
Axiom proof_of_sm3_final_safety_wit_40 : sm3_final_safety_wit_40.
Axiom proof_of_sm3_final_safety_wit_41 : sm3_final_safety_wit_41.
Axiom proof_of_sm3_final_safety_wit_42 : sm3_final_safety_wit_42.
Axiom proof_of_sm3_final_safety_wit_43 : sm3_final_safety_wit_43.
Axiom proof_of_sm3_final_safety_wit_44 : sm3_final_safety_wit_44.
Axiom proof_of_sm3_final_safety_wit_45 : sm3_final_safety_wit_45.
Axiom proof_of_sm3_final_safety_wit_46 : sm3_final_safety_wit_46.
Axiom proof_of_sm3_final_safety_wit_47 : sm3_final_safety_wit_47.
Axiom proof_of_sm3_final_safety_wit_48 : sm3_final_safety_wit_48.
Axiom proof_of_sm3_final_safety_wit_49 : sm3_final_safety_wit_49.
Axiom proof_of_sm3_final_safety_wit_50 : sm3_final_safety_wit_50.
Axiom proof_of_sm3_final_safety_wit_51 : sm3_final_safety_wit_51.
Axiom proof_of_sm3_final_safety_wit_52 : sm3_final_safety_wit_52.
Axiom proof_of_sm3_final_safety_wit_53 : sm3_final_safety_wit_53.
Axiom proof_of_sm3_final_safety_wit_54 : sm3_final_safety_wit_54.
Axiom proof_of_sm3_final_safety_wit_55 : sm3_final_safety_wit_55.
Axiom proof_of_sm3_final_safety_wit_56 : sm3_final_safety_wit_56.
Axiom proof_of_sm3_final_safety_wit_57 : sm3_final_safety_wit_57.
Axiom proof_of_sm3_final_safety_wit_58 : sm3_final_safety_wit_58.
Axiom proof_of_sm3_final_safety_wit_59 : sm3_final_safety_wit_59.
Axiom proof_of_sm3_final_safety_wit_60 : sm3_final_safety_wit_60.
Axiom proof_of_sm3_final_safety_wit_61 : sm3_final_safety_wit_61.
Axiom proof_of_sm3_final_safety_wit_62 : sm3_final_safety_wit_62.
Axiom proof_of_sm3_final_safety_wit_63 : sm3_final_safety_wit_63.
Axiom proof_of_sm3_final_safety_wit_64 : sm3_final_safety_wit_64.
Axiom proof_of_sm3_final_safety_wit_65 : sm3_final_safety_wit_65.
Axiom proof_of_sm3_final_safety_wit_66 : sm3_final_safety_wit_66.
Axiom proof_of_sm3_final_safety_wit_67 : sm3_final_safety_wit_67.
Axiom proof_of_sm3_final_safety_wit_68 : sm3_final_safety_wit_68.
Axiom proof_of_sm3_final_safety_wit_69 : sm3_final_safety_wit_69.
Axiom proof_of_sm3_final_safety_wit_70 : sm3_final_safety_wit_70.
Axiom proof_of_sm3_final_safety_wit_71 : sm3_final_safety_wit_71.
Axiom proof_of_sm3_final_safety_wit_72 : sm3_final_safety_wit_72.
Axiom proof_of_sm3_final_safety_wit_73 : sm3_final_safety_wit_73.
Axiom proof_of_sm3_final_safety_wit_74 : sm3_final_safety_wit_74.
Axiom proof_of_sm3_final_safety_wit_75 : sm3_final_safety_wit_75.
Axiom proof_of_sm3_final_safety_wit_76 : sm3_final_safety_wit_76.
Axiom proof_of_sm3_final_safety_wit_77 : sm3_final_safety_wit_77.
Axiom proof_of_sm3_final_safety_wit_78 : sm3_final_safety_wit_78.
Axiom proof_of_sm3_final_safety_wit_79 : sm3_final_safety_wit_79.
Axiom proof_of_sm3_final_safety_wit_80 : sm3_final_safety_wit_80.
Axiom proof_of_sm3_final_safety_wit_81 : sm3_final_safety_wit_81.
Axiom proof_of_sm3_final_safety_wit_82 : sm3_final_safety_wit_82.
Axiom proof_of_sm3_final_safety_wit_83 : sm3_final_safety_wit_83.
Axiom proof_of_sm3_final_safety_wit_84 : sm3_final_safety_wit_84.
Axiom proof_of_sm3_final_safety_wit_85 : sm3_final_safety_wit_85.
Axiom proof_of_sm3_final_safety_wit_86 : sm3_final_safety_wit_86.
Axiom proof_of_sm3_final_entail_wit_1 : sm3_final_entail_wit_1.
Axiom proof_of_sm3_final_entail_wit_2 : sm3_final_entail_wit_2.
Axiom proof_of_sm3_final_entail_wit_3 : sm3_final_entail_wit_3.
Axiom proof_of_sm3_final_entail_wit_4 : sm3_final_entail_wit_4.
Axiom proof_of_sm3_final_entail_wit_5 : sm3_final_entail_wit_5.
Axiom proof_of_sm3_final_entail_wit_6 : sm3_final_entail_wit_6.
Axiom proof_of_sm3_final_entail_wit_7 : sm3_final_entail_wit_7.
Axiom proof_of_sm3_final_entail_wit_8 : sm3_final_entail_wit_8.
Axiom proof_of_sm3_final_entail_wit_9 : sm3_final_entail_wit_9.
Axiom proof_of_sm3_final_entail_wit_10 : sm3_final_entail_wit_10.
Axiom proof_of_sm3_final_entail_wit_11 : sm3_final_entail_wit_11.
Axiom proof_of_sm3_final_entail_wit_12 : sm3_final_entail_wit_12.
Axiom proof_of_sm3_final_entail_wit_13 : sm3_final_entail_wit_13.
Axiom proof_of_sm3_final_entail_wit_14 : sm3_final_entail_wit_14.
Axiom proof_of_sm3_final_entail_wit_15 : sm3_final_entail_wit_15.
Axiom proof_of_sm3_final_entail_wit_16_1 : sm3_final_entail_wit_16_1.
Axiom proof_of_sm3_final_entail_wit_16_2 : sm3_final_entail_wit_16_2.
Axiom proof_of_sm3_final_entail_wit_17 : sm3_final_entail_wit_17.
Axiom proof_of_sm3_final_entail_wit_18 : sm3_final_entail_wit_18.
Axiom proof_of_sm3_final_entail_wit_19 : sm3_final_entail_wit_19.
Axiom proof_of_sm3_final_entail_wit_20 : sm3_final_entail_wit_20.
Axiom proof_of_sm3_final_entail_wit_21 : sm3_final_entail_wit_21.
Axiom proof_of_sm3_final_entail_wit_22 : sm3_final_entail_wit_22.
Axiom proof_of_sm3_final_entail_wit_23 : sm3_final_entail_wit_23.
Axiom proof_of_sm3_final_entail_wit_24 : sm3_final_entail_wit_24.
Axiom proof_of_sm3_final_entail_wit_25 : sm3_final_entail_wit_25.
Axiom proof_of_sm3_final_return_wit_1 : sm3_final_return_wit_1.
Axiom proof_of_sm3_final_partial_solve_wit_1 : sm3_final_partial_solve_wit_1.
Axiom proof_of_sm3_final_partial_solve_wit_2_pure : sm3_final_partial_solve_wit_2_pure.
Axiom proof_of_sm3_final_partial_solve_wit_2 : sm3_final_partial_solve_wit_2.
Axiom proof_of_sm3_final_partial_solve_wit_3_pure : sm3_final_partial_solve_wit_3_pure.
Axiom proof_of_sm3_final_partial_solve_wit_3 : sm3_final_partial_solve_wit_3.
Axiom proof_of_sm3_final_partial_solve_wit_4_pure : sm3_final_partial_solve_wit_4_pure.
Axiom proof_of_sm3_final_partial_solve_wit_4 : sm3_final_partial_solve_wit_4.
Axiom proof_of_sm3_final_partial_solve_wit_5_pure : sm3_final_partial_solve_wit_5_pure.
Axiom proof_of_sm3_final_partial_solve_wit_5 : sm3_final_partial_solve_wit_5.
Axiom proof_of_sm3_final_partial_solve_wit_6 : sm3_final_partial_solve_wit_6.
Axiom proof_of_sm3_final_partial_solve_wit_7 : sm3_final_partial_solve_wit_7.
Axiom proof_of_sm3_final_partial_solve_wit_8_pure : sm3_final_partial_solve_wit_8_pure.
Axiom proof_of_sm3_final_partial_solve_wit_8 : sm3_final_partial_solve_wit_8.
Axiom proof_of_sm3_final_partial_solve_wit_9 : sm3_final_partial_solve_wit_9.
Axiom proof_of_sm3_final_partial_solve_wit_10 : sm3_final_partial_solve_wit_10.
Axiom proof_of_sm3_final_partial_solve_wit_11 : sm3_final_partial_solve_wit_11.
Axiom proof_of_sm3_final_partial_solve_wit_12 : sm3_final_partial_solve_wit_12.
Axiom proof_of_sm3_final_partial_solve_wit_13 : sm3_final_partial_solve_wit_13.

End VC_Correct.
