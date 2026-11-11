Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition sm3_ctx_views_strategy1 :=
  forall (ctx : Z) (required_ctx : Z) (message : (@list Z)),
    TT &&
    (“ (ctx = required_ctx) ”) &&
    emp **
    ((store_sm3_ctx ctx message))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (required_message : (@list Z)),
      TT &&
      (“ (message = required_message) ”) &&
      emp -*
      TT &&
      emp **
      ((store_sm3_ctx required_ctx required_message))
      ).

Definition sm3_ctx_views_strategy10 :=
  forall (ctx : Z) (required_ctx : Z),
    TT &&
    (“ (ctx = required_ctx) ”) &&
    emp **
    ((undef_sm3_ctx ctx))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((undef_sm3_ctx required_ctx))
    ).

Definition sm3_ctx_views_strategy13 :=
  forall (ctx : Z) (required_ctx : Z),
    TT &&
    (“ (ctx = required_ctx) ”) &&
    emp **
    ((UndefStructPred_SM3_CTX ctx))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((undef_sm3_ctx required_ctx))
    ).

Definition sm3_ctx_views_strategy20 :=
  forall (ctx : Z) (required_ctx : Z),
    TT &&
    (“ (ctx = required_ctx) ”) &&
    emp **
    ((sm3_ctx_full_shape ctx))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((sm3_ctx_full_shape required_ctx))
    ).

Definition sm3_ctx_views_strategy22 :=
  forall (ctx : Z) (required_ctx : Z) (value : Record_SM3_CTX),
    TT &&
    (“ (ctx = required_ctx) ”) &&
    emp **
    ((StructPred_SM3_CTX ctx value))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((sm3_ctx_full_shape required_ctx))
    ).

Definition sm3_ctx_views_strategy2 :=
  forall (ctx : Z) (message : (@list Z)),
    TT &&
    emp **
    ((store_sm3_ctx ctx message))
    |--
    (
    TT &&
    (“ (u8_list_bounded message) ”) &&
    (“ (Z.lt (@Zlength Z message) ( SM3_MAX_BYTES)) ”) &&
    (“ (aligned_4 &( ((ctx)) # "_SM3_CTX" ->ₛ "block")) ”) &&
    (“ (aligned_4 (Z.add &( ((ctx)) # "_SM3_CTX" ->ₛ "block") 56)) ”) &&
    emp **
    ((store_u32_words &( ((ctx)) # "_SM3_CTX" ->ₛ "digest") 8 ( sm3_compress_bytes ( SM3_IV) ( sm3_full_bytes message)))) **
    ((poly_store FET_uint64 &( ((ctx)) # "_SM3_CTX" ->ₛ "nblocks") (Z.div (@Zlength Z message) 64))) **
    ((store_byte_prefix &( ((ctx)) # "_SM3_CTX" ->ₛ "block") 64 ( sm3_tail message))) **
    ((poly_store FET_uint64 &( ((ctx)) # "_SM3_CTX" ->ₛ "num") (@Zlength Z ( sm3_tail message))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm3_ctx_views_strategy4 :=
  forall (ctx : Z) (message : (@list Z)),
    TT &&
    emp **
    ((store_sm3_ctx ctx message))
    |--
    (
    TT &&
    (“ (aligned_4 &( ((ctx)) # "_SM3_CTX" ->ₛ "block")) ”) &&
    emp **
    ((store_sm3_ctx ctx message))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm3_ctx_views_strategy5 :=
  forall (ctx : Z) (message : (@list Z)),
    TT &&
    emp **
    ((store_sm3_ctx ctx message))
    |--
    (
    TT &&
    (“ (aligned_4 (Z.add &( ((ctx)) # "_SM3_CTX" ->ₛ "block") 56)) ”) &&
    emp **
    ((store_sm3_ctx ctx message))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm3_ctx_views_strategy11 :=
  forall (ctx : Z),
    TT &&
    emp **
    ((undef_sm3_ctx ctx))
    |--
    (
    TT &&
    emp **
    ((UIntArray.undef_full &( ((ctx)) # "_SM3_CTX" ->ₛ "digest") 8)) **
    ((poly_undef_store FET_uint64 &( ((ctx)) # "_SM3_CTX" ->ₛ "nblocks"))) **
    ((UCharArray.undef_full &( ((ctx)) # "_SM3_CTX" ->ₛ "block") 64)) **
    ((poly_undef_store FET_uint64 &( ((ctx)) # "_SM3_CTX" ->ₛ "num")))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm3_ctx_views_strategy21 :=
  forall (block_bytes : (@list Z)) (digest_words : (@list Z)) (nblocks : Z) (num : Z) (ctx : Z),
    TT &&
    emp **
    ((store_u32_words &( ((ctx)) # "_SM3_CTX" ->ₛ "digest") 8 digest_words)) **
    ((poly_store FET_uint64 &( ((ctx)) # "_SM3_CTX" ->ₛ "nblocks") nblocks)) **
    ((UCharArray.full &( ((ctx)) # "_SM3_CTX" ->ₛ "block") 64 block_bytes)) **
    ((poly_store FET_uint64 &( ((ctx)) # "_SM3_CTX" ->ₛ "num") num))
    |--
    (
    TT &&
    emp **
    ((sm3_ctx_full_shape ctx))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm3_ctx_views_strategy3 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (message : (@list Z)) (ctx : Z),
    TT &&
    (“ (u8_list_bounded message) ”) &&
    (“ (Z.lt (@Zlength Z message) ( SM3_MAX_BYTES)) ”) &&
    emp **
    ((store_u32_words &( ((ctx)) # "_SM3_CTX" ->ₛ "digest") 8 ( sm3_compress_bytes ( SM3_IV) ( sm3_full_bytes message)))) **
    ((poly_store FET_uint64 &( ((ctx)) # "_SM3_CTX" ->ₛ "nblocks") (Z.div (@Zlength Z message) 64))) **
    ((store_byte_prefix &( ((ctx)) # "_SM3_CTX" ->ₛ "block") 64 ( sm3_tail message))) **
    ((poly_store FET_uint64 &( ((ctx)) # "_SM3_CTX" ->ₛ "num") (@Zlength Z ( sm3_tail message)))) -*
    TT &&
    emp **
    ((store_sm3_ctx ctx message))
    ).

Definition sm3_ctx_views_strategy12 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (ctx : Z),
    TT &&
    emp **
    ((UIntArray.undef_full &( ((ctx)) # "_SM3_CTX" ->ₛ "digest") 8)) **
    ((poly_undef_store FET_uint64 &( ((ctx)) # "_SM3_CTX" ->ₛ "nblocks"))) **
    ((UCharArray.undef_full &( ((ctx)) # "_SM3_CTX" ->ₛ "block") 64)) **
    ((poly_undef_store FET_uint64 &( ((ctx)) # "_SM3_CTX" ->ₛ "num"))) -*
    TT &&
    emp **
    ((undef_sm3_ctx ctx))
    ).

Module Type sm3_ctx_views_Strategy_Correct.

  Axiom sm3_ctx_views_strategy1_correctness : sm3_ctx_views_strategy1.
  Axiom sm3_ctx_views_strategy10_correctness : sm3_ctx_views_strategy10.
  Axiom sm3_ctx_views_strategy13_correctness : sm3_ctx_views_strategy13.
  Axiom sm3_ctx_views_strategy20_correctness : sm3_ctx_views_strategy20.
  Axiom sm3_ctx_views_strategy22_correctness : sm3_ctx_views_strategy22.
  Axiom sm3_ctx_views_strategy2_correctness : sm3_ctx_views_strategy2.
  Axiom sm3_ctx_views_strategy4_correctness : sm3_ctx_views_strategy4.
  Axiom sm3_ctx_views_strategy5_correctness : sm3_ctx_views_strategy5.
  Axiom sm3_ctx_views_strategy11_correctness : sm3_ctx_views_strategy11.
  Axiom sm3_ctx_views_strategy21_correctness : sm3_ctx_views_strategy21.
  Axiom sm3_ctx_views_strategy3_correctness : sm3_ctx_views_strategy3.
  Axiom sm3_ctx_views_strategy12_correctness : sm3_ctx_views_strategy12.

End sm3_ctx_views_Strategy_Correct.
