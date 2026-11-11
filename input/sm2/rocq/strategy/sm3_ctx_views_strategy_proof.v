Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_ctx_views_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sm3_ctx_views_strategy1_correctness : sm3_ctx_views_strategy1.
Proof.
  pre_process_default.
  subst required_ctx.
  Intros; subst.
  entailer!.
Qed.

Lemma sm3_ctx_views_strategy10_correctness : sm3_ctx_views_strategy10.
Proof.
  pre_process_default.
  subst required_ctx.
  entailer!.
Qed.

Lemma sm3_ctx_views_strategy13_correctness : sm3_ctx_views_strategy13.
Proof.
  pre_process_default.
  subst required_ctx.
  unfold undef_sm3_ctx.
  entailer!.
Qed.

Lemma sm3_ctx_views_strategy20_correctness : sm3_ctx_views_strategy20.
Proof.
  pre_process_default.
  subst required_ctx.
  entailer!.
Qed.

Lemma sm3_ctx_views_strategy22_correctness : sm3_ctx_views_strategy22.
Proof.
  pre_process_default.
  subst required_ctx.
  unfold sm3_ctx_full_shape.
  Exists value.
  entailer!.
Qed.

Lemma sm3_ctx_views_strategy2_correctness : sm3_ctx_views_strategy2.
Proof.
  pre_process_default.
  prop_apply (store_sm3_ctx_block_aligned ctx message).
  Intros.
  prop_apply (store_sm3_ctx_count_aligned ctx message).
  Intros.
  unfold store_sm3_ctx.
  entailer!.
Qed.

Lemma sm3_ctx_views_strategy4_correctness : sm3_ctx_views_strategy4.
Proof.
  pre_process_default.
  prop_apply (store_sm3_ctx_block_aligned ctx message).
  entailer!.
Qed.

Lemma sm3_ctx_views_strategy5_correctness : sm3_ctx_views_strategy5.
Proof.
  pre_process_default.
  prop_apply (store_sm3_ctx_count_aligned ctx message).
  entailer!.
Qed.

Lemma sm3_ctx_views_strategy11_correctness : sm3_ctx_views_strategy11.
Proof.
  pre_process_default.
  unfold undef_sm3_ctx, UndefStructPred_SM3_CTX.
  entailer!.
Qed.

Lemma sm3_ctx_views_strategy21_correctness : sm3_ctx_views_strategy21.
Proof.
  pre_process_default.
  unfold store_u32_words.
  Intros.
  unfold sm3_ctx_full_shape, StructPred_SM3_CTX.
  Exists (make_record__sm3_ctx digest_words nblocks block_bytes num).
  entailer!.
Qed.

Lemma sm3_ctx_views_strategy3_correctness : sm3_ctx_views_strategy3.
Proof.
  pre_process_default.
  unfold store_sm3_ctx.
  entailer!.
Qed.

Lemma sm3_ctx_views_strategy12_correctness : sm3_ctx_views_strategy12.
Proof.
  pre_process_default.
  unfold undef_sm3_ctx, UndefStructPred_SM3_CTX.
  entailer!.
Qed.
