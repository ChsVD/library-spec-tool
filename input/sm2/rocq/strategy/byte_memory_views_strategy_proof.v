Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.byte_memory.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma byte_memory_views_strategy1_correctness : byte_memory_views_strategy1.
Proof.
  pre_process_default.
  subst q; subst m. Intros; subst. entailer!.
Qed.

Lemma byte_memory_views_strategy4_correctness : byte_memory_views_strategy4.
Proof.
  pre_process_default.
  subst q; subst m. unfold store_bytes. Intros.
  sep_apply UCharArray.full_to_undef_full. entailer!.
Qed.

Lemma byte_memory_views_strategy5_correctness : byte_memory_views_strategy5.
Proof.
  pre_process_default.
  subst q; subst m.
  replace (p + 0 * sizeof_front_end_type FET_uchar) with p by lia.
  entailer!.
Qed.

Lemma byte_memory_views_strategy6_correctness : byte_memory_views_strategy6.
Proof.
  pre_process_default.
  subst q; subst m.
  replace (p + 0 * sizeof_front_end_type FET_uchar) with p by lia.
  unfold store_bytes.
  Intros.
  sep_apply UCharArray.full_to_undef_full.
  entailer!.
Qed.

Lemma byte_memory_views_strategy10_correctness : byte_memory_views_strategy10.
Proof.
  pre_process_default.
  subst q; subst m. Intros; subst. entailer!.
Qed.

Lemma byte_memory_views_strategy13_correctness : byte_memory_views_strategy13.
Proof.
  pre_process_default.
  subst q; subst m. unfold store_u32_words. Intros.
  sep_apply UIntArray.full_to_undef_full. entailer!.
Qed.

Lemma byte_memory_views_strategy20_correctness : byte_memory_views_strategy20.
Proof.
  pre_process_default.
  subst q; subst required_capacity. Intros; subst. entailer!.
Qed.

Lemma byte_memory_views_strategy2_correctness : byte_memory_views_strategy2.
Proof.
  pre_process_default.
  unfold store_bytes. entailer!.
Qed.

Lemma byte_memory_views_strategy11_correctness : byte_memory_views_strategy11.
Proof.
  pre_process_default.
  unfold store_u32_words. entailer!.
Qed.

Lemma byte_memory_views_strategy21_correctness : byte_memory_views_strategy21.
Proof.
  pre_process_default.
  unfold store_byte_prefix. entailer!.
Qed.

Lemma byte_memory_views_strategy23_correctness : byte_memory_views_strategy23.
Proof.
  pre_process_default.
  unfold store_byte_prefix.
  rewrite Zlength_nil.
  replace (p + 0) with p by lia.
  replace (capacity - 0) with capacity by lia.
  rewrite UCharArray.full_empty.
  entailer!.
  unfold u8_list_bounded, limb_list_bounded.
  intros; rewrite Zlength_nil in H0; lia.
Qed.

Lemma byte_memory_views_strategy30_correctness : byte_memory_views_strategy30.
Proof.
  pre_process_default.
  sep_apply store_u256_to_store_bytes32.
  Intros bytes. Exists bytes. entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint. entailer!.
Qed.

Lemma byte_memory_views_strategy31_correctness : byte_memory_views_strategy31.
Proof.
  pre_process_default.
  sep_apply (store_bytes32_to_store_u256 p value bytes H H0).
  entailer!.
Qed.

Lemma byte_memory_views_strategy32_correctness : byte_memory_views_strategy32.
Proof.
  pre_process_default.
  sep_apply undef_u256_to_u8_undef_full32_aligned.
  entailer!.
Qed.

Lemma byte_memory_views_strategy3_correctness : byte_memory_views_strategy3.
Proof.
  pre_process_default.
  unfold store_bytes. entailer!.
Qed.

Lemma byte_memory_views_strategy12_correctness : byte_memory_views_strategy12.
Proof.
  pre_process_default.
  unfold store_u32_words. entailer!.
Qed.

Lemma byte_memory_views_strategy22_correctness : byte_memory_views_strategy22.
Proof.
  pre_process_default.
  unfold store_byte_prefix. entailer!.
Qed.
