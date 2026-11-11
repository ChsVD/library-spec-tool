Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_streaming_memory_views_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sm3_streaming_memory_views_strategy6_correctness : sm3_streaming_memory_views_strategy6.
Proof.
  pre_process_default.
  subst q; subst m.
  replace (p + 0 * sizeof_front_end_type FET_uchar) with p by lia.
  entailer!.
  subst required; reflexivity.
Qed.

Lemma sm3_streaming_memory_views_strategy7_correctness : sm3_streaming_memory_views_strategy7.
Proof.
  pre_process_default.
  subst q; subst m.
  replace (p + 0 * sizeof_front_end_type FET_uint) with p by lia.
  entailer!.
  subst required; reflexivity.
Qed.

Lemma sm3_streaming_memory_views_strategy8_correctness : sm3_streaming_memory_views_strategy8.
Proof.
  pre_process_default.
  subst q; subst j; subst m.
  rewrite sizeof_uchar.
  replace (p + i * 1) with (p + i) by lia.
  reflexivity.
Qed.

Lemma sm3_streaming_memory_views_strategy13_correctness : sm3_streaming_memory_views_strategy13.
Proof.
  pre_process_default.
  subst q; subst j; subst m.
  reflexivity.
Qed.

Lemma sm3_streaming_memory_views_strategy3_correctness : sm3_streaming_memory_views_strategy3.
Proof.
  pre_process_default.
  prop_apply (store_bytes_address_space_bound src count bytes).
  Intros.
  sep_apply
    (UCharArray.undef_full_split_to_undef_full
      p count capacity ltac:(lia)).
  entailer!.
Qed.

Lemma sm3_streaming_memory_views_strategy4_correctness : sm3_streaming_memory_views_strategy4.
Proof.
  pre_process_default.
  unfold store_bytes.
  Intros.
  sep_apply
    (UCharArray.full_split_to_full p count total bytes ltac:(lia)).
  entailer!.
  - unfold u8_list_bounded.
    eapply limb_list_bounded_sublist.
    + exact (proj2 H1).
    + lia.
  - rewrite Zlength_sublist by lia.
    lia.
Qed.

Lemma sm3_streaming_memory_views_strategy5_correctness : sm3_streaming_memory_views_strategy5.
Proof.
  pre_process_default.
  sep_apply
    (UCharArray.full_merge_to_full
      p prefix_len total prefix suffix ltac:(lia)).
  entailer!.
Qed.

Lemma sm3_streaming_memory_views_strategy9_correctness : sm3_streaming_memory_views_strategy9.
Proof.
  pre_process_default.
  subst next.
  sep_apply
    (UCharArray.seg_merge_to_seg
      p lo mid hi left_bytes right_bytes ltac:(lia)).
  entailer!.
Qed.

Lemma sm3_streaming_memory_views_strategy10_correctness : sm3_streaming_memory_views_strategy10.
Proof.
  pre_process_default.
Qed.

Lemma sm3_streaming_memory_views_strategy12_correctness : sm3_streaming_memory_views_strategy12.
Proof.
  pre_process_default.
  unfold store_bytes.
  Intros.
  rewrite UCharArray.seg_0_shift.
  replace (lo + count - lo) with count by lia.
  entailer!.
Qed.

Lemma sm3_streaming_memory_views_strategy11_correctness : sm3_streaming_memory_views_strategy11.
Proof.
  pre_process_default.
  subst address; subst count.
  Intros; subst required.
  apply UCharArray.seg_to_full.
Qed.

Lemma sm3_streaming_memory_views_strategy2_correctness : sm3_streaming_memory_views_strategy2.
Proof.
  pre_process_default.
  unfold store_u32_words_missing_i, store_u32_words.
  Intros.
  replace (p + i * 4) with (p + i * sizeof(UINT))
    by (rewrite sizeof_uint; lia).
  sep_apply_l_atomic
    (UIntArray.missing_i_merge_to_full
      p i n (Znth i words 0) words).
  - dump_pre_spatial; lia.
  - rewrite replace_Znth_Znth by lia.
    entailer!.
Qed.

Lemma sm3_streaming_memory_views_strategy1_correctness : sm3_streaming_memory_views_strategy1.
Proof.
  pre_process_default.
  unfold store_u32_words, store_u32_words_missing_i.
  Intros.
  sep_apply_l_atomic
    (UIntArray.full_split_to_missing_i p i n words 0).
  - dump_pre_spatial; lia.
  - replace (p + i * 4) with (p + i * sizeof(UINT))
      by (rewrite sizeof_uint; lia).
    entailer!.
    Intros_r value.
    apply_sepcon_adjoint.
    Intros_p Hvalue.
    subst value.
    cancel.
Qed.
