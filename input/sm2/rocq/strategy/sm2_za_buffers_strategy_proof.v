Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_za_buffers_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sm2_za_buffers_strategy4_correctness : sm2_za_buffers_strategy4.
Proof.
  pre_process_default.
  subst required_lo; subst required_hi.
  Intros; subst required_bytes.
  entailer!.
Qed.

Lemma sm2_za_buffers_strategy6_correctness : sm2_za_buffers_strategy6.
Proof.
  pre_process_default.
  subst required_n.
  Intros; subst required_bytes.
  entailer!.
Qed.

Lemma sm2_za_buffers_strategy8_correctness : sm2_za_buffers_strategy8.
Proof.
  pre_process_default.
  subst required_n.
  entailer!.
Qed.

Lemma sm2_za_buffers_strategy1_correctness : sm2_za_buffers_strategy1.
Proof.
  pre_process_default.
  sep_apply UCharArray.undef_full_to_mixed_full.
  entailer!.
Qed.

Lemma sm2_za_buffers_strategy2_correctness : sm2_za_buffers_strategy2.
Proof.
  pre_process_default.
  assert (Hrepeat :
    repeat_Z (None : option Z) n =
      None :: None :: repeat_Z None (n - 2)).
  {
    unfold repeat_Z.
    replace (Z.to_nat n) with (S (S (Z.to_nat (n - 2)))) by lia.
    reflexivity.
  }
  rewrite Hrepeat.
  unfold replace_Znth; simpl.
  rewrite UCharArray.mixed_full_unfold.
  rewrite UCharArray.mixed_seg_unfold.
  simpl UCharArray.mixedstoreA.
  sep_apply UCharArray.mixed_seg_to_undef_seg.
  rewrite UCharArray.seg_unfold.
  rewrite UCharArray.seg_unfold.
  simpl.
  replace (p + 0) with p by lia.
  replace (1 + 1) with 2 by lia.
  cancel.
  rewrite UCharArray.seg_empty.
  entailer!.
Qed.

Lemma sm2_za_buffers_strategy3_correctness : sm2_za_buffers_strategy3.
Proof.
  pre_process_default.
  subst next.
  prop_apply (UCharArray.seg_valid p lo mid left_bytes).
  Intros.
  prop_apply (UCharArray.seg_valid p mid hi right_bytes).
  Intros.
  sep_apply
    (UCharArray.seg_merge_to_seg
       p lo mid hi left_bytes right_bytes); [entailer! | lia].
Qed.

Lemma sm2_za_buffers_strategy5_correctness : sm2_za_buffers_strategy5.
Proof.
  pre_process_default.
Qed.

Lemma sm2_za_buffers_strategy7_correctness : sm2_za_buffers_strategy7.
Proof.
  pre_process_default.
  sep_apply UCharArray.full_to_undef_full.
  entailer!.
Qed.

Lemma sm2_za_buffers_strategy9_correctness : sm2_za_buffers_strategy9.
Proof.
  pre_process_default.
  unfold store_bytes.
  Intros.
  replace (base + 0 * sizeof_front_end_type FET_uchar) with base by lia.
  prop_apply (UCharArray.full_Zlength base used bytes).
  Intros.
  prop_apply (UCharArray.undef_seg_valid base used capacity).
  Intros.
  sep_apply (UCharArray.full_to_seg base used bytes).
  sep_apply (UCharArray.seg_to_undef_seg base 0 used bytes).
  pose proof (Zlength_nonneg bytes).
  etransitivity.
  {
    apply (UCharArray.undef_seg_merge_to_undef_full
             base 0 used capacity).
    lia.
  }
  replace (base + 0 * sizeof_front_end_type FET_uchar) with base by lia.
  replace (capacity - 0) with capacity by lia.
  entailer!.
Qed.

Lemma sm2_za_buffers_strategy11_correctness : sm2_za_buffers_strategy11.
Proof.
  pre_process_default.
  unfold store_bytes.
  Intros.
  sep_apply UCharArray.full_to_seg.
  entailer!.
  rewrite (UCharArray.seg_0_shift base lo (lo + count) bytes).
  replace (lo + count - lo) with count by lia.
  entailer!.
Qed.

Lemma sm2_za_buffers_strategy10_correctness : sm2_za_buffers_strategy10.
Proof.
  pre_process_default.
  Intros.
  subst required.
  subst address.
  subst count.
  apply UCharArray.seg_to_full.
Qed.
