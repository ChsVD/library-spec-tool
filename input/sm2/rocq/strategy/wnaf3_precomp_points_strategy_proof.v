Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import wnaf3_precomp_points_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma wnaf3_precomp_points_strategy10_correctness : wnaf3_precomp_points_strategy10.
Proof.
  pre_process_default.
  unfold wnaf3_precomp_undef, afpoint_array_slot,
    UndefStructPredAFPoint, UndefStructPredu32.
  pose proof sm2_c_layout.sizeof_AFPoint_matches_generated as Hlayout.
  change (sizeof_front_end_type (FET_alias "AFPoint") =
    StoreStructAFPointAsElement.sizeA) in Hlayout.
  rewrite Hlayout.
  entailer!.
Qed.

Lemma wnaf3_precomp_points_strategy11_correctness : wnaf3_precomp_points_strategy11.
Proof.
  pre_process_default.
  unfold store_mont_wnaf3_precomp, afpoint_array_slot.
  pose proof sm2_c_layout.sizeof_AFPoint_matches_generated as Hlayout.
  change (sizeof_front_end_type (FET_alias "AFPoint") =
    StoreStructAFPointAsElement.sizeA) in Hlayout.
  rewrite Hlayout.
  entailer!.
Qed.

Lemma wnaf3_precomp_points_strategy20_correctness : wnaf3_precomp_points_strategy20.
Proof.
  pre_process_default.
  pose proof sm2_c_layout.sizeof_AFPoint_matches_generated as Hlayout.
  change (sizeof_front_end_type (FET_alias "AFPoint") =
    StoreStructAFPointAsElement.sizeA) in Hlayout.
  rewrite Hlayout.
  rewrite (store_mont_wnaf3_precomp_focus_positive
    positive negative point digit H H0).
  entailer!.
Qed.

Lemma wnaf3_precomp_points_strategy21_correctness : wnaf3_precomp_points_strategy21.
Proof.
  pre_process_default.
  pose proof sm2_c_layout.sizeof_AFPoint_matches_generated as Hlayout.
  change (sizeof_front_end_type (FET_alias "AFPoint") =
    StoreStructAFPointAsElement.sizeA) in Hlayout.
  rewrite Hlayout.
  rewrite (store_mont_wnaf3_precomp_restore_positive
    positive negative point digit H H0).
  entailer!.
Qed.

Lemma wnaf3_precomp_points_strategy22_correctness : wnaf3_precomp_points_strategy22.
Proof.
  pre_process_default.
  pose proof sm2_c_layout.sizeof_AFPoint_matches_generated as Hlayout.
  change (sizeof_front_end_type (FET_alias "AFPoint") =
    StoreStructAFPointAsElement.sizeA) in Hlayout.
  rewrite Hlayout.
  rewrite (store_mont_wnaf3_precomp_focus_negative
    positive negative point digit H H0).
  entailer!.
Qed.

Lemma wnaf3_precomp_points_strategy23_correctness : wnaf3_precomp_points_strategy23.
Proof.
  pre_process_default.
  pose proof sm2_c_layout.sizeof_AFPoint_matches_generated as Hlayout.
  change (sizeof_front_end_type (FET_alias "AFPoint") =
    StoreStructAFPointAsElement.sizeA) in Hlayout.
  rewrite Hlayout.
  rewrite (store_mont_wnaf3_precomp_restore_negative
    positive negative point digit H H0).
  entailer!.
Qed.

Lemma wnaf3_precomp_points_strategy30_correctness : wnaf3_precomp_points_strategy30.
Proof.
  pre_process_default.
  repeat rewrite (StructAFPointArray.undef_full_unfold _ 3 nil) by lia.
  repeat rewrite (StructAFPointArray.undef_seg_unfold _ 1 4) by lia.
  repeat rewrite (StructAFPointArray.undef_seg_unfold _ 2 4) by lia.
  repeat rewrite (StructAFPointArray.undef_seg_unfold _ 3 4) by lia.
  repeat rewrite StructAFPointArray.undef_seg_empty.
  unfold wnaf3_positive_array_undef, afpoint_array_slot,
    StoreStructAFPointAsElement.undefstoreA.
  entailer!.
Qed.

Lemma wnaf3_precomp_points_strategy31_correctness : wnaf3_precomp_points_strategy31.
Proof.
  pre_process_default.
  repeat rewrite (StructAFPointArray.undef_full_unfold _ 3 nil) by lia.
  repeat rewrite (StructAFPointArray.undef_seg_unfold _ 1 4) by lia.
  repeat rewrite (StructAFPointArray.undef_seg_unfold _ 2 4) by lia.
  repeat rewrite (StructAFPointArray.undef_seg_unfold _ 3 4) by lia.
  repeat rewrite StructAFPointArray.undef_seg_empty.
  unfold wnaf3_negative_array_undef, afpoint_array_slot,
    StoreStructAFPointAsElement.undefstoreA.
  entailer!.
Qed.

Lemma wnaf3_precomp_points_strategy32_correctness : wnaf3_precomp_points_strategy32.
Proof.
  pre_process_default.
  unfold wnaf3_positive_array_undef, wnaf3_negative_array_undef,
    wnaf3_precomp_undef, wnaf3_precomp_unused.
  entailer!.
Qed.

Lemma wnaf3_precomp_points_strategy33_correctness : wnaf3_precomp_points_strategy33.
Proof.
  pre_process_default.
  assert (Hafpoint_to_undef : forall address point,
    store_mont_afpoint address point |-- UndefStructPredAFPoint address).
  {
    intros address value.
    unfold store_mont_afpoint, store_mont_afpoint_coords,
      store_afpoint_fields, store_fp, store_mod,
      UndefStructPredAFPoint, UndefStructPredu32.
    Intros x y.
    repeat sep_apply store_u256_to_undef.
    entailer!.
    unfold UndefStructPredu32.
    cancel.
  }
  unfold store_mont_wnaf3_precomp, wnaf3_precomp_unused,
    afpoint_array_slot.
  rewrite (Hafpoint_to_undef
    (positive + 1 * StoreStructAFPointAsElement.sizeA) point).
  rewrite (Hafpoint_to_undef
    (positive + 3 * StoreStructAFPointAsElement.sizeA)
    (sm2_point_mul 3 point)).
  rewrite (Hafpoint_to_undef
    (negative + 1 * StoreStructAFPointAsElement.sizeA)
    (sm2_point_negate point)).
  rewrite (Hafpoint_to_undef
    (negative + 3 * StoreStructAFPointAsElement.sizeA)
    (sm2_point_negate (sm2_point_mul 3 point))).
  repeat rewrite (StructAFPointArray.undef_full_unfold _ 3 nil) by lia.
  repeat rewrite (StructAFPointArray.undef_seg_unfold _ 1 4) by lia.
  repeat rewrite (StructAFPointArray.undef_seg_unfold _ 2 4) by lia.
  repeat rewrite (StructAFPointArray.undef_seg_unfold _ 3 4) by lia.
  repeat rewrite StructAFPointArray.undef_seg_empty.
  unfold StoreStructAFPointAsElement.undefstoreA.
  entailer!.
Qed.

Lemma wnaf3_precomp_points_strategy35_correctness : wnaf3_precomp_points_strategy35.
Proof.
  pre_process_default.
  replace (positive + 0 * sizeof_front_end_type (FET_alias "AFPoint"))
    with positive by lia.
  replace (negative + 0 * sizeof_front_end_type (FET_alias "AFPoint"))
    with negative by lia.
  entailer!.
Qed.

Lemma wnaf3_precomp_points_strategy41_correctness : wnaf3_precomp_points_strategy41.
Proof.
  pre_process_default.
  unfold store_wnaf3.
  Intros digits.
  Exists digits.
  entailer!.
  unfold WNAF3_LENGTH.
  entailer!.
  pre_process_default.
Qed.

Lemma wnaf3_precomp_points_strategy42_correctness : wnaf3_precomp_points_strategy42.
Proof.
  pre_process_default.
  apply CharArray.full_to_undef_full.
Qed.

Lemma wnaf3_precomp_points_strategy43_correctness : wnaf3_precomp_points_strategy43.
Proof.
  pre_process_default.
  replace (address + 0 * sizeof_front_end_type FET_char)
    with address by lia.
  entailer!.
Qed.
