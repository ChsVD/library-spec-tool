Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
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

Lemma ecc_representation_strategy10_correctness : ecc_representation_strategy10.
Proof.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma ecc_representation_strategy13_correctness : ecc_representation_strategy13.
Proof.
  pre_process_default.
  unfold store_afpoint_fields, store_fp, store_mod.
  entailer!.
  Intros_r rx.
  apply_sepcon_adjoint.
  Intros_p Hx.
  subst rx.
  cancel.
Qed.

Lemma ecc_representation_strategy14_correctness : ecc_representation_strategy14.
Proof.
  pre_process_default.
  unfold store_afpoint_fields, store_fp, store_mod.
  entailer!.
  Intros_r ry.
  apply_sepcon_adjoint.
  Intros_p Hy.
  subst ry.
  cancel.
Qed.

Lemma ecc_representation_strategy110_correctness : ecc_representation_strategy110.
Proof.
  pre_process_default.
  subst q.
  unfold store_afpoint_fields, store_fp, store_mod.
  entailer!.
  Intros_r rx.
  apply_sepcon_adjoint.
  Intros_p Hx.
  subst rx.
  entailer!.
Qed.

Lemma ecc_representation_strategy111_correctness : ecc_representation_strategy111.
Proof.
  pre_process_default.
  subst q.
  unfold store_afpoint_fields, store_fp, store_mod.
  entailer!.
  Intros_r ry.
  apply_sepcon_adjoint.
  Intros_p Hy.
  subst ry.
  entailer!.
Qed.

Lemma ecc_representation_strategy20_correctness : ecc_representation_strategy20.
Proof.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma ecc_representation_strategy120_correctness : ecc_representation_strategy120.
Proof.
  pre_process_default.
  subst q.
  unfold store_jpoint_fields.
  entailer!.
  Intros_r rx.
  apply_sepcon_adjoint.
  Intros_p Hx.
  subst rx.
  cancel.
Qed.

Lemma ecc_representation_strategy121_correctness : ecc_representation_strategy121.
Proof.
  pre_process_default.
  subst q.
  unfold store_jpoint_fields.
  entailer!.
  Intros_r ry.
  apply_sepcon_adjoint.
  Intros_p Hy.
  subst ry.
  cancel.
Qed.

Lemma ecc_representation_strategy122_correctness : ecc_representation_strategy122.
Proof.
  pre_process_default.
  subst q.
  unfold store_jpoint_fields.
  entailer!.
  Intros_r rz.
  apply_sepcon_adjoint.
  Intros_p Hz.
  subst rz.
  cancel.
Qed.

Lemma ecc_representation_strategy126_correctness : ecc_representation_strategy126.
Proof.
  pre_process_default.
  subst q.
  unfold store_jpoint_fields, store_fp, store_mod, store_u256.
  entailer!.
  sep_apply store_u256_limbs_to_undef_full.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma ecc_representation_strategy127_correctness : ecc_representation_strategy127.
Proof.
  pre_process_default.
  subst q.
  unfold store_jpoint_fields, store_fp, store_mod, store_u256.
  entailer!.
  sep_apply store_u256_limbs_to_undef_full.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma ecc_representation_strategy128_correctness : ecc_representation_strategy128.
Proof.
  pre_process_default.
  subst q.
  unfold store_jpoint_fields, store_fp, store_mod, store_u256.
  entailer!.
  sep_apply store_u256_limbs_to_undef_full.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma ecc_representation_strategy130_correctness : ecc_representation_strategy130.
Proof.
  pre_process_default.
  subst q.
  unfold store_jpoint_fields, store_fp, store_mod.
  entailer!.
  Intros_r rx.
  apply_sepcon_adjoint.
  Intros_p Hx.
  subst rx.
  cancel.
Qed.

Lemma ecc_representation_strategy131_correctness : ecc_representation_strategy131.
Proof.
  pre_process_default.
  subst q.
  unfold store_jpoint_fields, store_fp, store_mod.
  entailer!.
  Intros_r ry.
  apply_sepcon_adjoint.
  Intros_p Hy.
  subst ry.
  cancel.
Qed.

Lemma ecc_representation_strategy132_correctness : ecc_representation_strategy132.
Proof.
  pre_process_default.
  subst q.
  unfold store_jpoint_fields, store_fp, store_mod.
  entailer!.
  Intros_r rz.
  apply_sepcon_adjoint.
  Intros_p Hz.
  subst rz.
  cancel.
Qed.

Lemma ecc_representation_strategy30_correctness : ecc_representation_strategy30.
Proof.
  pre_process_default.
Qed.

Lemma ecc_representation_strategy40_correctness : ecc_representation_strategy40.
Proof.
  pre_process_default.
Qed.

Lemma ecc_representation_strategy50_correctness : ecc_representation_strategy50.
Proof.
  pre_process_default.
Qed.

Lemma ecc_representation_strategy60_correctness : ecc_representation_strategy60.
Proof.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma ecc_representation_strategy70_correctness : ecc_representation_strategy70.
Proof.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma ecc_representation_strategy80_correctness : ecc_representation_strategy80.
Proof.
  pre_process_default.
Qed.

Lemma ecc_representation_strategy90_correctness : ecc_representation_strategy90.
Proof.
  pre_process_default.
Qed.

Lemma ecc_representation_strategy11_correctness : ecc_representation_strategy11.
Proof.
  pre_process_default.
Qed.

Lemma ecc_representation_strategy112_correctness : ecc_representation_strategy112.
Proof.
  pre_process_default.
  unfold store_afpoint_fields.
  sep_apply store_fp_materialize_full.
  Intros xs.
  sep_apply store_fp_materialize_full.
  Intros ys.
  Exists xs ys.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma ecc_representation_strategy21_correctness : ecc_representation_strategy21.
Proof.
  pre_process_default.
  unfold store_jpoint_fields.
  entailer!.
Qed.

Lemma ecc_representation_strategy129_correctness : ecc_representation_strategy129.
Proof.
  pre_process_default.
  unfold store_jpoint_fields.
  sep_apply store_fp_materialize_full.
  Intros xs.
  sep_apply store_fp_materialize_full.
  Intros ys.
  sep_apply store_fp_materialize_full.
  Intros zs.
  Exists xs ys zs.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma ecc_representation_strategy31_correctness : ecc_representation_strategy31.
Proof.
  pre_process_default.
  unfold store_afpoint.
  entailer!.
  Intros x y.
  Exists x y.
  entailer!.
  pre_process_default.
Qed.

Lemma ecc_representation_strategy41_correctness : ecc_representation_strategy41.
Proof.
  pre_process_default.
  unfold store_jpoint.
  entailer!.
  Intros x y z.
  Exists x y z.
  entailer!.
  pre_process_default.
Qed.

Lemma ecc_representation_strategy51_correctness : ecc_representation_strategy51.
Proof.
  pre_process_default.
  unfold store_jpoint_with_canonical_infinity.
  entailer!.
  Intros x y z.
  Exists x y z.
  unfold jpoint_canonical_infinity_encoding.
  entailer!.
  pre_process_default.
  destruct H as [_ H].
  exact H.
Qed.

Lemma ecc_representation_strategy61_correctness : ecc_representation_strategy61.
Proof.
  pre_process_default.
  unfold store_mont_afpoint_coords.
  entailer!.
Qed.

Lemma ecc_representation_strategy71_correctness : ecc_representation_strategy71.
Proof.
  pre_process_default.
  unfold store_mont_jpoint_coords.
  entailer!.
Qed.

Lemma ecc_representation_strategy81_correctness : ecc_representation_strategy81.
Proof.
  pre_process_default.
  unfold store_mont_afpoint.
  entailer!.
  Intros x y.
  Exists x y.
  entailer!.
  pre_process_default.
Qed.

Lemma ecc_representation_strategy91_correctness : ecc_representation_strategy91.
Proof.
  pre_process_default.
  unfold store_mont_jpoint.
  entailer!.
  Intros x y z.
  Exists x y z.
  entailer!.
  pre_process_default.
Qed.

Lemma ecc_representation_strategy18_correctness : ecc_representation_strategy18.
Proof.
  pre_process_default.
  unfold store_jpoint_fields, store_fp, store_mod, store_u256.
  entailer!.
  sep_apply store_u256_limbs_to_undef_full.
  sep_apply store_u256_limbs_to_undef_full.
  sep_apply store_u256_limbs_to_undef_full.
  entailer!.
Qed.

Lemma ecc_representation_strategy12_correctness : ecc_representation_strategy12.
Proof.
  pre_process_default.
Qed.

Lemma ecc_representation_strategy22_correctness : ecc_representation_strategy22.
Proof.
  pre_process_default.
  unfold store_jpoint_fields.
  entailer!.
Qed.

Lemma ecc_representation_strategy32_correctness : ecc_representation_strategy32.
Proof.
  pre_process_default.
  unfold store_afpoint.
  entailer!.
  Exists x y.
  entailer!.
Qed.

Lemma ecc_representation_strategy42_correctness : ecc_representation_strategy42.
Proof.
  pre_process_default.
  unfold store_jpoint.
  entailer!.
  Exists x y z.
  entailer!.
Qed.

Lemma ecc_representation_strategy52_correctness : ecc_representation_strategy52.
Proof.
  pre_process_default.
  unfold store_jpoint_with_canonical_infinity,
    jpoint_canonical_infinity_encoding.
  entailer!.
  Exists x y z.
  entailer!.
Qed.

Lemma ecc_representation_strategy62_correctness : ecc_representation_strategy62.
Proof.
  pre_process_default.
  unfold store_mont_afpoint_coords.
  entailer!.
Qed.

Lemma ecc_representation_strategy72_correctness : ecc_representation_strategy72.
Proof.
  pre_process_default.
  unfold store_mont_jpoint_coords.
  entailer!.
Qed.

Lemma ecc_representation_strategy82_correctness : ecc_representation_strategy82.
Proof.
  pre_process_default.
  unfold store_mont_afpoint.
  entailer!.
  Exists x y.
  entailer!.
Qed.

Lemma ecc_representation_strategy92_correctness : ecc_representation_strategy92.
Proof.
  pre_process_default.
  unfold store_mont_jpoint.
  entailer!.
  Exists x y z.
  entailer!.
Qed.
