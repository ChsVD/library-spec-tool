Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_goal.
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

Lemma ecc_point_copy_steps_strategy10_correctness : ecc_point_copy_steps_strategy10.
  pre_process_default.
Qed.

Lemma ecc_point_copy_steps_strategy15_correctness : ecc_point_copy_steps_strategy15.
  pre_process_default.
Qed.

Lemma ecc_point_copy_steps_strategy20_correctness : ecc_point_copy_steps_strategy20.
  pre_process_default.
  unfold UndefStructPredJPoint, UndefStructPredu32.
  cancel.
  reflexivity.
Qed.

Lemma ecc_point_copy_steps_strategy25_correctness : ecc_point_copy_steps_strategy25.
  pre_process_default.
  unfold UndefStructPredJPoint, UndefStructPredu32.
  cancel.
  reflexivity.
Qed.

Lemma ecc_point_copy_steps_strategy30_correctness : ecc_point_copy_steps_strategy30.
  pre_process_default.
  subst result.
  unfold store_jpoint_fields, store_fp, store_mod,
    UndefStructPredJPoint, UndefStructPredu32.
  entailer!.
  repeat sep_apply store_u256_to_undef.
  entailer!.
  unfold UndefStructPredu32.
  cancel.
Qed.

Lemma ecc_point_copy_steps_strategy31_correctness : ecc_point_copy_steps_strategy31.
  pre_process_default.
  subst result.
  unfold store_jpoint_fields, store_fp, store_mod,
    UndefStructPredJPoint, UndefStructPredu32.
  entailer!.
  repeat sep_apply store_u256_to_undef.
  entailer!.
  unfold UndefStructPredu32.
  cancel.
Qed.

Lemma ecc_point_copy_steps_strategy32_correctness : ecc_point_copy_steps_strategy32.
  pre_process_default.
  subst result.
  unfold store_fp, store_mod, UndefStructPredJPoint, UndefStructPredu32.
  entailer!.
  repeat sep_apply store_u256_to_undef.
  entailer!.
  unfold UndefStructPredu32.
  cancel.
Qed.

Lemma ecc_point_copy_steps_strategy33_correctness : ecc_point_copy_steps_strategy33.
  pre_process_default.
  subst result.
  unfold store_fp, store_mod, UndefStructPredJPoint, UndefStructPredu32.
  entailer!.
  repeat sep_apply store_u256_to_undef.
  entailer!.
  unfold UndefStructPredu32.
  cancel.
Qed.
