Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import add_JPoint_trace_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import SimpleC.EE.Applications_human.sm2.lib.add_JPoint_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma add_JPoint_trace_strategy10_correctness : add_JPoint_trace_strategy10.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy11_correctness : add_JPoint_trace_strategy11.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy12_correctness : add_JPoint_trace_strategy12.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy13_correctness : add_JPoint_trace_strategy13.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy14_correctness : add_JPoint_trace_strategy14.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy15_correctness : add_JPoint_trace_strategy15.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy16_correctness : add_JPoint_trace_strategy16.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy17_correctness : add_JPoint_trace_strategy17.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy18_correctness : add_JPoint_trace_strategy18.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy19_correctness : add_JPoint_trace_strategy19.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy20_correctness : add_JPoint_trace_strategy20.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy21_correctness : add_JPoint_trace_strategy21.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy22_correctness : add_JPoint_trace_strategy22.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy23_correctness : add_JPoint_trace_strategy23.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy24_correctness : add_JPoint_trace_strategy24.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy25_correctness : add_JPoint_trace_strategy25.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy26_correctness : add_JPoint_trace_strategy26.
Proof.
  pre_process_default.
  unfold aj_twice_rx.
  replace (2 * aj_rx x1 y1 z1 x2 y2 z2) with
    (aj_rx x1 y1 z1 x2 y2 z2 + aj_rx x1 y1 z1 x2 y2 z2) by ring.
  reflexivity.
Qed.

Lemma add_JPoint_trace_strategy27_correctness : add_JPoint_trace_strategy27.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy28_correctness : add_JPoint_trace_strategy28.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy29_correctness : add_JPoint_trace_strategy29.
Proof.
  pre_process_default.
  unfold aj_right_y.
  rewrite Z.mul_mod_idemp_l by (pose proof sm2_p_gt_one; lia).
  reflexivity.
Qed.

Lemma add_JPoint_trace_strategy30_correctness : add_JPoint_trace_strategy30.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy31_correctness : add_JPoint_trace_strategy31.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy33_correctness : add_JPoint_trace_strategy33.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy32_correctness : add_JPoint_trace_strategy32.
Proof.
  pre_process_default.
Qed.

Lemma add_JPoint_trace_strategy34_correctness : add_JPoint_trace_strategy34.
Proof.
  unfold add_JPoint_trace_strategy34.
  pre_process_default.
  entailer!.
  assert (HP1 : P1 = ECInfinity).
  {
    apply (proj1 (jpoint_represents_infinity_iff x1 y1 z1 P1 H)).
    exact H3.
  }
  subst P1.
  apply sm2_point_add_infinity_left.
Qed.

Lemma add_JPoint_trace_strategy35_correctness : add_JPoint_trace_strategy35.
Proof.
  unfold add_JPoint_trace_strategy35.
  pre_process_default.
  entailer!.
  assert (HP2 : P2 = ECInfinity).
  {
    apply (proj1 (jpoint_represents_infinity_iff x2 y2 z2 P2 H0)).
    exact H3.
  }
  subst P2.
  apply sm2_point_add_infinity_right.
Qed.

Lemma add_JPoint_trace_strategy36_correctness : add_JPoint_trace_strategy36.
Proof.
  unfold add_JPoint_trace_strategy36.
  pre_process_default.
  entailer!.
  eapply aj_noncanonical_encoded_is_finite; eauto.
Qed.
