Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import jpoint_double_trace_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Require Import SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma jpoint_double_trace_strategy12_correctness : jpoint_double_trace_strategy12.
  unfold jpoint_double_trace_strategy12.
  intros.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy13_correctness : jpoint_double_trace_strategy13.
  unfold jpoint_double_trace_strategy13.
  intros.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy14_correctness : jpoint_double_trace_strategy14.
  unfold jpoint_double_trace_strategy14.
  intros.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy15_correctness : jpoint_double_trace_strategy15.
  unfold jpoint_double_trace_strategy15.
  intros.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy16_correctness : jpoint_double_trace_strategy16.
  unfold jpoint_double_trace_strategy16.
  intros.
  pre_process_default.
  unfold jdouble_trace_sum.
  rewrite Z.add_comm.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy17_correctness : jpoint_double_trace_strategy17.
  unfold jpoint_double_trace_strategy17.
  intros.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy18_correctness : jpoint_double_trace_strategy18.
  unfold jpoint_double_trace_strategy18.
  intros.
  pre_process_default.
  unfold jdouble_trace_prod.
  rewrite Z.mul_comm.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy19_correctness : jpoint_double_trace_strategy19.
  unfold jpoint_double_trace_strategy19.
  intros.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy20_correctness : jpoint_double_trace_strategy20.
  unfold jpoint_double_trace_strategy20.
  intros.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy21_correctness : jpoint_double_trace_strategy21.
  unfold jpoint_double_trace_strategy21.
  intros.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy22_correctness : jpoint_double_trace_strategy22.
  unfold jpoint_double_trace_strategy22.
  intros.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy23_correctness : jpoint_double_trace_strategy23.
  unfold jpoint_double_trace_strategy23.
  intros.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy24_correctness : jpoint_double_trace_strategy24.
  unfold jpoint_double_trace_strategy24.
  intros.
  pre_process_default.
  unfold jdouble_trace_tmp2.
  rewrite Z.mul_comm.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy25_correctness : jpoint_double_trace_strategy25.
  unfold jpoint_double_trace_strategy25.
  intros.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy30_correctness : jpoint_double_trace_strategy30.
  unfold jpoint_double_trace_strategy30.
  intros.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy31_correctness : jpoint_double_trace_strategy31.
  unfold jpoint_double_trace_strategy31.
  intros.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy112_correctness : jpoint_double_trace_strategy112.
  unfold jpoint_double_trace_strategy112.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_m4 y < SM2_P_Z).
  {
    unfold jdouble_trace_m4.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_m4.
  rewrite mont_p_mod.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy113_correctness : jpoint_double_trace_strategy113.
  unfold jpoint_double_trace_strategy113.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_t16 y < SM2_P_Z).
  {
    unfold jdouble_trace_t16.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_t16.
  rewrite mont_p_mod.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy114_correctness : jpoint_double_trace_strategy114.
  unfold jpoint_double_trace_strategy114.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_s4 x y < SM2_P_Z).
  {
    unfold jdouble_trace_s4.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_s4.
  rewrite mont_p_mod.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy115_correctness : jpoint_double_trace_strategy115.
  unfold jpoint_double_trace_strategy115.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_t8 y < SM2_P_Z).
  {
    unfold jdouble_trace_t8.
    apply fp_div2_bounds.
    unfold jdouble_trace_t16.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy116_correctness : jpoint_double_trace_strategy116.
  unfold jpoint_double_trace_strategy116.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_sum x z < SM2_P_Z).
  {
    unfold jdouble_trace_sum.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_sum.
  rewrite mont_p_mod.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy117_correctness : jpoint_double_trace_strategy117.
  unfold jpoint_double_trace_strategy117.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_diff x z < SM2_P_Z).
  {
    unfold jdouble_trace_diff.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_diff.
  rewrite mont_p_mod.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy118_correctness : jpoint_double_trace_strategy118.
  unfold jpoint_double_trace_strategy118.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_prod x z < SM2_P_Z).
  {
    unfold jdouble_trace_prod.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_prod.
  rewrite mont_p_mod.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy119_correctness : jpoint_double_trace_strategy119.
  unfold jpoint_double_trace_strategy119.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_slope x z < SM2_P_Z).
  {
    unfold jdouble_trace_slope.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_slope.
  rewrite mont_p_mod.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy120_correctness : jpoint_double_trace_strategy120.
  unfold jpoint_double_trace_strategy120.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_slope_sq x z < SM2_P_Z).
  {
    unfold jdouble_trace_slope_sq.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_slope_sq.
  rewrite mont_p_mod.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy121_correctness : jpoint_double_trace_strategy121.
  unfold jpoint_double_trace_strategy121.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_u8 x y < SM2_P_Z).
  {
    unfold jdouble_trace_u8.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_u8.
  rewrite mont_p_mod.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy122_correctness : jpoint_double_trace_strategy122.
  unfold jpoint_double_trace_strategy122.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_rx x y z < SM2_P_Z).
  {
    unfold jdouble_trace_rx.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_rx.
  rewrite mont_p_mod.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy123_correctness : jpoint_double_trace_strategy123.
  unfold jpoint_double_trace_strategy123.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_tmp x y z < SM2_P_Z).
  {
    unfold jdouble_trace_tmp.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_tmp.
  rewrite mont_p_mod.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy124_correctness : jpoint_double_trace_strategy124.
  unfold jpoint_double_trace_strategy124.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_tmp2 x y z < SM2_P_Z).
  {
    unfold jdouble_trace_tmp2.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_tmp2.
  rewrite mont_p_mod.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy125_correctness : jpoint_double_trace_strategy125.
  unfold jpoint_double_trace_strategy125.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_ry x y z < SM2_P_Z).
  {
    unfold jdouble_trace_ry.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_ry.
  rewrite mont_p_mod.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy130_correctness : jpoint_double_trace_strategy130.
  unfold jpoint_double_trace_strategy130.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_s2 y < SM2_P_Z).
  {
    unfold jdouble_trace_s2.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_s2.
  rewrite mont_p_mod.
  pre_process_default.
Qed.

Lemma jpoint_double_trace_strategy131_correctness : jpoint_double_trace_strategy131.
  unfold jpoint_double_trace_strategy131.
  intros.
  pre_process_default.
  assert (Hrange : 0 <= jdouble_trace_z2 z < SM2_P_Z).
  {
    unfold jdouble_trace_z2.
    apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds.
    lia.
  }
  unfold jdouble_trace_z2.
  rewrite mont_p_mod.
  pre_process_default.
Qed.
