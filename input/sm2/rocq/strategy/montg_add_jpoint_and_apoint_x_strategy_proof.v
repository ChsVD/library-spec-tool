Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_x_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.montg_add_jpoint_and_apoint_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma montg_add_jpoint_and_apoint_x_strategy1_correctness : montg_add_jpoint_and_apoint_x_strategy1.
Proof.
  pre_process_default.
  unfold maja_h2.
  rewrite ec_math_refinement.mont_p_mod.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_x_strategy2_correctness : montg_add_jpoint_and_apoint_x_strategy2.
Proof.
  pre_process_default.
  unfold maja_h3.
  rewrite ec_math_refinement.mont_p_mod.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_x_strategy3_correctness : montg_add_jpoint_and_apoint_x_strategy3.
Proof.
  pre_process_default.
  unfold maja_u1h2.
  rewrite ec_math_refinement.mont_p_mod.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_x_strategy4_correctness : montg_add_jpoint_and_apoint_x_strategy4.
Proof.
  pre_process_default.
  unfold maja_two_u1h2.
  rewrite ec_math_refinement.mont_p_mod.
  rewrite ec_math_refinement.mont_p_double.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_x_strategy5_correctness : montg_add_jpoint_and_apoint_x_strategy5.
Proof.
  pre_process_default.
  unfold maja_x_adjust.
  rewrite ec_math_refinement.mont_p_mod.
  rewrite ec_math_refinement.mont_p_add.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_x_strategy6_correctness : montg_add_jpoint_and_apoint_x_strategy6.
Proof.
  pre_process_default.
  unfold maja_r2.
  rewrite ec_math_refinement.mont_p_mod.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_x_strategy7_correctness : montg_add_jpoint_and_apoint_x_strategy7.
Proof.
  pre_process_default.
  unfold maja_rx.
  rewrite ec_math_refinement.mont_p_mod.
  rewrite ec_math_refinement.mont_p_sub.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_x_strategy101_correctness : montg_add_jpoint_and_apoint_x_strategy101.
Proof.
  pre_process_default.
  unfold maja_h2.
  pose proof (maja_mod_range
    (maja_h x1 x2 z1 * maja_h x1 x2 z1)).
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_x_strategy102_correctness : montg_add_jpoint_and_apoint_x_strategy102.
Proof.
  pre_process_default.
  unfold maja_h3.
  pose proof (maja_mod_range
    (maja_h x1 x2 z1 * maja_h2 x1 x2 z1)).
  entailer!.
Qed.
