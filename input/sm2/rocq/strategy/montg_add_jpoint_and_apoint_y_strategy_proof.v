Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_y_strategy_goal.
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

Lemma montg_add_jpoint_and_apoint_y_strategy1_correctness : montg_add_jpoint_and_apoint_y_strategy1.
Proof.
  pre_process_default.
  unfold maja_e_minus_rx.
  rewrite ec_math_refinement.mont_p_mod.
  rewrite ec_math_refinement.mont_p_sub.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_y_strategy2_correctness : montg_add_jpoint_and_apoint_y_strategy2.
Proof.
  pre_process_default.
  unfold maja_r_times_delta.
  rewrite ec_math_refinement.mont_p_mod.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_y_strategy3_correctness : montg_add_jpoint_and_apoint_y_strategy3.
Proof.
  pre_process_default.
  unfold maja_y1h3.
  rewrite ec_math_refinement.mont_p_mod.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_y_strategy101_correctness : montg_add_jpoint_and_apoint_y_strategy101.
Proof.
  pre_process_default.
  unfold maja_e_minus_rx.
  pose proof (maja_mod_range
    (maja_u1h2 x1 x2 z1 - maja_rx x1 y1 z1 x2 y2)).
  entailer!.
Qed.
