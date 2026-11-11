Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_precompute_strategy_goal.
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

Lemma montg_add_jpoint_and_apoint_precompute_strategy1_correctness : montg_add_jpoint_and_apoint_precompute_strategy1.
Proof.
  pre_process_default.
  unfold maja_z2.
  rewrite ec_math_refinement.mont_p_mod.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_precompute_strategy2_correctness : montg_add_jpoint_and_apoint_precompute_strategy2.
Proof.
  pre_process_default.
  unfold maja_u2.
  rewrite ec_math_refinement.mont_p_mod.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_precompute_strategy3_correctness : montg_add_jpoint_and_apoint_precompute_strategy3.
Proof.
  pre_process_default.
  unfold maja_z3.
  rewrite ec_math_refinement.mont_p_mod.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_precompute_strategy4_correctness : montg_add_jpoint_and_apoint_precompute_strategy4.
Proof.
  pre_process_default.
  unfold maja_s2.
  rewrite ec_math_refinement.mont_p_mod.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_precompute_strategy101_correctness : montg_add_jpoint_and_apoint_precompute_strategy101.
Proof.
  pre_process_default.
  unfold maja_z2.
  pose proof (maja_mod_range (z * z)).
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_precompute_strategy103_correctness : montg_add_jpoint_and_apoint_precompute_strategy103.
Proof.
  pre_process_default.
  unfold maja_z3.
  pose proof (maja_mod_range (z * maja_z2 z)).
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_precompute_strategy105_correctness : montg_add_jpoint_and_apoint_precompute_strategy105.
Proof.
  pre_process_default.
  unfold maja_h.
  pose proof (maja_mod_range (maja_u2 x2 z1 - x1)).
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_precompute_strategy106_correctness : montg_add_jpoint_and_apoint_precompute_strategy106.
Proof.
  pre_process_default.
  unfold maja_r.
  pose proof (maja_mod_range (maja_s2 y2 z1 - y1)).
  entailer!.
Qed.
