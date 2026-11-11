Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_precompute_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import SimpleC.EE.Applications_human.sm2.lib.add_JPoint_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.montg_add_jpoint_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma montg_add_jpoint_precompute_strategy1_correctness : montg_add_jpoint_precompute_strategy1.
Proof. solve_mont_mod_trace aj_pz2. Qed.

Lemma montg_add_jpoint_precompute_strategy2_correctness : montg_add_jpoint_precompute_strategy2.
Proof. solve_mont_mod_trace aj_qz2. Qed.

Lemma montg_add_jpoint_precompute_strategy3_correctness : montg_add_jpoint_precompute_strategy3.
Proof. solve_mont_mod_trace aj_u1. Qed.

Lemma montg_add_jpoint_precompute_strategy4_correctness : montg_add_jpoint_precompute_strategy4.
Proof. solve_mont_mod_trace aj_u2. Qed.

Lemma montg_add_jpoint_precompute_strategy5_correctness : montg_add_jpoint_precompute_strategy5.
Proof.
  pre_process_default.
  unfold aj_pz3.
  rewrite ec_math_refinement.mont_p_mod.
  rewrite (Z.mul_comm z (aj_pz2 z)).
  entailer!.
Qed.

Lemma montg_add_jpoint_precompute_strategy6_correctness : montg_add_jpoint_precompute_strategy6.
Proof. solve_mont_mod_trace aj_s2. Qed.

Lemma montg_add_jpoint_precompute_strategy7_correctness : montg_add_jpoint_precompute_strategy7.
Proof.
  pre_process_default.
  unfold aj_qz3.
  rewrite ec_math_refinement.mont_p_mod.
  rewrite (Z.mul_comm z (aj_qz2 z)).
  entailer!.
Qed.

Lemma montg_add_jpoint_precompute_strategy8_correctness : montg_add_jpoint_precompute_strategy8.
Proof. solve_mont_mod_trace aj_s1. Qed.

Lemma montg_add_jpoint_precompute_strategy101_correctness : montg_add_jpoint_precompute_strategy101.
Proof. solve_aj_trace_range aj_pz2. Qed.

Lemma montg_add_jpoint_precompute_strategy102_correctness : montg_add_jpoint_precompute_strategy102.
Proof. solve_aj_trace_range aj_qz2. Qed.

Lemma montg_add_jpoint_precompute_strategy103_correctness : montg_add_jpoint_precompute_strategy103.
Proof. solve_aj_trace_range aj_pz3. Qed.

Lemma montg_add_jpoint_precompute_strategy104_correctness : montg_add_jpoint_precompute_strategy104.
Proof. solve_aj_trace_range aj_qz3. Qed.

Lemma montg_add_jpoint_precompute_strategy105_correctness : montg_add_jpoint_precompute_strategy105.
Proof. solve_aj_trace_range aj_u1. Qed.

Lemma montg_add_jpoint_precompute_strategy106_correctness : montg_add_jpoint_precompute_strategy106.
Proof. solve_aj_trace_range aj_u2. Qed.

Lemma montg_add_jpoint_precompute_strategy107_correctness : montg_add_jpoint_precompute_strategy107.
Proof. solve_aj_trace_range aj_s1. Qed.

Lemma montg_add_jpoint_precompute_strategy108_correctness : montg_add_jpoint_precompute_strategy108.
Proof. solve_aj_trace_range aj_s2. Qed.
