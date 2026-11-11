Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_x_strategy_goal.
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

Lemma montg_add_jpoint_x_strategy1_correctness : montg_add_jpoint_x_strategy1.
Proof. solve_mont_sub_trace aj_h. Qed.

Lemma montg_add_jpoint_x_strategy2_correctness : montg_add_jpoint_x_strategy2.
Proof. solve_mont_sub_trace aj_rr. Qed.

Lemma montg_add_jpoint_x_strategy3_correctness : montg_add_jpoint_x_strategy3.
Proof. solve_mont_add_trace aj_u_sum. Qed.

Lemma montg_add_jpoint_x_strategy4_correctness : montg_add_jpoint_x_strategy4.
Proof. solve_mont_add_trace aj_s_sum. Qed.

Lemma montg_add_jpoint_x_strategy5_correctness : montg_add_jpoint_x_strategy5.
Proof. solve_mont_mod_trace aj_h2. Qed.

Lemma montg_add_jpoint_x_strategy6_correctness : montg_add_jpoint_x_strategy6.
Proof. solve_mont_mod_trace aj_base. Qed.

Lemma montg_add_jpoint_x_strategy7_correctness : montg_add_jpoint_x_strategy7.
Proof. solve_mont_mod_trace aj_rr2. Qed.

Lemma montg_add_jpoint_x_strategy8_correctness : montg_add_jpoint_x_strategy8.
Proof. solve_mont_sub_trace aj_rx. Qed.

Lemma montg_add_jpoint_x_strategy9_correctness : montg_add_jpoint_x_strategy9.
Proof.
  pre_process_default.
  rewrite ec_math_refinement.mont_p_double.
  finish_mont_trace aj_twice_rx.
Qed.

Lemma montg_add_jpoint_x_strategy10_correctness : montg_add_jpoint_x_strategy10.
Proof. solve_mont_sub_trace aj_base_minus_twice_rx. Qed.

Lemma montg_add_jpoint_x_strategy101_correctness : montg_add_jpoint_x_strategy101.
Proof. solve_aj_trace_range aj_h. Qed.

Lemma montg_add_jpoint_x_strategy102_correctness : montg_add_jpoint_x_strategy102.
Proof. solve_aj_trace_range aj_rr. Qed.

Lemma montg_add_jpoint_x_strategy103_correctness : montg_add_jpoint_x_strategy103.
Proof. solve_aj_trace_range aj_u_sum. Qed.

Lemma montg_add_jpoint_x_strategy104_correctness : montg_add_jpoint_x_strategy104.
Proof. solve_aj_trace_range aj_s_sum. Qed.

Lemma montg_add_jpoint_x_strategy105_correctness : montg_add_jpoint_x_strategy105.
Proof. solve_aj_trace_range aj_h2. Qed.

Lemma montg_add_jpoint_x_strategy106_correctness : montg_add_jpoint_x_strategy106.
Proof. solve_aj_trace_range aj_base. Qed.

Lemma montg_add_jpoint_x_strategy107_correctness : montg_add_jpoint_x_strategy107.
Proof. solve_aj_trace_range aj_rr2. Qed.

Lemma montg_add_jpoint_x_strategy108_correctness : montg_add_jpoint_x_strategy108.
Proof. solve_aj_trace_range aj_rx. Qed.

Lemma montg_add_jpoint_x_strategy109_correctness : montg_add_jpoint_x_strategy109.
Proof. solve_aj_trace_range aj_twice_rx. Qed.

Lemma montg_add_jpoint_x_strategy110_correctness : montg_add_jpoint_x_strategy110.
Proof. solve_aj_trace_range aj_base_minus_twice_rx. Qed.
