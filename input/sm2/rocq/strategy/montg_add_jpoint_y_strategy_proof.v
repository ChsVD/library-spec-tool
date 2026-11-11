Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_y_strategy_goal.
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

Lemma montg_add_jpoint_y_strategy1_correctness : montg_add_jpoint_y_strategy1.
Proof.
  pre_process_default.
  rewrite ec_math_refinement.mont_p_mod.
  finish_spatial_trace.
Qed.

Lemma montg_add_jpoint_y_strategy2_correctness : montg_add_jpoint_y_strategy2.
Proof.
  pre_process_default.
  rewrite montg_add_right_y_mont.
  finish_spatial_trace.
Qed.

Lemma montg_add_jpoint_y_strategy3_correctness : montg_add_jpoint_y_strategy3.
Proof.
  pre_process_default.
  finish_mont_trace aj_left_y.
Qed.

Lemma montg_add_jpoint_y_strategy4_correctness : montg_add_jpoint_y_strategy4.
Proof.
  pre_process_default.
  rewrite ec_math_refinement.mont_p_sub.
  finish_mont_trace aj_y_num.
Qed.

Lemma montg_add_jpoint_y_strategy5_correctness : montg_add_jpoint_y_strategy5.
Proof.
  pre_process_default.
  rewrite ec_math_refinement.fp_div2_mont.
  rewrite montg_add_ry_mont.
  finish_spatial_trace.
Qed.

Lemma montg_add_jpoint_y_strategy101_correctness : montg_add_jpoint_y_strategy101.
Proof.
  pre_process_default.
  pose proof (aj_mod_range
    (aj_h2 x1 z1 x2 z2 * aj_h x1 z1 x2 z2)) as Hrange.
  entailer!.
Qed.

Lemma montg_add_jpoint_y_strategy102_correctness : montg_add_jpoint_y_strategy102.
Proof. solve_aj_trace_range aj_right_y. Qed.

Lemma montg_add_jpoint_y_strategy103_correctness : montg_add_jpoint_y_strategy103.
Proof. solve_aj_trace_range aj_left_y. Qed.

Lemma montg_add_jpoint_y_strategy104_correctness : montg_add_jpoint_y_strategy104.
Proof. solve_aj_trace_range aj_y_num. Qed.
