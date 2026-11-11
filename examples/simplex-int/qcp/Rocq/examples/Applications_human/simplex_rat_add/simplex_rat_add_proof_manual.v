Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.simplex_rat_add Require Import simplex_rat_add_goal.
From SimpleC.EE.Applications_human.simplex_rat_add Require Import simplex_rat_add_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_checked_mul.simplex_checked_mul_lib.
Require Import SimpleC.EE.Applications_human.simplex_checked_add.simplex_checked_add_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_reduce.simplex_rat_reduce_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_add.simplex_rat_add_lib.
Local Open Scope sac.

Lemma proof_of_rat_add_return_wit_1_out_known_split_goal_1 : rat_add_return_wit_1_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto); reflexivity.
Qed.

Lemma proof_of_rat_add_return_wit_1_out_known_split_goal_2 : rat_add_return_wit_1_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_rat_add_result; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_1_out_known_split_goal_3 : rat_add_return_wit_1_out_known_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_add_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_1_out_known : rat_add_return_wit_1_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_add_return_wit_1_out_known_split_goal_1.
  - Goal_apply proof_of_rat_add_return_wit_1_out_known_split_goal_2.
  - Goal_apply proof_of_rat_add_return_wit_1_out_known_split_goal_3.
Qed. 

Lemma proof_of_rat_add_return_wit_2_out_known_split_goal_1 : rat_add_return_wit_2_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto); reflexivity.
Qed.

Lemma proof_of_rat_add_return_wit_2_out_known_split_goal_2 : rat_add_return_wit_2_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_rat_add_result; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_2_out_known_split_goal_3 : rat_add_return_wit_2_out_known_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_add_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_2_out_known : rat_add_return_wit_2_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_add_return_wit_2_out_known_split_goal_1.
  - Goal_apply proof_of_rat_add_return_wit_2_out_known_split_goal_2.
  - Goal_apply proof_of_rat_add_return_wit_2_out_known_split_goal_3.
Qed. 

Lemma proof_of_rat_add_return_wit_3_out_known_split_goal_1 : rat_add_return_wit_3_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: unfold simplex_rat_add_result; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_3_out_known_split_goal_2 : rat_add_return_wit_3_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: symmetry; apply simplex_rat_add_flag_success; repeat split; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_3_out_known : rat_add_return_wit_3_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_add_return_wit_3_out_known_split_goal_1.
  - Goal_apply proof_of_rat_add_return_wit_3_out_known_split_goal_2.
Qed. 

Lemma proof_of_rat_add_return_wit_4_out_known_split_goal_1 : rat_add_return_wit_4_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: unfold simplex_rat_add_result; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_4_out_known_split_goal_2 : rat_add_return_wit_4_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: symmetry; apply simplex_rat_add_flag_success; repeat split; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_4_out_known : rat_add_return_wit_4_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_add_return_wit_4_out_known_split_goal_1.
  - Goal_apply proof_of_rat_add_return_wit_4_out_known_split_goal_2.
Qed. 

Lemma proof_of_rat_add_return_wit_5_out_undef_split_goal_1 : rat_add_return_wit_5_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto); reflexivity.
Qed.

Lemma proof_of_rat_add_return_wit_5_out_undef_split_goal_2 : rat_add_return_wit_5_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_rat_add_result; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_5_out_undef_split_goal_3 : rat_add_return_wit_5_out_undef_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_add_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_5_out_undef : rat_add_return_wit_5_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_add_return_wit_5_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_add_return_wit_5_out_undef_split_goal_2.
  - Goal_apply proof_of_rat_add_return_wit_5_out_undef_split_goal_3.
Qed. 

Lemma proof_of_rat_add_return_wit_6_out_undef_split_goal_1 : rat_add_return_wit_6_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto); reflexivity.
Qed.

Lemma proof_of_rat_add_return_wit_6_out_undef_split_goal_2 : rat_add_return_wit_6_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_rat_add_result; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_6_out_undef_split_goal_3 : rat_add_return_wit_6_out_undef_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_add_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_6_out_undef : rat_add_return_wit_6_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_add_return_wit_6_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_add_return_wit_6_out_undef_split_goal_2.
  - Goal_apply proof_of_rat_add_return_wit_6_out_undef_split_goal_3.
Qed. 

Lemma proof_of_rat_add_return_wit_7_out_undef_split_goal_1 : rat_add_return_wit_7_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: unfold simplex_rat_add_result; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_7_out_undef_split_goal_2 : rat_add_return_wit_7_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: symmetry; apply simplex_rat_add_flag_success; repeat split; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_7_out_undef : rat_add_return_wit_7_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_add_return_wit_7_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_add_return_wit_7_out_undef_split_goal_2.
Qed. 

Lemma proof_of_rat_add_return_wit_8_out_undef_split_goal_1 : rat_add_return_wit_8_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: unfold simplex_rat_add_result; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_8_out_undef_split_goal_2 : rat_add_return_wit_8_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: symmetry; apply simplex_rat_add_flag_success; repeat split; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_8_out_undef : rat_add_return_wit_8_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_add_return_wit_8_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_add_return_wit_8_out_undef_split_goal_2.
Qed. 

Lemma proof_of_rat_add_return_wit_9_r_eq_x_split_goal_1 : rat_add_return_wit_9_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto); reflexivity.
Qed.

Lemma proof_of_rat_add_return_wit_9_r_eq_x_split_goal_2 : rat_add_return_wit_9_r_eq_x_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_rat_add_result; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_9_r_eq_x_split_goal_3 : rat_add_return_wit_9_r_eq_x_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_add_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_9_r_eq_x : rat_add_return_wit_9_r_eq_x.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_add_return_wit_9_r_eq_x_split_goal_1.
  - Goal_apply proof_of_rat_add_return_wit_9_r_eq_x_split_goal_2.
  - Goal_apply proof_of_rat_add_return_wit_9_r_eq_x_split_goal_3.
Qed. 

Lemma proof_of_rat_add_return_wit_10_r_eq_x_split_goal_1 : rat_add_return_wit_10_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto); reflexivity.
Qed.

Lemma proof_of_rat_add_return_wit_10_r_eq_x_split_goal_2 : rat_add_return_wit_10_r_eq_x_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_rat_add_result; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_10_r_eq_x_split_goal_3 : rat_add_return_wit_10_r_eq_x_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_add_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_10_r_eq_x : rat_add_return_wit_10_r_eq_x.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_add_return_wit_10_r_eq_x_split_goal_1.
  - Goal_apply proof_of_rat_add_return_wit_10_r_eq_x_split_goal_2.
  - Goal_apply proof_of_rat_add_return_wit_10_r_eq_x_split_goal_3.
Qed. 

Lemma proof_of_rat_add_return_wit_11_r_eq_x_split_goal_1 : rat_add_return_wit_11_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: unfold simplex_rat_add_result; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_11_r_eq_x_split_goal_2 : rat_add_return_wit_11_r_eq_x_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: symmetry; apply simplex_rat_add_flag_success; repeat split; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_11_r_eq_x : rat_add_return_wit_11_r_eq_x.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_add_return_wit_11_r_eq_x_split_goal_1.
  - Goal_apply proof_of_rat_add_return_wit_11_r_eq_x_split_goal_2.
Qed. 

Lemma proof_of_rat_add_return_wit_12_r_eq_x_split_goal_1 : rat_add_return_wit_12_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: unfold simplex_rat_add_result; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_12_r_eq_x_split_goal_2 : rat_add_return_wit_12_r_eq_x_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: symmetry; apply simplex_rat_add_flag_success; repeat split; congruence.
Qed.

Lemma proof_of_rat_add_return_wit_12_r_eq_x : rat_add_return_wit_12_r_eq_x.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_add_return_wit_12_r_eq_x_split_goal_1.
  - Goal_apply proof_of_rat_add_return_wit_12_r_eq_x_split_goal_2.
Qed. 

Lemma proof_of_rat_add_return_wit_13_out_known_split_goal_1 : rat_add_return_wit_13_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_add_flag_failure_ordered.
  right; right; right.
  repeat split; lia.
Qed.

Lemma proof_of_rat_add_return_wit_13_out_known : rat_add_return_wit_13_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_return_wit_13_out_known_split_goal_1.
Qed. 

Lemma proof_of_rat_add_return_wit_14_out_undef_split_goal_1 : rat_add_return_wit_14_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_add_flag_failure_ordered.
  right; right; right.
  repeat split; lia.
Qed.

Lemma proof_of_rat_add_return_wit_14_out_undef : rat_add_return_wit_14_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_return_wit_14_out_undef_split_goal_1.
Qed. 

Lemma proof_of_rat_add_return_wit_15_r_eq_x_split_goal_1 : rat_add_return_wit_15_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_add_flag_failure_ordered.
  right; right; right.
  repeat split; lia.
Qed.

Lemma proof_of_rat_add_return_wit_15_r_eq_x : rat_add_return_wit_15_r_eq_x.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_return_wit_15_r_eq_x_split_goal_1.
Qed. 

Lemma proof_of_rat_add_return_wit_16_out_known_split_goal_1 : rat_add_return_wit_16_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_add_flag_failure_ordered.
  right; right; left.
  repeat split; lia.
Qed.

Lemma proof_of_rat_add_return_wit_16_out_known : rat_add_return_wit_16_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_return_wit_16_out_known_split_goal_1.
Qed. 

Lemma proof_of_rat_add_return_wit_17_out_undef_split_goal_1 : rat_add_return_wit_17_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_add_flag_failure_ordered.
  right; right; left.
  repeat split; lia.
Qed.

Lemma proof_of_rat_add_return_wit_17_out_undef : rat_add_return_wit_17_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_return_wit_17_out_undef_split_goal_1.
Qed. 

Lemma proof_of_rat_add_return_wit_18_r_eq_x_split_goal_1 : rat_add_return_wit_18_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_add_flag_failure_ordered.
  right; right; left.
  repeat split; lia.
Qed.

Lemma proof_of_rat_add_return_wit_18_r_eq_x : rat_add_return_wit_18_r_eq_x.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_return_wit_18_r_eq_x_split_goal_1.
Qed. 

Lemma proof_of_rat_add_return_wit_19_out_known_split_goal_1 : rat_add_return_wit_19_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply (proj2 (simplex_rat_add_flag_failure_ordered _ _ _ _)).
  right; left; split; lia.
Qed.

Lemma proof_of_rat_add_return_wit_19_out_known : rat_add_return_wit_19_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_return_wit_19_out_known_split_goal_1.
Qed. 

Lemma proof_of_rat_add_return_wit_20_out_undef_split_goal_1 : rat_add_return_wit_20_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply (proj2 (simplex_rat_add_flag_failure_ordered _ _ _ _)).
  right; left; split; lia.
Qed.

Lemma proof_of_rat_add_return_wit_20_out_undef : rat_add_return_wit_20_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_return_wit_20_out_undef_split_goal_1.
Qed. 

Lemma proof_of_rat_add_return_wit_21_r_eq_x_split_goal_1 : rat_add_return_wit_21_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply (proj2 (simplex_rat_add_flag_failure_ordered _ _ _ _)).
  right; left; split; lia.
Qed.

Lemma proof_of_rat_add_return_wit_21_r_eq_x : rat_add_return_wit_21_r_eq_x.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_return_wit_21_r_eq_x_split_goal_1.
Qed. 

Lemma proof_of_rat_add_return_wit_22_out_known_split_goal_1 : rat_add_return_wit_22_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply (proj2 (simplex_rat_add_flag_failure_ordered _ _ _ _)).
  left; lia.
Qed.

Lemma proof_of_rat_add_return_wit_22_out_known : rat_add_return_wit_22_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_return_wit_22_out_known_split_goal_1.
Qed. 

Lemma proof_of_rat_add_return_wit_23_out_undef_split_goal_1 : rat_add_return_wit_23_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply (proj2 (simplex_rat_add_flag_failure_ordered _ _ _ _)).
  left; lia.
Qed.

Lemma proof_of_rat_add_return_wit_23_out_undef : rat_add_return_wit_23_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_return_wit_23_out_undef_split_goal_1.
Qed. 

Lemma proof_of_rat_add_return_wit_24_r_eq_x_split_goal_1 : rat_add_return_wit_24_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply (proj2 (simplex_rat_add_flag_failure_ordered _ _ _ _)).
  left; lia.
Qed.

Lemma proof_of_rat_add_return_wit_24_r_eq_x : rat_add_return_wit_24_r_eq_x.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_return_wit_24_r_eq_x_split_goal_1.
Qed. 

Lemma proof_of_rat_add_partial_solve_wit_15_out_known_pure_split_goal_1 : rat_add_partial_solve_wit_15_out_known_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hadd : checked_add_flag (A_out_known * E_out_known) (C_out_known * B_out_known) = 1) by congruence.
  apply checked_add_flag_success_iff in Hadd.
  try dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_add_partial_solve_wit_15_out_known_pure : rat_add_partial_solve_wit_15_out_known_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_partial_solve_wit_15_out_known_pure_split_goal_1.
Qed. 

Lemma proof_of_rat_add_partial_solve_wit_16_out_undef_pure_split_goal_1 : rat_add_partial_solve_wit_16_out_undef_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hadd : checked_add_flag (A_out_undef * E_out_undef) (C_out_undef * B_out_undef) = 1) by congruence.
  apply checked_add_flag_success_iff in Hadd.
  try dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_add_partial_solve_wit_16_out_undef_pure : rat_add_partial_solve_wit_16_out_undef_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_partial_solve_wit_16_out_undef_pure_split_goal_1.
Qed. 

Lemma proof_of_rat_add_partial_solve_wit_17_r_eq_x_pure_split_goal_1 : rat_add_partial_solve_wit_17_r_eq_x_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hadd : checked_add_flag (A_r_eq_x * E_r_eq_x) (C_r_eq_x * B_r_eq_x) = 1) by congruence.
  apply checked_add_flag_success_iff in Hadd.
  try dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_add_partial_solve_wit_17_r_eq_x_pure : rat_add_partial_solve_wit_17_r_eq_x_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_add_partial_solve_wit_17_r_eq_x_pure_split_goal_1.
Qed. 

