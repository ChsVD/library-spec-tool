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
From SimpleC.EE.Applications_human.simplex_checked_add_branches Require Import simplex_checked_add_branches_goal.
From SimpleC.EE.Applications_human.simplex_checked_add_branches Require Import simplex_checked_add_branches_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_checked_add.simplex_checked_add_lib.
Local Open Scope sac.

Lemma proof_of_checked_add_return_wit_1_out_undef_split_goal_1 : checked_add_return_wit_1_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_add_flag_success_iff. lia.
Qed.

Lemma proof_of_checked_add_return_wit_1_out_undef : checked_add_return_wit_1_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_1_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_2_out_known_split_goal_1 : checked_add_return_wit_2_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_add_flag_success_iff. lia.
Qed.

Lemma proof_of_checked_add_return_wit_2_out_known : checked_add_return_wit_2_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_2_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_3_out_known_split_goal_1 : checked_add_return_wit_3_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_add_flag_success_iff. lia.
Qed.

Lemma proof_of_checked_add_return_wit_3_out_known : checked_add_return_wit_3_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_3_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_4_out_undef_split_goal_1 : checked_add_return_wit_4_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_add_flag_success_iff. lia.
Qed.

Lemma proof_of_checked_add_return_wit_4_out_undef : checked_add_return_wit_4_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_4_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_5_out_undef_split_goal_1 : checked_add_return_wit_5_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_add_flag_success_iff. lia.
Qed.

Lemma proof_of_checked_add_return_wit_5_out_undef : checked_add_return_wit_5_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_5_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_6_out_known_split_goal_1 : checked_add_return_wit_6_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_add_flag_success_iff. lia.
Qed.

Lemma proof_of_checked_add_return_wit_6_out_known : checked_add_return_wit_6_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_6_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_7_out_undef_split_goal_1 : checked_add_return_wit_7_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_flag_failure_iff.
  right; right; left; lia.
Qed.

Lemma proof_of_checked_add_return_wit_7_out_undef : checked_add_return_wit_7_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_7_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_8_out_known_split_goal_1 : checked_add_return_wit_8_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_flag_failure_iff.
  right; right; left; lia.
Qed.

Lemma proof_of_checked_add_return_wit_8_out_known : checked_add_return_wit_8_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_8_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_9_out_known_split_goal_1 : checked_add_return_wit_9_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_flag_failure_iff.
  right; right; right; lia.
Qed.

Lemma proof_of_checked_add_return_wit_9_out_known : checked_add_return_wit_9_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_9_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_10_out_undef_split_goal_1 : checked_add_return_wit_10_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_flag_failure_iff.
  right; right; right; lia.
Qed.

Lemma proof_of_checked_add_return_wit_10_out_undef : checked_add_return_wit_10_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_10_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_11_out_undef_split_goal_1 : checked_add_return_wit_11_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_min_rejected.
  left; lia.
Qed.

Lemma proof_of_checked_add_return_wit_11_out_undef : checked_add_return_wit_11_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_11_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_12_out_known_split_goal_1 : checked_add_return_wit_12_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_min_rejected.
  left; lia.
Qed.

Lemma proof_of_checked_add_return_wit_12_out_known : checked_add_return_wit_12_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_12_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_13_out_known_split_goal_1 : checked_add_return_wit_13_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_min_rejected.
  right; lia.
Qed.

Lemma proof_of_checked_add_return_wit_13_out_known : checked_add_return_wit_13_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_13_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_14_out_undef_split_goal_1 : checked_add_return_wit_14_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_min_rejected.
  right; lia.
Qed.

Lemma proof_of_checked_add_return_wit_14_out_undef : checked_add_return_wit_14_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_14_out_undef_split_goal_1.
Qed. 

