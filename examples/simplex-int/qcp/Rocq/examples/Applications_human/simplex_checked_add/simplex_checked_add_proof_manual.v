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
From SimpleC.EE.Applications_human.simplex_checked_add Require Import simplex_checked_add_goal.
From SimpleC.EE.Applications_human.simplex_checked_add Require Import simplex_checked_add_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_checked_add.simplex_checked_add_lib.
Local Open Scope sac.

Lemma proof_of_checked_add_return_wit_1_split_goal_1 : checked_add_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_add_flag_success_iff. lia.
Qed.

Lemma proof_of_checked_add_return_wit_1 : checked_add_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_2_split_goal_1 : checked_add_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_add_flag_success_iff. lia.
Qed.

Lemma proof_of_checked_add_return_wit_2 : checked_add_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_2_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_3_split_goal_1 : checked_add_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_add_flag_success_iff. lia.
Qed.

Lemma proof_of_checked_add_return_wit_3 : checked_add_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_3_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_4_split_goal_1 : checked_add_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_add_flag_success_iff. lia.
Qed.

Lemma proof_of_checked_add_return_wit_4 : checked_add_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_4_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_5_split_goal_1 : checked_add_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_add_flag_success_iff. lia.
Qed.

Lemma proof_of_checked_add_return_wit_5 : checked_add_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_5_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_6_split_goal_1 : checked_add_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_add_flag_success_iff. lia.
Qed.

Lemma proof_of_checked_add_return_wit_6 : checked_add_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_6_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_7_split_goal_1 : checked_add_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_flag_failure_iff.
  right; right; left; lia.
Qed.

Lemma proof_of_checked_add_return_wit_7 : checked_add_return_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_7_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_8_split_goal_1 : checked_add_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_flag_failure_iff.
  right; right; left; lia.
Qed.

Lemma proof_of_checked_add_return_wit_8 : checked_add_return_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_8_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_9_split_goal_1 : checked_add_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_flag_failure_iff.
  right; right; right; lia.
Qed.

Lemma proof_of_checked_add_return_wit_9 : checked_add_return_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_9_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_10_split_goal_1 : checked_add_return_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_flag_failure_iff.
  right; right; right; lia.
Qed.

Lemma proof_of_checked_add_return_wit_10 : checked_add_return_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_10_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_11_split_goal_1 : checked_add_return_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_min_rejected.
  left; lia.
Qed.

Lemma proof_of_checked_add_return_wit_11 : checked_add_return_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_11_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_12_split_goal_1 : checked_add_return_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_min_rejected.
  left; lia.
Qed.

Lemma proof_of_checked_add_return_wit_12 : checked_add_return_wit_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_12_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_13_split_goal_1 : checked_add_return_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_min_rejected.
  right; lia.
Qed.

Lemma proof_of_checked_add_return_wit_13 : checked_add_return_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_13_split_goal_1.
Qed. 

Lemma proof_of_checked_add_return_wit_14_split_goal_1 : checked_add_return_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply checked_add_min_rejected.
  right; lia.
Qed.

Lemma proof_of_checked_add_return_wit_14 : checked_add_return_wit_14.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_add_return_wit_14_split_goal_1.
Qed. 

