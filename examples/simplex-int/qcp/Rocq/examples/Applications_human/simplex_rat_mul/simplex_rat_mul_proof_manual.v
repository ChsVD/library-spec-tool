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
From SimpleC.EE.Applications_human.simplex_rat_mul Require Import simplex_rat_mul_goal.
From SimpleC.EE.Applications_human.simplex_rat_mul Require Import simplex_rat_mul_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_checked_mul.simplex_checked_mul_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_reduce.simplex_rat_reduce_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_mul.simplex_rat_mul_lib.
Local Open Scope sac.

Lemma proof_of_rat_mul_return_wit_1_out_known_split_goal_1 : rat_mul_return_wit_1_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_rat_mul_return_wit_1_out_known_split_goal_2 : rat_mul_return_wit_1_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros; subst.
  unfold simplex_rat_mul_result. assumption.
Qed.

Lemma proof_of_rat_mul_return_wit_1_out_known_split_goal_3 : rat_mul_return_wit_1_out_known_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry.
  apply (proj2 (simplex_rat_mul_flag_success _ _ _ _)).
  split; congruence.
Qed.

Lemma proof_of_rat_mul_return_wit_1_out_known : rat_mul_return_wit_1_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_mul_return_wit_1_out_known_split_goal_1.
  - Goal_apply proof_of_rat_mul_return_wit_1_out_known_split_goal_2.
  - Goal_apply proof_of_rat_mul_return_wit_1_out_known_split_goal_3.
Qed. 

Lemma proof_of_rat_mul_return_wit_2_out_known_split_goal_1 : rat_mul_return_wit_2_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_rat_mul_return_wit_2_out_known_split_goal_2 : rat_mul_return_wit_2_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros; subst.
  unfold simplex_rat_mul_result. assumption.
Qed.

Lemma proof_of_rat_mul_return_wit_2_out_known_split_goal_3 : rat_mul_return_wit_2_out_known_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry.
  apply (proj2 (simplex_rat_mul_flag_success _ _ _ _)).
  split; congruence.
Qed.

Lemma proof_of_rat_mul_return_wit_2_out_known : rat_mul_return_wit_2_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_mul_return_wit_2_out_known_split_goal_1.
  - Goal_apply proof_of_rat_mul_return_wit_2_out_known_split_goal_2.
  - Goal_apply proof_of_rat_mul_return_wit_2_out_known_split_goal_3.
Qed. 

Lemma proof_of_rat_mul_return_wit_3_out_known_split_goal_1 : rat_mul_return_wit_3_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold simplex_rat_mul_result; congruence).
Qed.

Lemma proof_of_rat_mul_return_wit_3_out_known_split_goal_2 : rat_mul_return_wit_3_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply simplex_rat_mul_flag_success.
  split; congruence.
Qed.

Lemma proof_of_rat_mul_return_wit_3_out_known : rat_mul_return_wit_3_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_mul_return_wit_3_out_known_split_goal_1.
  - Goal_apply proof_of_rat_mul_return_wit_3_out_known_split_goal_2.
Qed. 

Lemma proof_of_rat_mul_return_wit_4_out_known_split_goal_1 : rat_mul_return_wit_4_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold simplex_rat_mul_result; congruence).
Qed.

Lemma proof_of_rat_mul_return_wit_4_out_known_split_goal_2 : rat_mul_return_wit_4_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply simplex_rat_mul_flag_success.
  split; congruence.
Qed.

Lemma proof_of_rat_mul_return_wit_4_out_known : rat_mul_return_wit_4_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_mul_return_wit_4_out_known_split_goal_1.
  - Goal_apply proof_of_rat_mul_return_wit_4_out_known_split_goal_2.
Qed. 

Lemma proof_of_rat_mul_return_wit_5_out_undef_split_goal_1 : rat_mul_return_wit_5_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_rat_mul_return_wit_5_out_undef_split_goal_2 : rat_mul_return_wit_5_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros; subst.
  unfold simplex_rat_mul_result. assumption.
Qed.

Lemma proof_of_rat_mul_return_wit_5_out_undef_split_goal_3 : rat_mul_return_wit_5_out_undef_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry.
  apply (proj2 (simplex_rat_mul_flag_success _ _ _ _)).
  split; congruence.
Qed.

Lemma proof_of_rat_mul_return_wit_5_out_undef : rat_mul_return_wit_5_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_mul_return_wit_5_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_mul_return_wit_5_out_undef_split_goal_2.
  - Goal_apply proof_of_rat_mul_return_wit_5_out_undef_split_goal_3.
Qed. 

Lemma proof_of_rat_mul_return_wit_6_out_undef_split_goal_1 : rat_mul_return_wit_6_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_rat_mul_return_wit_6_out_undef_split_goal_2 : rat_mul_return_wit_6_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros; subst.
  unfold simplex_rat_mul_result. assumption.
Qed.

Lemma proof_of_rat_mul_return_wit_6_out_undef_split_goal_3 : rat_mul_return_wit_6_out_undef_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry.
  apply (proj2 (simplex_rat_mul_flag_success _ _ _ _)).
  split; congruence.
Qed.

Lemma proof_of_rat_mul_return_wit_6_out_undef : rat_mul_return_wit_6_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_mul_return_wit_6_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_mul_return_wit_6_out_undef_split_goal_2.
  - Goal_apply proof_of_rat_mul_return_wit_6_out_undef_split_goal_3.
Qed. 

Lemma proof_of_rat_mul_return_wit_7_out_undef_split_goal_1 : rat_mul_return_wit_7_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold simplex_rat_mul_result; congruence).
Qed.

Lemma proof_of_rat_mul_return_wit_7_out_undef_split_goal_2 : rat_mul_return_wit_7_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply simplex_rat_mul_flag_success.
  split; congruence.
Qed.

Lemma proof_of_rat_mul_return_wit_7_out_undef : rat_mul_return_wit_7_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_mul_return_wit_7_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_mul_return_wit_7_out_undef_split_goal_2.
Qed. 

Lemma proof_of_rat_mul_return_wit_8_out_undef_split_goal_1 : rat_mul_return_wit_8_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold simplex_rat_mul_result; congruence).
Qed.

Lemma proof_of_rat_mul_return_wit_8_out_undef_split_goal_2 : rat_mul_return_wit_8_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply simplex_rat_mul_flag_success.
  split; congruence.
Qed.

Lemma proof_of_rat_mul_return_wit_8_out_undef : rat_mul_return_wit_8_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_mul_return_wit_8_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_mul_return_wit_8_out_undef_split_goal_2.
Qed. 

Lemma proof_of_rat_mul_return_wit_9_out_known_split_goal_1 : rat_mul_return_wit_9_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply (proj2 (simplex_rat_mul_flag_failure_ordered _ _ _ _)).
  right; split; lia.
Qed.

Lemma proof_of_rat_mul_return_wit_9_out_known : rat_mul_return_wit_9_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_mul_return_wit_9_out_known_split_goal_1.
Qed. 

Lemma proof_of_rat_mul_return_wit_10_out_undef_split_goal_1 : rat_mul_return_wit_10_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply (proj2 (simplex_rat_mul_flag_failure_ordered _ _ _ _)).
  right; split; lia.
Qed.

Lemma proof_of_rat_mul_return_wit_10_out_undef : rat_mul_return_wit_10_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_mul_return_wit_10_out_undef_split_goal_1.
Qed. 

Lemma proof_of_rat_mul_return_wit_11_out_known_split_goal_1 : rat_mul_return_wit_11_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply (proj2 (simplex_rat_mul_flag_failure_ordered _ _ _ _)).
  left; lia.
Qed.

Lemma proof_of_rat_mul_return_wit_11_out_known : rat_mul_return_wit_11_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_mul_return_wit_11_out_known_split_goal_1.
Qed. 

Lemma proof_of_rat_mul_return_wit_12_out_undef_split_goal_1 : rat_mul_return_wit_12_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  apply (proj2 (simplex_rat_mul_flag_failure_ordered _ _ _ _)).
  left; lia.
Qed.

Lemma proof_of_rat_mul_return_wit_12_out_undef : rat_mul_return_wit_12_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_mul_return_wit_12_out_undef_split_goal_1.
Qed. 

Lemma proof_of_rat_mul_partial_solve_wit_5_out_known_pure_split_goal_1 : rat_mul_partial_solve_wit_5_out_known_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HF : simplex_rat_mul_flag A_out_known B_out_known C_out_known D_out_known = 1).
  { apply simplex_rat_mul_flag_success. split; lia. }
  pose proof (simplex_rat_mul_reduce_inputs A_out_known B_out_known C_out_known D_out_known
    ltac:(lia) ltac:(lia) HF) as HR.
  dump_pre_spatial.
  change (-2147483647 <= A_out_known * C_out_known).
  exact (proj1 (proj1 HR)).
Qed.

Lemma proof_of_rat_mul_partial_solve_wit_5_out_known_pure : rat_mul_partial_solve_wit_5_out_known_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_mul_partial_solve_wit_5_out_known_pure_split_goal_1.
Qed. 

Lemma proof_of_rat_mul_partial_solve_wit_6_out_undef_pure_split_goal_1 : rat_mul_partial_solve_wit_6_out_undef_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HF : simplex_rat_mul_flag A_out_undef B_out_undef C_out_undef D_out_undef = 1).
  { apply simplex_rat_mul_flag_success. split; lia. }
  pose proof (simplex_rat_mul_reduce_inputs A_out_undef B_out_undef C_out_undef D_out_undef
    ltac:(lia) ltac:(lia) HF) as HR.
  dump_pre_spatial.
  change (-2147483647 <= A_out_undef * C_out_undef).
  exact (proj1 (proj1 HR)).
Qed.

Lemma proof_of_rat_mul_partial_solve_wit_6_out_undef_pure : rat_mul_partial_solve_wit_6_out_undef_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_mul_partial_solve_wit_6_out_undef_pure_split_goal_1.
Qed. 

