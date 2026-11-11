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
From SimpleC.EE.Applications_human.simplex_rat_compare Require Import simplex_rat_compare_goal.
From SimpleC.EE.Applications_human.simplex_rat_compare Require Import simplex_rat_compare_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_checked_mul.simplex_checked_mul_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_compare.simplex_rat_compare_lib.
Local Open Scope sac.

Lemma proof_of_rat_compare_return_wit_1_out_known_split_goal_1 : rat_compare_return_wit_1_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- _ = simplex_rat_compare_flag ?a ?b ?c ?d =>
      symmetry; apply (proj2 (simplex_rat_compare_flag_success a b c d));
      split; congruence
  end.
Qed.

Lemma proof_of_rat_compare_return_wit_1_out_known_split_goal_2 : rat_compare_return_wit_1_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- _ = simplex_rat_compare_order ?a ?b ?c ?d =>
      symmetry; apply (proj2 (proj2 (proj2 (simplex_rat_compare_order_spec a b c d)))); lia
  end.
Qed.

Lemma proof_of_rat_compare_return_wit_1_out_known : rat_compare_return_wit_1_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_compare_return_wit_1_out_known_split_goal_1.
  - Goal_apply proof_of_rat_compare_return_wit_1_out_known_split_goal_2.
Qed. 

Lemma proof_of_rat_compare_return_wit_2_out_undef_split_goal_1 : rat_compare_return_wit_2_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- _ = simplex_rat_compare_flag ?a ?b ?c ?d =>
      symmetry; apply (proj2 (simplex_rat_compare_flag_success a b c d));
      split; congruence
  end.
Qed.

Lemma proof_of_rat_compare_return_wit_2_out_undef_split_goal_2 : rat_compare_return_wit_2_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- _ = simplex_rat_compare_order ?a ?b ?c ?d =>
      symmetry; apply (proj2 (proj2 (proj2 (simplex_rat_compare_order_spec a b c d)))); lia
  end.
Qed.

Lemma proof_of_rat_compare_return_wit_2_out_undef : rat_compare_return_wit_2_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_compare_return_wit_2_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_compare_return_wit_2_out_undef_split_goal_2.
Qed. 

Lemma proof_of_rat_compare_return_wit_3_out_known_split_goal_1 : rat_compare_return_wit_3_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- _ = simplex_rat_compare_flag ?a ?b ?c ?d =>
      symmetry; apply (proj2 (simplex_rat_compare_flag_success a b c d));
      split; congruence
  end.
Qed.

Lemma proof_of_rat_compare_return_wit_3_out_known_split_goal_2 : rat_compare_return_wit_3_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- _ = simplex_rat_compare_order ?a ?b ?c ?d =>
      symmetry; apply (proj2 (proj1 (simplex_rat_compare_order_spec a b c d))); lia
  end.
Qed.

Lemma proof_of_rat_compare_return_wit_3_out_known : rat_compare_return_wit_3_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_compare_return_wit_3_out_known_split_goal_1.
  - Goal_apply proof_of_rat_compare_return_wit_3_out_known_split_goal_2.
Qed. 

Lemma proof_of_rat_compare_return_wit_4_out_undef_split_goal_1 : rat_compare_return_wit_4_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- _ = simplex_rat_compare_flag ?a ?b ?c ?d =>
      symmetry; apply (proj2 (simplex_rat_compare_flag_success a b c d));
      split; congruence
  end.
Qed.

Lemma proof_of_rat_compare_return_wit_4_out_undef_split_goal_2 : rat_compare_return_wit_4_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- _ = simplex_rat_compare_order ?a ?b ?c ?d =>
      symmetry; apply (proj2 (proj1 (simplex_rat_compare_order_spec a b c d))); lia
  end.
Qed.

Lemma proof_of_rat_compare_return_wit_4_out_undef : rat_compare_return_wit_4_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_compare_return_wit_4_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_compare_return_wit_4_out_undef_split_goal_2.
Qed. 

Lemma proof_of_rat_compare_return_wit_5_out_known_split_goal_1 : rat_compare_return_wit_5_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- _ = simplex_rat_compare_flag ?a ?b ?c ?d =>
      symmetry; apply (proj2 (simplex_rat_compare_flag_success a b c d));
      split; congruence
  end.
Qed.

Lemma proof_of_rat_compare_return_wit_5_out_known_split_goal_2 : rat_compare_return_wit_5_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- _ = simplex_rat_compare_order ?a ?b ?c ?d =>
      symmetry; apply (proj2 (proj1 (proj2 (simplex_rat_compare_order_spec a b c d)))); lia
  end.
Qed.

Lemma proof_of_rat_compare_return_wit_5_out_known : rat_compare_return_wit_5_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_compare_return_wit_5_out_known_split_goal_1.
  - Goal_apply proof_of_rat_compare_return_wit_5_out_known_split_goal_2.
Qed. 

Lemma proof_of_rat_compare_return_wit_6_out_undef_split_goal_1 : rat_compare_return_wit_6_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- _ = simplex_rat_compare_flag ?a ?b ?c ?d =>
      symmetry; apply (proj2 (simplex_rat_compare_flag_success a b c d));
      split; congruence
  end.
Qed.

Lemma proof_of_rat_compare_return_wit_6_out_undef_split_goal_2 : rat_compare_return_wit_6_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- _ = simplex_rat_compare_order ?a ?b ?c ?d =>
      symmetry; apply (proj2 (proj1 (proj2 (simplex_rat_compare_order_spec a b c d)))); lia
  end.
Qed.

Lemma proof_of_rat_compare_return_wit_6_out_undef : rat_compare_return_wit_6_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_compare_return_wit_6_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_compare_return_wit_6_out_undef_split_goal_2.
Qed. 

Lemma proof_of_rat_compare_return_wit_7_out_known_split_goal_1 : rat_compare_return_wit_7_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry.
  apply (proj2 (simplex_rat_compare_flag_failure_ordered _ _ _ _)).
  right; split; lia.
Qed.

Lemma proof_of_rat_compare_return_wit_7_out_known : rat_compare_return_wit_7_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_compare_return_wit_7_out_known_split_goal_1.
Qed. 

Lemma proof_of_rat_compare_return_wit_8_out_undef_split_goal_1 : rat_compare_return_wit_8_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry.
  apply (proj2 (simplex_rat_compare_flag_failure_ordered _ _ _ _)).
  right; split; lia.
Qed.

Lemma proof_of_rat_compare_return_wit_8_out_undef : rat_compare_return_wit_8_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_compare_return_wit_8_out_undef_split_goal_1.
Qed. 

Lemma proof_of_rat_compare_return_wit_9_out_known_split_goal_1 : rat_compare_return_wit_9_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry.
  apply (proj2 (simplex_rat_compare_flag_failure_ordered _ _ _ _)).
  left; lia.
Qed.

Lemma proof_of_rat_compare_return_wit_9_out_known : rat_compare_return_wit_9_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_compare_return_wit_9_out_known_split_goal_1.
Qed. 

Lemma proof_of_rat_compare_return_wit_10_out_undef_split_goal_1 : rat_compare_return_wit_10_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry.
  apply (proj2 (simplex_rat_compare_flag_failure_ordered _ _ _ _)).
  left; lia.
Qed.

Lemma proof_of_rat_compare_return_wit_10_out_undef : rat_compare_return_wit_10_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_compare_return_wit_10_out_undef_split_goal_1.
Qed. 

