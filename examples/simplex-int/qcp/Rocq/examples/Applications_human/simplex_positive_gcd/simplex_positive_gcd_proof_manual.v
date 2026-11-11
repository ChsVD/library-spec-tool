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
From SimpleC.EE.Applications_human.simplex_positive_gcd Require Import simplex_positive_gcd_goal.
From SimpleC.EE.Applications_human.simplex_positive_gcd Require Import simplex_positive_gcd_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_positive_gcd.simplex_positive_gcd_lib.
Local Open Scope sac.

Lemma proof_of_positive_gcd_entail_wit_2_split_goal_1 : positive_gcd_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (Z.gcd b (Z.rem a b) = Z.gcd A B).
  rewrite simplex_gcd_rem by assumption.
  assumption.
Qed.

Lemma proof_of_positive_gcd_entail_wit_2_split_goal_2 : positive_gcd_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (simplex_rem_bounds a b ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_positive_gcd_entail_wit_2_split_goal_3 : positive_gcd_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (simplex_rem_bounds a b ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_positive_gcd_entail_wit_2 : positive_gcd_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_positive_gcd_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_positive_gcd_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_positive_gcd_entail_wit_2_split_goal_3.
Qed. 

Lemma proof_of_positive_gcd_return_wit_1_split_goal_1 : positive_gcd_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst b.
  apply (simplex_gcd_exit A B a); assumption.
Qed.

Lemma proof_of_positive_gcd_return_wit_1 : positive_gcd_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_positive_gcd_return_wit_1_split_goal_1.
Qed. 

