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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import mul_mod_n_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import mul_mod_n_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Local Open Scope sac.

Lemma proof_of_mul_mod_n_return_wit_1_non_alias_split_goal_1 : mul_mod_n_return_wit_1_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  rewrite u64_list_value_four.
  reflexivity.
Qed.

Lemma proof_of_mul_mod_n_return_wit_1_non_alias_split_goal_2 : mul_mod_n_return_wit_1_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof sm2_n_bounds as [HNpos _].
  pose proof (Z.mod_pos_bound X_non_alias SM2_N_Z HNpos) as [Hlo _].
  replace (X_non_alias * 1) with X_non_alias by ring.
  exact Hlo.
Qed.

Lemma proof_of_mul_mod_n_return_wit_1_non_alias_split_goal_3 : mul_mod_n_return_wit_1_non_alias_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof sm2_n_bounds as [HNpos _].
  pose proof (Z.mod_pos_bound X_non_alias SM2_N_Z HNpos) as [_ Hhi].
  replace (X_non_alias * 1) with X_non_alias by ring.
  exact Hhi.
Qed.

Lemma proof_of_mul_mod_n_return_wit_1_non_alias_split_goal_4 : mul_mod_n_return_wit_1_non_alias_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four.
  rewrite <- PreH10.
  replace (X_non_alias * 1) with X_non_alias by ring.
  rewrite Zmod_small by lia.
  reflexivity.
Qed.

Lemma proof_of_mul_mod_n_return_wit_1_non_alias : mul_mod_n_return_wit_1_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mul_mod_n_return_wit_1_non_alias_split_goal_1.
  - Goal_apply proof_of_mul_mod_n_return_wit_1_non_alias_split_goal_2.
  - Goal_apply proof_of_mul_mod_n_return_wit_1_non_alias_split_goal_3.
  - Goal_apply proof_of_mul_mod_n_return_wit_1_non_alias_split_goal_4.
Qed.

Lemma proof_of_mul_mod_n_return_wit_2_non_alias_split_goal_1 : mul_mod_n_return_wit_2_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  rewrite u64_list_value_four.
  reflexivity.
Qed.

Lemma proof_of_mul_mod_n_return_wit_2_non_alias_split_goal_2 : mul_mod_n_return_wit_2_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof sm2_n_bounds as [HNpos _].
  pose proof (Z.mod_pos_bound Y_non_alias SM2_N_Z HNpos) as [Hlo _].
  replace (1 * Y_non_alias) with Y_non_alias by ring.
  exact Hlo.
Qed.

Lemma proof_of_mul_mod_n_return_wit_2_non_alias_split_goal_3 : mul_mod_n_return_wit_2_non_alias_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof sm2_n_bounds as [HNpos _].
  pose proof (Z.mod_pos_bound Y_non_alias SM2_N_Z HNpos) as [_ Hhi].
  replace (1 * Y_non_alias) with Y_non_alias by ring.
  exact Hhi.
Qed.

Lemma proof_of_mul_mod_n_return_wit_2_non_alias_split_goal_4 : mul_mod_n_return_wit_2_non_alias_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four.
  rewrite <- PreH1.
  replace (1 * Y_non_alias) with Y_non_alias by ring.
  rewrite Zmod_small by lia.
  reflexivity.
Qed.

Lemma proof_of_mul_mod_n_return_wit_2_non_alias : mul_mod_n_return_wit_2_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mul_mod_n_return_wit_2_non_alias_split_goal_1.
  - Goal_apply proof_of_mul_mod_n_return_wit_2_non_alias_split_goal_2.
  - Goal_apply proof_of_mul_mod_n_return_wit_2_non_alias_split_goal_3.
  - Goal_apply proof_of_mul_mod_n_return_wit_2_non_alias_split_goal_4.
Qed.

Lemma proof_of_mul_mod_n_return_wit_3_non_alias_split_goal_1 : mul_mod_n_return_wit_3_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply (sm2n_double_reduction_result
    X_non_alias Y_non_alias R R_2 K K_2).
  - lia.
  - exact PreH6.
  - exact PreH3.
Qed.

Lemma proof_of_mul_mod_n_return_wit_3_non_alias : mul_mod_n_return_wit_3_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mul_mod_n_return_wit_3_non_alias_split_goal_1.
Qed.
