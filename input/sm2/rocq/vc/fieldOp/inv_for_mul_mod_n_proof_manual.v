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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import inv_for_mul_mod_n_def.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import inv_for_mul_mod_n_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import inv_for_mul_mod_n_proof_auto.
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

Lemma proof_of_inv_for_mul_mod_n_return_wit_1_non_alias_split_goal_1 : inv_for_mul_mod_n_return_wit_1_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct sm2n_montgomery_parameters_valid as [_ Hgcd].
  eapply (unscale_inverse_product_mod_one
    SM2_N_Z A_non_alias Znon R K1non K2).
  - pose proof sm2_n_bounds. lia.
  - exact Hgcd.
  - exact PreH24.
  - replace (Znon * 1) with Znon in PreH3 by ring.
    exact PreH3.
Qed.

Lemma proof_of_inv_for_mul_mod_n_return_wit_1_non_alias : inv_for_mul_mod_n_return_wit_1_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_inv_for_mul_mod_n_return_wit_1_non_alias_split_goal_1.
Qed. 

Lemma proof_of_inv_for_mul_mod_n_return_wit_2_in_place_split_goal_1 : inv_for_mul_mod_n_return_wit_2_in_place_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct sm2n_montgomery_parameters_valid as [_ Hgcd].
  eapply (unscale_inverse_product_mod_one
    SM2_N_Z A_in_place Zin R K1in K2).
  - pose proof sm2_n_bounds. lia.
  - exact Hgcd.
  - exact PreH16.
  - replace (Zin * 1) with Zin in PreH3 by ring.
    exact PreH3.
Qed.

Lemma proof_of_inv_for_mul_mod_n_return_wit_2_in_place : inv_for_mul_mod_n_return_wit_2_in_place.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_inv_for_mul_mod_n_return_wit_2_in_place_split_goal_1.
Qed. 

Lemma proof_of_inv_for_mul_mod_n_partial_solve_wit_3_non_alias_pure_split_goal_1 : inv_for_mul_mod_n_partial_solve_wit_3_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_inv_for_mul_mod_n_partial_solve_wit_3_non_alias_pure : inv_for_mul_mod_n_partial_solve_wit_3_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia).
Qed. 

Lemma proof_of_inv_for_mul_mod_n_partial_solve_wit_4_in_place_pure_split_goal_1 : inv_for_mul_mod_n_partial_solve_wit_4_in_place_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_inv_for_mul_mod_n_partial_solve_wit_4_in_place_pure : inv_for_mul_mod_n_partial_solve_wit_4_in_place_pure.
Proof.
  LLM_pre_process ltac:(lia).
Qed. 
