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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import pow_mod_p_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import pow_mod_p_proof_auto.
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

Lemma proof_of_pow_mod_p_return_wit_1_non_alias_split_goal_1 : pow_mod_p_return_wit_1_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four.
  lia.
Qed.

Lemma proof_of_pow_mod_p_return_wit_1_non_alias_split_goal_2 : pow_mod_p_return_wit_1_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.mul_1_l, Zmod_small by (cbv [SM2_P_Z]; lia).
  lia.
Qed.

Lemma proof_of_pow_mod_p_return_wit_1_non_alias_split_goal_3 : pow_mod_p_return_wit_1_non_alias_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_pow_mod_p_return_wit_1_non_alias_split_goal_4 : pow_mod_p_return_wit_1_non_alias_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four, Z.mul_1_l, Zmod_small by lia.
  lia.
Qed.

Lemma proof_of_pow_mod_p_return_wit_1_non_alias : pow_mod_p_return_wit_1_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pow_mod_p_return_wit_1_non_alias_split_goal_1.
  - Goal_apply proof_of_pow_mod_p_return_wit_1_non_alias_split_goal_2.
  - Goal_apply proof_of_pow_mod_p_return_wit_1_non_alias_split_goal_3.
  - Goal_apply proof_of_pow_mod_p_return_wit_1_non_alias_split_goal_4.
Qed. 

Lemma proof_of_pow_mod_p_return_wit_2_non_alias : pow_mod_p_return_wit_2_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hres :
    Zout = Zmod (X_non_alias * X_non_alias) SM2_P_Z).
  {
    symmetry.
    apply (canonical_residue_from_decomposition
      SM2_P_Z (X_non_alias * X_non_alias) Zout K).
    - cbv [SM2_P_Z]. lia.
    - exact (conj PreH4 PreH5).
    - exact PreH6.
  }
  rewrite Hres.
  unfold store_fp, store_mod, store_u256.
  entailer!.
  replace (&(x_pre # "u32" ->ₛ "v") + 0 * sizeof(UINT64))
    with (&(x_pre # "u32" ->ₛ "v")) by lia.
  reflexivity.
Qed. 
