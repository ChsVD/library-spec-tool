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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import jacobian_to_affine_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import jacobian_to_affine_proof_auto.
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
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Local Open Scope sac.

Lemma proof_of_jacobian_to_affine_return_wit_1_non_alias_split_goal_1 : jacobian_to_affine_return_wit_1_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply jpoint_to_afpoint_coordinates_nonzero.
  - exact PreH8.
  - lia.
  - exact PreH3.
Qed.

Lemma proof_of_jacobian_to_affine_return_wit_1_non_alias : jacobian_to_affine_return_wit_1_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_jacobian_to_affine_return_wit_1_non_alias_split_goal_1.
Qed. 

Lemma proof_of_jacobian_to_affine_return_wit_2_non_alias_split_goal_1 : jacobian_to_affine_return_wit_2_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst JX_non_alias; subst JY_non_alias; subst JZ_non_alias.
  unfold jpoint_to_afpoint_coordinates.
  left; split.
  - exact (PreH19 eq_refl).
  - unfold afpoint_infinity; split; reflexivity.
Qed.

Lemma proof_of_jacobian_to_affine_return_wit_2_non_alias : jacobian_to_affine_return_wit_2_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_jacobian_to_affine_return_wit_2_non_alias_split_goal_1.
Qed. 

Lemma proof_of_jacobian_to_affine_return_wit_3_non_alias : jacobian_to_affine_return_wit_3_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  pose proof (PreH16 PreH9) as Hcanonical.
  unfold canonical_jpoint_infinity in Hcanonical.
  tauto.
Qed. 

Lemma proof_of_jacobian_to_affine_return_wit_4_non_alias : jacobian_to_affine_return_wit_4_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  pose proof (PreH16 PreH9) as Hcanonical.
  unfold canonical_jpoint_infinity in Hcanonical.
  tauto.
Qed. 

Lemma proof_of_jacobian_to_affine_derive_point_non_alias_by_non_alias : jacobian_to_affine_derive_point_non_alias_by_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_jpoint_with_canonical_infinity at 1.
  Intros JX JY JZ.
  destruct H as [Hrep Hcanonical].
  assert (Hzcanonical :
    JZ = 0 -> canonical_jpoint_infinity JX JY JZ).
  { intros Hz.
    apply Hcanonical.
    apply
      (proj1
         (jpoint_represents_infinity_iff
            JX JY JZ P_point_non_alias Hrep)).
    exact Hz. }
  Exists JX JY JZ.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  Intros RX RY.
  unfold store_jpoint_with_canonical_infinity, store_afpoint.
  Exists JX JY JZ RX RY.
  pose proof
    (jpoint_to_afpoint_coordinates_represents
       JX JY JZ RX RY P_point_non_alias Hrep H) as Haffine.
  entailer!.
Qed. 
