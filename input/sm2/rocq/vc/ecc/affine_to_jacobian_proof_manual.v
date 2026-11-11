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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import affine_to_jacobian_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import affine_to_jacobian_proof_auto.
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

Lemma proof_of_affine_to_jacobian_return_wit_1_split_goal_1 : affine_to_jacobian_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold afpoint_to_jpoint_coordinates.
  right.
  split.
  - right. exact PreH15.
  - repeat split; reflexivity.
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_1_split_goal_2 : affine_to_jacobian_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_1_split_goal_3 : affine_to_jacobian_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_1_split_goal_4 : affine_to_jacobian_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_1_split_goal_5 : affine_to_jacobian_return_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_1_split_goal_6 : affine_to_jacobian_return_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_1_split_goal_7 : affine_to_jacobian_return_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_1 : affine_to_jacobian_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_1_split_goal_1.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_1_split_goal_2.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_1_split_goal_3.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_1_split_goal_4.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_1_split_goal_5.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_1_split_goal_6.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_1_split_goal_7.
Qed. 

Lemma proof_of_affine_to_jacobian_return_wit_2_split_goal_1 : affine_to_jacobian_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold afpoint_to_jpoint_coordinates.
  right.
  split.
  - left. exact PreH15.
  - repeat split; reflexivity.
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_2_split_goal_2 : affine_to_jacobian_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_2_split_goal_3 : affine_to_jacobian_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_2_split_goal_4 : affine_to_jacobian_return_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_2_split_goal_5 : affine_to_jacobian_return_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_2_split_goal_6 : affine_to_jacobian_return_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_2_split_goal_7 : affine_to_jacobian_return_wit_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_2 : affine_to_jacobian_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_2_split_goal_1.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_2_split_goal_2.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_2_split_goal_3.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_2_split_goal_4.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_2_split_goal_5.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_2_split_goal_6.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_2_split_goal_7.
Qed. 

Lemma proof_of_affine_to_jacobian_return_wit_3_split_goal_1 : affine_to_jacobian_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  unfold afpoint_to_jpoint_coordinates, afpoint_infinity,
    canonical_jpoint_infinity.
  left.
  repeat split; try assumption; reflexivity.
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_3_split_goal_spatial : affine_to_jacobian_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  rewrite PreH1, PreH6, PreH11.
  unfold store_jpoint_zero, store_jpoint_fields,
    store_fp, store_mod, store_u256.
  entailer!.
  csimpl.
  cancel.
Qed.

Lemma proof_of_affine_to_jacobian_return_wit_3 : affine_to_jacobian_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_affine_to_jacobian_return_wit_3_split_goal_1.
Qed. 

Lemma proof_of_affine_to_jacobian_derive_point_non_alias_by_non_alias : affine_to_jacobian_derive_point_non_alias_by_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_afpoint at 1.
  Intros X Y.
  Exists X Y.
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    Intros RX RY RZ.
    unfold store_afpoint, store_jpoint_with_canonical_infinity.
    Exists X Y RX RY RZ.
    pose proof
      (afpoint_to_jpoint_coordinates_represents_canonical
         X Y RX RY RZ P_point_non_alias H H0) as HJ.
    entailer!.
Qed. 
