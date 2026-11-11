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
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_is_apoint_zero_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_is_apoint_zero_proof_auto.
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

Lemma proof_of_montg_is_apoint_zero_return_wit_1_split_goal_1 : montg_is_apoint_zero_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply (proj1 (mont_p_eq_zero_iff Y_coords ltac:(lia))).
  assumption.
Qed.

Lemma proof_of_montg_is_apoint_zero_return_wit_1_split_goal_2 : montg_is_apoint_zero_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply (proj1 (mont_p_eq_zero_iff X_coords ltac:(lia))).
  assumption.
Qed.

Lemma proof_of_montg_is_apoint_zero_return_wit_1_split_goal_spatial : montg_is_apoint_zero_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_bn_zero.
  replace (&("BN_ZERO") + 0 * sizeof(UINT64)) with (&("BN_ZERO")) by lia.
  cancel.
Qed.

Lemma proof_of_montg_is_apoint_zero_return_wit_1 : montg_is_apoint_zero_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_montg_is_apoint_zero_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_montg_is_apoint_zero_return_wit_1_split_goal_1.
  - Goal_apply proof_of_montg_is_apoint_zero_return_wit_1_split_goal_2.
Qed. 

Lemma proof_of_montg_is_apoint_zero_return_wit_2 : montg_is_apoint_zero_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (HX : X_coords = 0).
  { apply (proj1 (mont_p_eq_zero_iff X_coords ltac:(lia))); assumption. }
  assert (HY : Y_coords <> 0).
  { intro HY. subst Y_coords. rewrite mont_p_zero in PreH3. contradiction. }
  Right.
  unfold store_mont_afpoint_coords, store_afpoint_fields, store_bn_zero.
  split_pure_spatial.
  unfold store_fp, store_mod.
  entailer!.
  replace (&("BN_ZERO") + 0 * sizeof(UINT64)) with (&("BN_ZERO")) by lia.
  cancel.
  split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_montg_is_apoint_zero_return_wit_3 : montg_is_apoint_zero_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (HX : X_coords <> 0).
  { intro HX. subst X_coords. rewrite mont_p_zero in PreH3. contradiction. }
  Left.
  unfold store_mont_afpoint_coords, store_afpoint_fields, store_bn_zero.
  split_pure_spatial.
  unfold store_fp, store_mod.
  entailer!.
  replace (&("BN_ZERO") + 0 * sizeof(UINT64)) with (&("BN_ZERO")) by lia.
  cancel.
  split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_montg_is_apoint_zero_which_implies_wit_1 : montg_is_apoint_zero_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_montg_is_apoint_zero_derive_point_by_coords : montg_is_apoint_zero_derive_point_by_coords.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_mont_afpoint.
  Intros X Y.
  Exists X Y.
  apply sepcon_cancel_end.
  - cancel (store_mont_afpoint_coords dst_pre X Y).
    cancel store_bn_zero.
  - apply derivable1_wand_sepcon_adjoint.
    LLM_pre_process ltac:(lia || nia || int_auto).
    assert (Hpoint :
      store_mont_afpoint_coords dst_pre X Y |--
      store_mont_afpoint dst_pre P_point).
    { unfold store_mont_afpoint. Exists X Y. entailer!. }
    pose proof (afpoint_represents_infinity_iff X Y P_point H) as Hinf.
    Split.
    * Split.
      -- Intros retval_2.
         assert (Hneq : P_point <> ECInfinity).
         { intro HP. apply H1. apply (proj2 Hinf) in HP. tauto. }
         sep_apply_l_atomic Hpoint.
         Left. Exists 0.
         apply split_pure_and_spatial_goals.
         ++ cancel (store_mont_afpoint dst_pre P_point).
            cancel store_bn_zero.
         ++ entailer!.
      -- Intros retval_2.
         assert (Hneq : P_point <> ECInfinity).
         { intro HP. apply H1. apply (proj2 Hinf) in HP. tauto. }
         sep_apply_l_atomic Hpoint.
         Left. Exists 0.
         apply split_pure_and_spatial_goals.
         ++ cancel (store_mont_afpoint dst_pre P_point).
            cancel store_bn_zero.
         ++ entailer!.
    * Intros retval_2.
      assert (Hinf_point : P_point = ECInfinity).
      { apply (proj1 Hinf). split; assumption. }
      sep_apply_l_atomic Hpoint.
      Right. Exists 1.
      apply split_pure_and_spatial_goals.
      -- cancel (store_mont_afpoint dst_pre P_point).
         cancel store_bn_zero.
      -- entailer!.
Qed. 
