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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import mod_n_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import mod_n_proof_auto.
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

Lemma proof_of_mod_n_entail_wit_4_non_alias_split_goal_1 : mod_n_entail_wit_4_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (u256_of_limbs_range x0 x1 x2 x3
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA.
  lia.
Qed.

Lemma proof_of_mod_n_entail_wit_4_non_alias_split_goal_2 : mod_n_entail_wit_4_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (u256_of_limbs_range x0 x1 x2 x3
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA.
  lia.
Qed.

Lemma proof_of_mod_n_entail_wit_4_non_alias_split_goal_3 : mod_n_entail_wit_4_non_alias_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite u64_list_value_four.
  lia.
Qed.

Lemma proof_of_mod_n_entail_wit_4_non_alias_split_goal_4 : mod_n_entail_wit_4_non_alias_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite u64_list_value_four.
  lia.
Qed.

Lemma proof_of_mod_n_entail_wit_4_non_alias : mod_n_entail_wit_4_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mod_n_entail_wit_4_non_alias_split_goal_1.
  - Goal_apply proof_of_mod_n_entail_wit_4_non_alias_split_goal_2.
  - Goal_apply proof_of_mod_n_entail_wit_4_non_alias_split_goal_3.
  - Goal_apply proof_of_mod_n_entail_wit_4_non_alias_split_goal_4.
Qed.

Lemma proof_of_mod_n_entail_wit_5_in_place_split_goal_1 : mod_n_entail_wit_5_in_place_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (u256_of_limbs_range x0 x1 x2 x3
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA.
  lia.
Qed.

Lemma proof_of_mod_n_entail_wit_5_in_place_split_goal_2 : mod_n_entail_wit_5_in_place_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (u256_of_limbs_range x0 x1 x2 x3
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA.
  lia.
Qed.

Lemma proof_of_mod_n_entail_wit_5_in_place : mod_n_entail_wit_5_in_place.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mod_n_entail_wit_5_in_place_split_goal_1.
  - Goal_apply proof_of_mod_n_entail_wit_5_in_place_split_goal_2.
Qed.

Lemma proof_of_mod_n_return_wit_1_non_alias_split_goal_1 : mod_n_return_wit_1_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_1_non_alias_split_goal_2 : mod_n_return_wit_1_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_1_non_alias_split_goal_3 : mod_n_return_wit_1_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_1_non_alias_split_goal_4 : mod_n_return_wit_1_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_1_non_alias : mod_n_return_wit_1_non_alias.
Proof.
  unfold mod_n_return_wit_1_non_alias.
  right; intros.
  pose proof (u256_of_limbs_range x0 x1 x2 x3
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA.
  pose proof sm2_rhon_limbs as [Hrho Hrho_bounds].
  pose proof sm2_rhon_is_neg_n as Hneg.
  pose proof sm2_n_bounds as HN.
  pose proof sm2_n_more_than_half as Hhalf.
  rewrite <- PreH10 in PreH5.
  assert (HNvalue :
    u256_of_limbs SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z = SM2_N_Z).
  { reflexivity. }
  rewrite u64_list_value_four, HNvalue in PreH9.
  assert (Hcarry : retval_2 = 1) by lia.
  assert (HS : S = A_non_alias - SM2_N_Z) by lia.
  assert (Hmod : Zmod A_non_alias SM2_N_Z = S).
  {
    rewrite sm2_n_reduce_u256_once by lia.
    destruct (A_non_alias <? SM2_N_Z)%Z eqn:Hlt.
    - apply Z.ltb_lt in Hlt; lia.
    - apply Z.ltb_ge in Hlt; lia.
  }
  assert (HSlt : S < SM2_N_Z) by lia.
  assert (HNlist :
    u64_list_value
      (SM2_N0_Z :: SM2_N1_Z :: SM2_N2_Z :: SM2_N3_Z :: nil) = SM2_N_Z).
  { rewrite u64_list_value_four. exact HNvalue. }
  rewrite Hmod.
  entailer!.
Qed.

Lemma proof_of_mod_n_return_wit_2_in_place_split_goal_1 : mod_n_return_wit_2_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_2_in_place_split_goal_2 : mod_n_return_wit_2_in_place_split_goal_2.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_2_in_place_split_goal_3 : mod_n_return_wit_2_in_place_split_goal_3.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_2_in_place_split_goal_4 : mod_n_return_wit_2_in_place_split_goal_4.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_2_in_place : mod_n_return_wit_2_in_place.
Proof.
  unfold mod_n_return_wit_2_in_place.
  right; intros.
  pose proof (u256_of_limbs_range x0 x1 x2 x3
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HA.
  pose proof sm2_rhon_limbs as [Hrho Hrho_bounds].
  pose proof sm2_rhon_is_neg_n as Hneg.
  pose proof sm2_n_bounds as HN.
  pose proof sm2_n_more_than_half as Hhalf.
  rewrite <- PreH10 in PreH5.
  assert (HNvalue :
    u256_of_limbs SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z = SM2_N_Z).
  { reflexivity. }
  rewrite u64_list_value_four, HNvalue in PreH9.
  assert (Hcarry : retval_2 = 1) by lia.
  assert (HS : S = A_in_place - SM2_N_Z) by lia.
  assert (Hmod : Zmod A_in_place SM2_N_Z = S).
  {
    rewrite sm2_n_reduce_u256_once by lia.
    destruct (A_in_place <? SM2_N_Z)%Z eqn:Hlt.
    - apply Z.ltb_lt in Hlt; lia.
    - apply Z.ltb_ge in Hlt; lia.
  }
  assert (HSlt : S < SM2_N_Z) by lia.
  assert (HNlist :
    u64_list_value
      (SM2_N0_Z :: SM2_N1_Z :: SM2_N2_Z :: SM2_N3_Z :: nil) = SM2_N_Z).
  { rewrite u64_list_value_four. exact HNvalue. }
  rewrite Hmod.
  entailer!.
Qed.

Lemma proof_of_mod_n_return_wit_3_non_alias_split_goal_1 : mod_n_return_wit_3_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_3_non_alias_split_goal_2 : mod_n_return_wit_3_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_3_non_alias_split_goal_3 : mod_n_return_wit_3_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_3_non_alias_split_goal_4 : mod_n_return_wit_3_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_3_non_alias_split_goal_spatial : mod_n_return_wit_3_non_alias_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_3_non_alias : mod_n_return_wit_3_non_alias.
Proof.
  unfold mod_n_return_wit_3_non_alias.
  right; intros.
  pose proof sm2_n_bounds as HN.
  assert (HNvalue :
    u256_of_limbs SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z = SM2_N_Z).
  { reflexivity. }
  rewrite <- PreH31 in PreH12.
  rewrite u64_list_value_four, HNvalue in PreH12.
  assert (Hcanonical : 0 <= A_non_alias < SM2_N_Z) by lia.
  assert (HNlist :
    u64_list_value
      (SM2_N0_Z :: SM2_N1_Z :: SM2_N2_Z :: SM2_N3_Z :: nil) = SM2_N_Z).
  { rewrite u64_list_value_four. exact HNvalue. }
  rewrite Z.mod_small by exact Hcanonical.
  assert (Hrho :
    SM2_RHON_Z = u256_of_limbs x0_3 x1_3 x2_3 x3_3) by exact PreH13.
  unfold store_sm2_rhon, store_u256_limbs.
  Exists x0_3 x1_3 x2_3 x3_3.
  entailer!.
Qed. 

Lemma proof_of_mod_n_return_wit_4_in_place_split_goal_1 : mod_n_return_wit_4_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_4_in_place_split_goal_2 : mod_n_return_wit_4_in_place_split_goal_2.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_4_in_place_split_goal_3 : mod_n_return_wit_4_in_place_split_goal_3.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_4_in_place_split_goal_4 : mod_n_return_wit_4_in_place_split_goal_4.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_4_in_place_split_goal_spatial : mod_n_return_wit_4_in_place_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mod_n_return_wit_4_in_place : mod_n_return_wit_4_in_place.
Proof.
  unfold mod_n_return_wit_4_in_place.
  right; intros.
  pose proof sm2_n_bounds as HN.
  assert (HNvalue :
    u256_of_limbs SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z = SM2_N_Z).
  { reflexivity. }
  rewrite <- PreH22 in PreH12.
  rewrite u64_list_value_four, HNvalue in PreH12.
  assert (Hcanonical : 0 <= A_in_place < SM2_N_Z) by lia.
  assert (HNlist :
    u64_list_value
      (SM2_N0_Z :: SM2_N1_Z :: SM2_N2_Z :: SM2_N3_Z :: nil) = SM2_N_Z).
  { rewrite u64_list_value_four. exact HNvalue. }
  rewrite Z.mod_small by exact Hcanonical.
  assert (Hrho :
    SM2_RHON_Z = u256_of_limbs x0_2 x1_2 x2_2 x3_2) by exact PreH13.
  unfold store_sm2_rhon, store_u256_limbs.
  Exists x0_2 x1_2 x2_2 x3_2.
  entailer!.
Qed. 
