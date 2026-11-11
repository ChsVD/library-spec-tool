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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import montg_times_base_point_def.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import montg_times_base_point_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import montg_times_base_point_proof_auto.
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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_ecc_const_table.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_basepoint_mul.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_basepoint_mul.
Local Open Scope sac.

Lemma proof_of_montg_times_base_point_entail_wit_3 : montg_times_base_point_entail_wit_3.
Proof.
  unfold montg_times_base_point_entail_wit_3.
  left; intros.
  rewrite <- (sm2_scalar_chunk_one_from_chunk
    K_non_alias byte_list 0 PreH7 PreH8 PreH9 ltac:(lia)).
  unfold UndefStructPredJPoint, UndefStructPredu32.
  rewrite <- (nested_jpoint_u32_v_addr_eq &( "K1" ) "x").
  rewrite <- (named_jpoint_u32_v_addr_eq "K1" "x").
  rewrite <- (nested_jpoint_u32_v_addr_eq &( "K1" ) "y").
  rewrite <- (named_jpoint_u32_v_addr_eq "K1" "y").
  rewrite <- (nested_jpoint_u32_v_addr_eq &( "K1" ) "z").
  rewrite <- (named_jpoint_u32_v_addr_eq "K1" "z").
  rewrite <- (nested_jpoint_u32_v_addr_eq &( "K2" ) "x").
  rewrite <- (named_jpoint_u32_v_addr_eq "K2" "x").
  rewrite <- (nested_jpoint_u32_v_addr_eq &( "K2" ) "y").
  rewrite <- (named_jpoint_u32_v_addr_eq "K2" "y").
  rewrite <- (nested_jpoint_u32_v_addr_eq &( "K2" ) "z").
  rewrite <- (named_jpoint_u32_v_addr_eq "K2" "z").
  rewrite <- (nested_jpoint_u32_v_addr_eq &( "K3" ) "x").
  rewrite <- (named_jpoint_u32_v_addr_eq "K3" "x").
  rewrite <- (nested_jpoint_u32_v_addr_eq &( "K3" ) "y").
  rewrite <- (named_jpoint_u32_v_addr_eq "K3" "y").
  rewrite <- (nested_jpoint_u32_v_addr_eq &( "K3" ) "z").
  rewrite <- (named_jpoint_u32_v_addr_eq "K3" "z").
  rewrite sizeof_uint64.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_entail_wit_4 : montg_times_base_point_entail_wit_4.
Proof.
  unfold montg_times_base_point_entail_wit_4.
  left; intros.
  pose proof (sm2_inner_add_step_from_chunk
    K_non_alias byte_list 0 i PreH10 PreH11 PreH12
    ltac:(lia) ltac:(lia)) as Hstep.
  replace (8 * 0) with 0 in Hstep by lia.
  replace (0 + 8) with 8 in Hstep by lia.
  rewrite Hstep.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_entail_wit_7 : montg_times_base_point_entail_wit_7.
Proof.
  unfold montg_times_base_point_entail_wit_7.
  left; intros.
  assert (i = 8) by lia.
  subst i.
  subst pk.
  rewrite <- (sm2_scalar_chunk_one_from_chunk
    K_non_alias byte_list 1 PreH10 PreH11 PreH12 ltac:(lia)).
  replace (8 * 1) with 8 by lia.
  replace (8 + 8) with 16 by lia.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_entail_wit_8 : montg_times_base_point_entail_wit_8.
Proof.
  unfold montg_times_base_point_entail_wit_8.
  left; intros.
  pose proof (sm2_inner_add_step_from_chunk
    K_non_alias byte_list 1 i PreH10 PreH11 PreH12
    ltac:(lia) ltac:(lia)) as Hstep.
  replace (8 * 1) with 8 in Hstep by lia.
  replace (8 + 8) with 16 in Hstep by lia.
  rewrite Hstep.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_entail_wit_11 : montg_times_base_point_entail_wit_11.
Proof.
  unfold montg_times_base_point_entail_wit_11.
  left; intros.
  assert (i = 8) by lia.
  subst i.
  subst pk.
  rewrite <- (sm2_scalar_chunk_one_from_chunk
    K_non_alias byte_list 2 PreH10 PreH11 PreH12 ltac:(lia)).
  replace (8 * 2) with 16 by lia.
  replace (16 + 8) with 24 by lia.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_entail_wit_12 : montg_times_base_point_entail_wit_12.
Proof.
  unfold montg_times_base_point_entail_wit_12.
  left; intros.
  pose proof (sm2_inner_add_step_from_chunk
    K_non_alias byte_list 2 i PreH10 PreH11 PreH12
    ltac:(lia) ltac:(lia)) as Hstep.
  replace (8 * 2) with 16 in Hstep by lia.
  replace (16 + 8) with 24 in Hstep by lia.
  rewrite Hstep.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_entail_wit_15 : montg_times_base_point_entail_wit_15.
Proof.
  unfold montg_times_base_point_entail_wit_15.
  left; intros.
  assert (i = 8) by lia.
  subst i.
  subst pk.
  rewrite <- (sm2_scalar_chunk_one_from_chunk
    K_non_alias byte_list 3 PreH10 PreH11 PreH12 ltac:(lia)).
  replace (8 * 3) with 24 by lia.
  replace (24 + 8) with 32 by lia.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_entail_wit_16 : montg_times_base_point_entail_wit_16.
Proof.
  unfold montg_times_base_point_entail_wit_16.
  left; intros.
  pose proof (sm2_inner_add_step_from_chunk
    K_non_alias byte_list 3 i PreH10 PreH11 PreH12
    ltac:(lia) ltac:(lia)) as Hstep.
  replace (8 * 3) with 24 in Hstep by lia.
  replace (24 + 8) with 32 in Hstep by lia.
  rewrite Hstep.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_return_wit_1 : montg_times_base_point_return_wit_1.
Proof.
  unfold montg_times_base_point_return_wit_1.
  left; intros.
  assert (i = 8) by lia.
  subst i.
  subst pk.
  replace 24 with (8 * 3) by lia.
  rewrite sm2_outer_prefix_step by lia.
  replace (8 * (3 + 1)) with 32 by lia.
  rewrite sm2_scalar_prefix_32 by lia.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_1 : montg_times_base_point_which_implies_wit_1.
Proof.
  unfold montg_times_base_point_which_implies_wit_1.
  left; intros.
  sep_apply (store_fn_to_u8_full32 k K_non_alias).
  Intros byte_list.
  Exists byte_list.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_2_split_goal_1 : montg_times_base_point_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_sm2_mont_base_point_table.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_2_split_goal_spatial : montg_times_base_point_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_2 : montg_times_base_point_which_implies_wit_2.
Proof.
  unfold montg_times_base_point_which_implies_wit_2.
  left; intros.
  unfold store_sm2_mont_base_point_table.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_3_split_goal_1 : montg_times_base_point_which_implies_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 0).
  assert (0 <= 0 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_3_split_goal_2 : montg_times_base_point_which_implies_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 0).
  assert (0 <= 0 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_3 : montg_times_base_point_which_implies_wit_3.
Proof.
  unfold montg_times_base_point_which_implies_wit_3.
  left; intros.
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 0).
  assert (0 <= 0 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_4_split_goal_1 : montg_times_base_point_which_implies_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (i + 0)).
  assert (0 <= i + 0 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_4_split_goal_2 : montg_times_base_point_which_implies_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (i + 0)).
  assert (0 <= i + 0 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_4 : montg_times_base_point_which_implies_wit_4.
Proof.
  unfold montg_times_base_point_which_implies_wit_4.
  left; intros.
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (i + 0)).
  assert (0 <= i + 0 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_5_split_goal_1 : montg_times_base_point_which_implies_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (0 + 8)).
  assert (0 <= 0 + 8 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_5_split_goal_2 : montg_times_base_point_which_implies_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (0 + 8)).
  assert (0 <= 0 + 8 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_5 : montg_times_base_point_which_implies_wit_5.
Proof.
  unfold montg_times_base_point_which_implies_wit_5.
  left; intros.
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (0 + 8)).
  assert (0 <= 0 + 8 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_6_split_goal_1 : montg_times_base_point_which_implies_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (i + 8)).
  assert (0 <= i + 8 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_6_split_goal_2 : montg_times_base_point_which_implies_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (i + 8)).
  assert (0 <= i + 8 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_6 : montg_times_base_point_which_implies_wit_6.
Proof.
  unfold montg_times_base_point_which_implies_wit_6.
  left; intros.
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (i + 8)).
  assert (0 <= i + 8 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_7_split_goal_1 : montg_times_base_point_which_implies_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (0 + 16)).
  assert (0 <= 0 + 16 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_7_split_goal_2 : montg_times_base_point_which_implies_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (0 + 16)).
  assert (0 <= 0 + 16 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_7 : montg_times_base_point_which_implies_wit_7.
Proof.
  unfold montg_times_base_point_which_implies_wit_7.
  left; intros.
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (0 + 16)).
  assert (0 <= 0 + 16 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_8_split_goal_1 : montg_times_base_point_which_implies_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (i + 16)).
  assert (0 <= i + 16 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_8_split_goal_2 : montg_times_base_point_which_implies_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (i + 16)).
  assert (0 <= i + 16 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_8 : montg_times_base_point_which_implies_wit_8.
Proof.
  unfold montg_times_base_point_which_implies_wit_8.
  left; intros.
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (i + 16)).
  assert (0 <= i + 16 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_9_split_goal_1 : montg_times_base_point_which_implies_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (0 + 24)).
  assert (0 <= 0 + 24 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_9_split_goal_2 : montg_times_base_point_which_implies_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (0 + 24)).
  assert (0 <= 0 + 24 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_9 : montg_times_base_point_which_implies_wit_9.
Proof.
  unfold montg_times_base_point_which_implies_wit_9.
  left; intros.
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (0 + 24)).
  assert (0 <= 0 + 24 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_10_split_goal_1 : montg_times_base_point_which_implies_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (i + 24)).
  assert (0 <= i + 24 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_10_split_goal_2 : montg_times_base_point_which_implies_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (i + 24)).
  assert (0 <= i + 24 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_10 : montg_times_base_point_which_implies_wit_10.
Proof.
  unfold montg_times_base_point_which_implies_wit_10.
  left; intros.
  subst byteIdx.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (i + 24)).
  assert (0 <= i + 24 < Zlength byte_list) by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_11 : montg_times_base_point_which_implies_wit_11.
Proof.
  unfold montg_times_base_point_which_implies_wit_11.
  left; intros.
  rewrite sm2_scalar_chunk_first_limb.
  replace 16 with (8 * (1 + 1)) by lia.
  pose proof (sm2_outer_prefix_step K_non_alias 1 ltac:(lia)) as Hstep.
  replace (8 * 1) with 8 in Hstep by lia.
  rewrite Hstep.
  reflexivity.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_12 : montg_times_base_point_which_implies_wit_12.
Proof.
  unfold montg_times_base_point_which_implies_wit_12.
  left; intros.
  pose proof (sm2_outer_prefix_step K_non_alias 2 ltac:(lia)) as Hstep.
  replace (8 * 2) with 16 in Hstep by lia.
  replace (8 * (2 + 1)) with 24 in Hstep by lia.
  rewrite Hstep.
  reflexivity.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_13_split_goal_spatial : montg_times_base_point_which_implies_wit_13_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_sm2_mont_base_point_table.
  entailer!.
Qed.

Lemma proof_of_montg_times_base_point_which_implies_wit_13 : montg_times_base_point_which_implies_wit_13.
Proof.
  unfold montg_times_base_point_which_implies_wit_13.
  left; intros.
  unfold store_sm2_mont_base_point_table.
  entailer!.
Qed.
