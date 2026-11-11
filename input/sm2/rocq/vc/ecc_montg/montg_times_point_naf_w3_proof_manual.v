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
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_times_point_naf_w3_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_times_point_naf_w3_proof_auto.
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

Lemma proof_of_montg_times_point_naf_w3_safety_wit_10_non_alias_split_goal_1 : montg_times_point_naf_w3_safety_wit_10_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_safety_wit_10_non_alias : montg_times_point_naf_w3_safety_wit_10_non_alias.
Proof.
  aggressive_pre_process.
  unfold wnaf3_digit in PreH5.
  repeat destruct PreH5 as [-> | PreH5]; try lia.
  all: entailer!; lia.
Qed.

Lemma proof_of_montg_times_point_naf_w3_safety_wit_18_non_alias_split_goal_1 : montg_times_point_naf_w3_safety_wit_18_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_safety_wit_18_non_alias : montg_times_point_naf_w3_safety_wit_18_non_alias.
Proof.
  aggressive_pre_process.
  unfold wnaf3_digit in PreH9.
  repeat destruct PreH9 as [-> | PreH9]; try lia.
  all: entailer!; lia.
Qed.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_10_non_alias_split_goal_1 : montg_times_point_naf_w3_entail_wit_10_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_10_non_alias_split_goal_2 : montg_times_point_naf_w3_entail_wit_10_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_10_non_alias_split_goal_3 : montg_times_point_naf_w3_entail_wit_10_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_10_non_alias : montg_times_point_naf_w3_entail_wit_10_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrange : store_fn k_pre K_non_alias |--
    “ 0 <= K_non_alias < SM2_N_Z ”).
  {
    unfold store_fn, store_mod.
    apply coq_prop_andp_left; intros Hbounds.
    dump_pre_spatial.
    exact Hbounds.
  }
  prop_apply_p Hrange.
  Intros_p HK.
  pose proof
    (wnaf3_last_suffix_value K_non_alias initial_digits PreH4)
    as Hlast.
  unfold WNAF3_LENGTH in Hlast.
  assert (Hsuffix :
    wnaf3_value (sublist 256 257 initial_digits) = first_digit).
  { rewrite Hlast. symmetry. exact PreH3. }
  entailer!.
  all: rewrite Hsuffix; try reflexivity; lia.
Qed.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_13_non_alias_split_goal_1 : montg_times_point_naf_w3_entail_wit_13_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_13_non_alias_split_goal_2 : montg_times_point_naf_w3_entail_wit_13_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_13_non_alias_split_goal_3 : montg_times_point_naf_w3_entail_wit_13_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_13_non_alias : montg_times_point_naf_w3_entail_wit_13_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrange : store_fn k_pre K_non_alias |--
    “ 0 <= K_non_alias < SM2_N_Z ”).
  {
    unfold store_fn, store_mod.
    apply coq_prop_andp_left; intros Hbounds.
    dump_pre_spatial.
    exact Hbounds.
  }
  prop_apply_p Hrange.
  Intros_p HK.
  pose proof
    (wnaf3_last_suffix_value K_non_alias initial_digits PreH5)
    as Hlast.
  unfold WNAF3_LENGTH in Hlast.
  assert (Hsuffix :
    wnaf3_value (sublist 256 257 initial_digits) = first_digit).
  { rewrite Hlast. symmetry. exact PreH4. }
  entailer!.
  all: pose proof
    (wnaf3_suffix_nonnegative K_non_alias initial_digits 256
      (proj1 HK) PreH5 ltac:(unfold WNAF3_LENGTH; lia))
    as Hnonnegative.
  all: unfold WNAF3_LENGTH in Hnonnegative.
  all: exfalso; rewrite Hsuffix in Hnonnegative; lia.
Qed.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_14_non_alias_split_goal_1 : montg_times_point_naf_w3_entail_wit_14_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_14_non_alias_split_goal_2 : montg_times_point_naf_w3_entail_wit_14_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_14_non_alias_split_goal_3 : montg_times_point_naf_w3_entail_wit_14_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_14_non_alias : montg_times_point_naf_w3_entail_wit_14_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrange : store_fn k_pre K_non_alias |--
    “ 0 <= K_non_alias < SM2_N_Z ”).
  {
    unfold store_fn, store_mod.
    apply coq_prop_andp_left; intros Hbounds.
    dump_pre_spatial.
    exact Hbounds.
  }
  prop_apply_p Hrange.
  Intros_p HK.
  pose proof
    (wnaf3_last_suffix_value K_non_alias initial_digits PreH4)
    as Hlast.
  unfold WNAF3_LENGTH in Hlast.
  assert (Hsuffix :
    wnaf3_value (sublist 256 257 initial_digits) = first_digit).
  { rewrite Hlast. symmetry. exact PreH3. }
  assert (Hdigit : first_digit = 0) by lia.
  subst first_digit.
  entailer!.
  rewrite Hsuffix, Hdigit, sm2_point_mul_zero.
  reflexivity.
Qed.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_19_non_alias_split_goal_1 : montg_times_point_naf_w3_entail_wit_19_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_19_non_alias_split_goal_2 : montg_times_point_naf_w3_entail_wit_19_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_19_non_alias : montg_times_point_naf_w3_entail_wit_19_non_alias.
Proof.
  aggressive_pre_process.
  - pose proof
      (wnaf3_suffix_step K_non_alias digits i PreH5
        ltac:(unfold WNAF3_LENGTH; lia))
      as Hstep.
    pose proof
      (wnaf3_suffix_nonnegative K_non_alias digits i PreH10 PreH5
        ltac:(unfold WNAF3_LENGTH; lia))
      as Hnonnegative.
    unfold WNAF3_LENGTH in Hstep, Hnonnegative.
    rewrite PreH13, Hstep, <- PreH2.
    rewrite <- sm2_point_mul_two.
    rewrite <- sm2_point_mul_mul by lia.
    rewrite <- sm2_point_mul_add by lia.
    f_equal; ring.
  - pose proof
      (wnaf3_suffix_nonnegative K_non_alias digits i PreH10 PreH5
        ltac:(unfold WNAF3_LENGTH; lia))
      as Hnonnegative.
    unfold WNAF3_LENGTH in Hnonnegative.
    exact Hnonnegative.
Qed.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_23_non_alias_split_goal_1 : montg_times_point_naf_w3_entail_wit_23_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_23_non_alias_split_goal_2 : montg_times_point_naf_w3_entail_wit_23_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_23_non_alias : montg_times_point_naf_w3_entail_wit_23_non_alias.
Proof.
  aggressive_pre_process.
  - pose proof
      (wnaf3_suffix_step K_non_alias digits i PreH8
        ltac:(unfold WNAF3_LENGTH; lia))
      as Hstep.
    pose proof
      (wnaf3_suffix_nonnegative K_non_alias digits i PreH13 PreH8
        ltac:(unfold WNAF3_LENGTH; lia))
      as Htarget_nonnegative.
    unfold WNAF3_LENGTH in Hstep, Htarget_nonnegative.
    rewrite PreH16, Hstep, <- PreH5.
    rewrite <- sm2_point_mul_two.
    rewrite <- sm2_point_mul_mul by lia.
    replace (wnaf3_value (sublist (i + 1) 257 digits) * 2)
      with ((digit + 2 * wnaf3_value (sublist (i + 1) 257 digits)) +
        (-digit)) by ring.
    rewrite sm2_point_mul_add by lia.
    rewrite <- sm2_point_add_associative.
    rewrite sm2_point_add_negate_right, sm2_point_add_infinity_right.
    reflexivity.
  - pose proof
      (wnaf3_suffix_nonnegative K_non_alias digits i PreH13 PreH8
        ltac:(unfold WNAF3_LENGTH; lia))
      as Hnonnegative.
    unfold WNAF3_LENGTH in Hnonnegative.
    exact Hnonnegative.
Qed.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_24_non_alias_split_goal_1 : montg_times_point_naf_w3_entail_wit_24_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_24_non_alias_split_goal_2 : montg_times_point_naf_w3_entail_wit_24_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_24_non_alias : montg_times_point_naf_w3_entail_wit_24_non_alias.
Proof.
  aggressive_pre_process.
  - pose proof
      (wnaf3_suffix_step K_non_alias digits i PreH4
        ltac:(unfold WNAF3_LENGTH; lia))
      as Hstep.
    unfold WNAF3_LENGTH in Hstep.
    rewrite PreH12, Hstep, <- PreH1, PreH13.
    rewrite <- sm2_point_mul_two.
    rewrite <- sm2_point_mul_mul by lia.
    f_equal; ring.
  - pose proof
      (wnaf3_suffix_nonnegative K_non_alias digits i PreH9 PreH4
        ltac:(unfold WNAF3_LENGTH; lia))
      as Hnonnegative.
    unfold WNAF3_LENGTH in Hnonnegative.
    exact Hnonnegative.
Qed.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_25_1_non_alias_split_goal_1 : montg_times_point_naf_w3_entail_wit_25_1_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_25_1_non_alias : montg_times_point_naf_w3_entail_wit_25_1_non_alias.
Proof.
  aggressive_pre_process.
  replace (i - 1 + 1) with i by lia.
  exact PreH1.
Qed.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_25_2_non_alias_split_goal_1 : montg_times_point_naf_w3_entail_wit_25_2_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_25_2_non_alias : montg_times_point_naf_w3_entail_wit_25_2_non_alias.
Proof.
  aggressive_pre_process.
  replace (i - 1 + 1) with i by lia.
  exact PreH1.
Qed.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_25_3_non_alias_split_goal_1 : montg_times_point_naf_w3_entail_wit_25_3_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_25_3_non_alias : montg_times_point_naf_w3_entail_wit_25_3_non_alias.
Proof.
  aggressive_pre_process.
  replace (i - 1 + 1) with i by lia.
  exact PreH1.
Qed.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_26_non_alias_split_goal_1 : montg_times_point_naf_w3_entail_wit_26_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_entail_wit_26_non_alias : montg_times_point_naf_w3_entail_wit_26_non_alias.
Proof.
  aggressive_pre_process.
  assert (i = -1) by lia; subst i.
  pose proof (wnaf3_representation_length _ _ PreH6) as Hlen.
  pose proof (wnaf3_representation_value _ _ PreH6) as Hvalue.
  unfold WNAF3_LENGTH in Hlen.
  assert (Hsub : sublist 0 257 digits = digits).
  {
    pose proof (sublist_app_exact1 digits nil) as Hsub0.
    rewrite app_nil_r in Hsub0.
    rewrite Hlen in Hsub0.
    exact Hsub0.
  }
  replace (-1 + 1) with 0 in PreH7 by lia.
  rewrite Hsub, Hvalue in PreH7.
  exact PreH7.
Qed.

Lemma proof_of_montg_times_point_naf_w3_which_implies_wit_1_split_goal_1 : montg_times_point_naf_w3_which_implies_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_which_implies_wit_1 : montg_times_point_naf_w3_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  destruct PreH2 as [Hlength [Hdigits Hrest]].
  rewrite PreH1.
  apply Hdigits.
  unfold WNAF3_LENGTH in Hlength; lia.
Qed.

Lemma proof_of_montg_times_point_naf_w3_which_implies_wit_2_split_goal_1 : montg_times_point_naf_w3_which_implies_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_montg_times_point_naf_w3_which_implies_wit_2 : montg_times_point_naf_w3_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  destruct PreH4 as [Hlength [Hdigits Hrest]].
  rewrite PreH1.
  apply Hdigits.
  unfold WNAF3_LENGTH in Hlength; lia.
Qed.
