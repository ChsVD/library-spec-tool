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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import sub_mod_p_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import sub_mod_p_proof_auto.
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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement.
Local Open Scope sac.

Lemma proof_of_sub_mod_p_return_wit_1_non_alias_split_goal_1 : sub_mod_p_return_wit_1_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_1_non_alias_split_goal_2 : sub_mod_p_return_wit_1_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_1_non_alias_split_goal_3 : sub_mod_p_return_wit_1_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_1_non_alias : sub_mod_p_return_wit_1_non_alias.
Proof.
  unfold sub_mod_p_return_wit_1_non_alias.
  right; intros.
  repeat first [rewrite Znth0_cons in * | rewrite Znth_cons in * by lia].
  close_sub_mod_p_borrow
    A_non_alias B_non_alias x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
    out retval out_2 retval_2 out_3 retval_3 out_4 retval_4
    out_5 retval_5 out_6 retval_6 out_7 retval_7 out_8 retval_8
    PreH41 PreH36 PreH31 PreH26 PreH42 PreH51 PreH15 PreH10 PreH5.
Qed. 

Lemma proof_of_sub_mod_p_return_wit_2_r_eq_a_split_goal_1 : sub_mod_p_return_wit_2_r_eq_a_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_2_r_eq_a_split_goal_2 : sub_mod_p_return_wit_2_r_eq_a_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_2_r_eq_a_split_goal_3 : sub_mod_p_return_wit_2_r_eq_a_split_goal_3.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_2_r_eq_a : sub_mod_p_return_wit_2_r_eq_a.
Proof.
  unfold sub_mod_p_return_wit_2_r_eq_a.
  right; intros.
  repeat first [rewrite Znth0_cons in * | rewrite Znth_cons in * by lia].
  close_sub_mod_p_borrow
    A_r_eq_a B_r_eq_a x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
    out retval out_2 retval_2 out_3 retval_3 out_4 retval_4
    out_5 retval_5 out_6 retval_6 out_7 retval_7 out_8 retval_8
    PreH41 PreH36 PreH31 PreH26 PreH42 PreH51 PreH15 PreH10 PreH5.
Qed. 

Lemma proof_of_sub_mod_p_return_wit_3_r_eq_b_split_goal_1 : sub_mod_p_return_wit_3_r_eq_b_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_3_r_eq_b_split_goal_2 : sub_mod_p_return_wit_3_r_eq_b_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_3_r_eq_b_split_goal_3 : sub_mod_p_return_wit_3_r_eq_b_split_goal_3.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_3_r_eq_b : sub_mod_p_return_wit_3_r_eq_b.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat first [rewrite Znth0_cons in * | rewrite Znth_cons in * by lia].
  rewrite (unsigned_lnot_u64 x0_2 ltac:(lia)) in PreH41.
  rewrite (unsigned_lnot_u64 x1_2 ltac:(lia)) in PreH36.
  rewrite (unsigned_lnot_u64 x2_2 ltac:(lia)) in PreH31.
  rewrite (unsigned_lnot_u64 x3_2 ltac:(lia)) in PreH26.
  assert (Hsub :
    A_r_eq_b + U256_MOD - B_r_eq_b =
      u256_of_limbs out out_2 out_3 out_4 + retval_4 * U256_MOD).
  {
    rewrite PreH51, PreH42.
    cbv [u256_of_limbs U64_MOD U256_MOD] in *.
    lia.
  }
  pose proof
    (u256_add_carry_chain
      out out_2 out_3 out_4
      SM2_P_LIMB_0 SM2_P_LIMB_1 SM2_P_LIMB_2 SM2_P_LIMB_3
      out_5 out_6 out_7 out_8 retval_5 retval_6 retval_7 retval_8
      ltac:(lia) PreH15 PreH10 PreH5) as Hadd.
  pose proof sm2_p_limbs as
    (Hp0 & Hp1 & Hp2 & Hp3 & Hpvalue).
  rewrite <- Hpvalue in Hadd.
  pose proof
    (u256_of_limbs_range out out_2 out_3 out_4
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof
    (u256_of_limbs_range out_5 out_6 out_7 out_8
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HR.
  pose proof sm2_p_montgomery_bounds as HPbounds.
  assert (Hlt : A_r_eq_b < B_r_eq_b) by nia.
  assert (Hcarry : retval_8 = 1) by nia.
  assert (Hvalue :
    u256_of_limbs out_5 out_6 out_7 out_8 =
      A_r_eq_b - B_r_eq_b + SM2_P_Z) by nia.
  assert (Hrange :
    0 <= u256_of_limbs out_5 out_6 out_7 out_8 < SM2_P_Z) by nia.
  assert (Hmod :
    Zmod (A_r_eq_b - B_r_eq_b) SM2_P_Z =
      u256_of_limbs out_5 out_6 out_7 out_8).
  {
    symmetry.
    apply (Zmod_unique
      (A_r_eq_b - B_r_eq_b) SM2_P_Z (-1)
      (u256_of_limbs out_5 out_6 out_7 out_8)); lia.
  }
  split_pure_spatial.
  - sep_apply_r_atomic
      (store_fp_base0_pack a_pre A_r_eq_b ltac:(lia)).
    sep_apply_r_atomic
      (store_fp_base0_pack result_pre
        (Zmod (A_r_eq_b - B_r_eq_b) SM2_P_Z)
        ltac:(rewrite Hmod; lia)).
    unfold store_sm2_p, store_u256_limbs.
    Exists out_5 out_6 out_7 out_8.
    Exists x0 x1 x2 x3.
    Exists SM2_P_LIMB_0 SM2_P_LIMB_1 SM2_P_LIMB_2 SM2_P_LIMB_3.
    rewrite sizeof_uint64.
    simpl.
    normalize_base0_offsets.
    entailer_with ltac:(try rewrite Hmod; try rewrite Hpvalue; lia).
    unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    entailer!.
  - dump_pre_spatial.
    lia.
Qed. 

Lemma proof_of_sub_mod_p_return_wit_4_non_alias_split_goal_1 : sub_mod_p_return_wit_4_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_4_non_alias_split_goal_2 : sub_mod_p_return_wit_4_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_4_non_alias_split_goal_3 : sub_mod_p_return_wit_4_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_4_non_alias : sub_mod_p_return_wit_4_non_alias.
Proof.
  unfold sub_mod_p_return_wit_4_non_alias.
  right; intros.
  close_sub_mod_p_no_borrow
    A_non_alias B_non_alias x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
    out retval out_2 retval_2 out_3 retval_3 out_4 retval_4
    PreH21 PreH16 PreH11 PreH6 PreH22 PreH31.
Qed. 

Lemma proof_of_sub_mod_p_return_wit_5_r_eq_a_split_goal_1 : sub_mod_p_return_wit_5_r_eq_a_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_5_r_eq_a_split_goal_2 : sub_mod_p_return_wit_5_r_eq_a_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_5_r_eq_a_split_goal_3 : sub_mod_p_return_wit_5_r_eq_a_split_goal_3.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_5_r_eq_a : sub_mod_p_return_wit_5_r_eq_a.
Proof.
  unfold sub_mod_p_return_wit_5_r_eq_a.
  right; intros.
  close_sub_mod_p_no_borrow
    A_r_eq_a B_r_eq_a x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
    out retval out_2 retval_2 out_3 retval_3 out_4 retval_4
    PreH21 PreH16 PreH11 PreH6 PreH22 PreH31.
Qed. 

Lemma proof_of_sub_mod_p_return_wit_6_r_eq_b_split_goal_1 : sub_mod_p_return_wit_6_r_eq_b_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_6_r_eq_b_split_goal_2 : sub_mod_p_return_wit_6_r_eq_b_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_6_r_eq_b_split_goal_3 : sub_mod_p_return_wit_6_r_eq_b_split_goal_3.
Proof. Abort.

Lemma proof_of_sub_mod_p_return_wit_6_r_eq_b : sub_mod_p_return_wit_6_r_eq_b.
Proof.
  unfold sub_mod_p_return_wit_6_r_eq_b.
  right; intros.
  close_sub_mod_p_no_borrow
    A_r_eq_b B_r_eq_b x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
    out retval out_2 retval_2 out_3 retval_3 out_4 retval_4
    PreH21 PreH16 PreH11 PreH6 PreH22 PreH31.
Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_1_non_alias_pure_split_goal_1 : sub_mod_p_partial_solve_wit_1_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_1_non_alias_pure_split_goal_2 : sub_mod_p_partial_solve_wit_1_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_1_non_alias_pure : sub_mod_p_partial_solve_wit_1_non_alias_pure.
Proof. close_sub_mod_p_partial. Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_2_r_eq_a_pure_split_goal_1 : sub_mod_p_partial_solve_wit_2_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_2_r_eq_a_pure_split_goal_2 : sub_mod_p_partial_solve_wit_2_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_2_r_eq_a_pure : sub_mod_p_partial_solve_wit_2_r_eq_a_pure.
Proof. close_sub_mod_p_partial. Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_3_r_eq_b_pure_split_goal_1 : sub_mod_p_partial_solve_wit_3_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_3_r_eq_b_pure_split_goal_2 : sub_mod_p_partial_solve_wit_3_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_3_r_eq_b_pure : sub_mod_p_partial_solve_wit_3_r_eq_b_pure.
Proof. close_sub_mod_p_partial. Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_1 : sub_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_2 : sub_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_4_non_alias_pure : sub_mod_p_partial_solve_wit_4_non_alias_pure.
Proof. close_sub_mod_p_partial. Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_5_r_eq_a_pure_split_goal_1 : sub_mod_p_partial_solve_wit_5_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_5_r_eq_a_pure_split_goal_2 : sub_mod_p_partial_solve_wit_5_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_5_r_eq_a_pure : sub_mod_p_partial_solve_wit_5_r_eq_a_pure.
Proof. close_sub_mod_p_partial. Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_6_r_eq_b_pure_split_goal_1 : sub_mod_p_partial_solve_wit_6_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_6_r_eq_b_pure_split_goal_2 : sub_mod_p_partial_solve_wit_6_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_6_r_eq_b_pure : sub_mod_p_partial_solve_wit_6_r_eq_b_pure.
Proof. close_sub_mod_p_partial. Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_7_non_alias_pure_split_goal_1 : sub_mod_p_partial_solve_wit_7_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_7_non_alias_pure_split_goal_2 : sub_mod_p_partial_solve_wit_7_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_7_non_alias_pure : sub_mod_p_partial_solve_wit_7_non_alias_pure.
Proof. close_sub_mod_p_partial. Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_8_r_eq_a_pure_split_goal_1 : sub_mod_p_partial_solve_wit_8_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_8_r_eq_a_pure_split_goal_2 : sub_mod_p_partial_solve_wit_8_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_8_r_eq_a_pure : sub_mod_p_partial_solve_wit_8_r_eq_a_pure.
Proof. close_sub_mod_p_partial. Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_9_r_eq_b_pure_split_goal_1 : sub_mod_p_partial_solve_wit_9_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_9_r_eq_b_pure_split_goal_2 : sub_mod_p_partial_solve_wit_9_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_9_r_eq_b_pure : sub_mod_p_partial_solve_wit_9_r_eq_b_pure.
Proof. close_sub_mod_p_partial. Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_1 : sub_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_2 : sub_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_10_non_alias_pure : sub_mod_p_partial_solve_wit_10_non_alias_pure.
Proof. close_sub_mod_p_partial. Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_11_r_eq_a_pure_split_goal_1 : sub_mod_p_partial_solve_wit_11_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_11_r_eq_a_pure_split_goal_2 : sub_mod_p_partial_solve_wit_11_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_11_r_eq_a_pure : sub_mod_p_partial_solve_wit_11_r_eq_a_pure.
Proof. close_sub_mod_p_partial. Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_12_r_eq_b_pure_split_goal_1 : sub_mod_p_partial_solve_wit_12_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_12_r_eq_b_pure_split_goal_2 : sub_mod_p_partial_solve_wit_12_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_12_r_eq_b_pure : sub_mod_p_partial_solve_wit_12_r_eq_b_pure.
Proof. close_sub_mod_p_partial. Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_14_non_alias_pure_split_goal_1 : sub_mod_p_partial_solve_wit_14_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_14_non_alias_pure_split_goal_2 : sub_mod_p_partial_solve_wit_14_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_14_non_alias_pure : sub_mod_p_partial_solve_wit_14_non_alias_pure.
Proof.
  unfold sub_mod_p_partial_solve_wit_14_non_alias_pure.
  close_sub_mod_p_partial_parent.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof sm2_p_limbs; lia.
Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_16_r_eq_a_pure_split_goal_1 : sub_mod_p_partial_solve_wit_16_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_16_r_eq_a_pure_split_goal_2 : sub_mod_p_partial_solve_wit_16_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_16_r_eq_a_pure : sub_mod_p_partial_solve_wit_16_r_eq_a_pure.
Proof.
  unfold sub_mod_p_partial_solve_wit_16_r_eq_a_pure.
  close_sub_mod_p_partial_parent.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof sm2_p_limbs; lia.
Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_18_r_eq_b_pure_split_goal_1 : sub_mod_p_partial_solve_wit_18_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_18_r_eq_b_pure_split_goal_2 : sub_mod_p_partial_solve_wit_18_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_18_r_eq_b_pure : sub_mod_p_partial_solve_wit_18_r_eq_b_pure.
Proof.
  unfold sub_mod_p_partial_solve_wit_18_r_eq_b_pure.
  close_sub_mod_p_partial_parent.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof sm2_p_limbs; lia.
Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_20_non_alias_pure_split_goal_1 : sub_mod_p_partial_solve_wit_20_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_20_non_alias_pure_split_goal_2 : sub_mod_p_partial_solve_wit_20_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_20_non_alias_pure : sub_mod_p_partial_solve_wit_20_non_alias_pure.
Proof.
  unfold sub_mod_p_partial_solve_wit_20_non_alias_pure.
  close_sub_mod_p_partial_parent.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof sm2_p_limbs; lia.
Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_22_r_eq_a_pure_split_goal_1 : sub_mod_p_partial_solve_wit_22_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_22_r_eq_a_pure_split_goal_2 : sub_mod_p_partial_solve_wit_22_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_22_r_eq_a_pure : sub_mod_p_partial_solve_wit_22_r_eq_a_pure.
Proof.
  unfold sub_mod_p_partial_solve_wit_22_r_eq_a_pure.
  close_sub_mod_p_partial_parent.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof sm2_p_limbs; lia.
Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_24_r_eq_b_pure_split_goal_1 : sub_mod_p_partial_solve_wit_24_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_24_r_eq_b_pure_split_goal_2 : sub_mod_p_partial_solve_wit_24_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_24_r_eq_b_pure : sub_mod_p_partial_solve_wit_24_r_eq_b_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer_with ltac:(
    try close_sub_mod_p_unsigned_range;
    cbv [U32_MOD U64_MOD SM2_P_LIMB_0 SM2_P_LIMB_1
         SM2_P_LIMB_2 SM2_P_LIMB_3] in *;
    lia).
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    entailer_with ltac:(pose proof sm2_p_limbs; lia).
Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_26_non_alias_pure_split_goal_1 : sub_mod_p_partial_solve_wit_26_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_26_non_alias_pure_split_goal_2 : sub_mod_p_partial_solve_wit_26_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_26_non_alias_pure : sub_mod_p_partial_solve_wit_26_non_alias_pure.
Proof.
  unfold sub_mod_p_partial_solve_wit_26_non_alias_pure.
  close_sub_mod_p_partial_parent_right.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof sm2_p_limbs; lia.
Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_28_r_eq_a_pure_split_goal_1 : sub_mod_p_partial_solve_wit_28_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_28_r_eq_a_pure_split_goal_2 : sub_mod_p_partial_solve_wit_28_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_28_r_eq_a_pure : sub_mod_p_partial_solve_wit_28_r_eq_a_pure.
Proof.
  unfold sub_mod_p_partial_solve_wit_28_r_eq_a_pure.
  close_sub_mod_p_partial_parent_right.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof sm2_p_limbs; lia.
Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_30_r_eq_b_pure_split_goal_1 : sub_mod_p_partial_solve_wit_30_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_30_r_eq_b_pure_split_goal_2 : sub_mod_p_partial_solve_wit_30_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_30_r_eq_b_pure : sub_mod_p_partial_solve_wit_30_r_eq_b_pure.
Proof.
  unfold sub_mod_p_partial_solve_wit_30_r_eq_b_pure.
  close_sub_mod_p_partial_parent_right.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof sm2_p_limbs; lia.
Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_32_non_alias_pure_split_goal_1 : sub_mod_p_partial_solve_wit_32_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_32_non_alias_pure_split_goal_2 : sub_mod_p_partial_solve_wit_32_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_32_non_alias_pure : sub_mod_p_partial_solve_wit_32_non_alias_pure.
Proof.
  unfold sub_mod_p_partial_solve_wit_32_non_alias_pure.
  close_sub_mod_p_partial_parent.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof sm2_p_limbs; lia.
Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_34_r_eq_a_pure_split_goal_1 : sub_mod_p_partial_solve_wit_34_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_34_r_eq_a_pure_split_goal_2 : sub_mod_p_partial_solve_wit_34_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_34_r_eq_a_pure : sub_mod_p_partial_solve_wit_34_r_eq_a_pure.
Proof.
  unfold sub_mod_p_partial_solve_wit_34_r_eq_a_pure.
  close_sub_mod_p_partial_parent.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof sm2_p_limbs; lia.
Qed. 

Lemma proof_of_sub_mod_p_partial_solve_wit_36_r_eq_b_pure_split_goal_1 : sub_mod_p_partial_solve_wit_36_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_36_r_eq_b_pure_split_goal_2 : sub_mod_p_partial_solve_wit_36_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_p_partial_solve_wit_36_r_eq_b_pure : sub_mod_p_partial_solve_wit_36_r_eq_b_pure.
Proof.
  unfold sub_mod_p_partial_solve_wit_36_r_eq_b_pure.
  close_sub_mod_p_partial_parent.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof sm2_p_limbs; lia.
Qed. 

Lemma proof_of_sub_mod_p_derive_mont_r_eq_b_by_r_eq_b : sub_mod_p_derive_mont_r_eq_b_by_r_eq_b.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename B_mont_r_eq_b into B.
  rename A_mont_r_eq_b into A.
  Exists (mont_p A) (mont_p B).
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    rewrite ec_math_refinement.mont_p_sub.
    entailer!.
Qed. 

Lemma proof_of_sub_mod_p_derive_mont_non_alias_by_non_alias : sub_mod_p_derive_mont_non_alias_by_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename B_mont_non_alias into B.
  rename A_mont_non_alias into A.
  Exists (mont_p A) (mont_p B).
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    rewrite ec_math_refinement.mont_p_sub.
    entailer!.
Qed. 
