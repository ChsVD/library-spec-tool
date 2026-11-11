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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import MontgInvModp_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import MontgInvModp_proof_auto.
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

Lemma proof_of_MontgInvModp_entail_wit_2_non_alias_split_goal_1 : MontgInvModp_entail_wit_2_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_2_non_alias_split_goal_2 : MontgInvModp_entail_wit_2_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_2_non_alias : MontgInvModp_entail_wit_2_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_fp, store_mod.
  symmetry in PreH1, PreH10.
  apply u256_of_limbs_eq_zero_iff__eq_zero in PreH1; try lia.
  apply u256_of_limbs_eq_zero_iff__eq_zero in PreH10; try lia.
  destruct PreH1 as [Hx06 [Hx16 [Hx26 Hx36]]].
  destruct PreH10 as [Hx05 [Hx15 [Hx25 Hx35]]].
  subst x0_4 x1_4 x2_4 x3_4 x0_3 x1_3 x2_3 x3_3.
  Exists SM2_P_Z A_non_alias 0 1.
  entailer!.
  unfold UndefStructPredu32, store_u256, store_u256_limbs.
  Exists x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2 0 0 0 0 1 0 0 0.
  entailer!.
  repeat rewrite <- global_u32_v_addr_eq; cancel.
  apply sm2p_mont_inv_phase1_init_nonzero; assumption.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_3_in_place_split_goal_1 : MontgInvModp_entail_wit_3_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_3_in_place_split_goal_2 : MontgInvModp_entail_wit_3_in_place_split_goal_2.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_3_in_place : MontgInvModp_entail_wit_3_in_place.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_fp, store_mod.
  symmetry in PreH1, PreH10.
  apply u256_of_limbs_eq_zero_iff__eq_zero in PreH1; try lia.
  apply u256_of_limbs_eq_zero_iff__eq_zero in PreH10; try lia.
  destruct PreH1 as [Hx06 [Hx16 [Hx26 Hx36]]].
  destruct PreH10 as [Hx05 [Hx15 [Hx25 Hx35]]].
  subst x0_4 x1_4 x2_4 x3_4 x0_3 x1_3 x2_3 x3_3.
  Exists SM2_P_Z A_in_place 0 1.
  entailer!.
  unfold UndefStructPredu32, store_u256, store_u256_limbs.
  Exists x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2 0 0 0 0 1 0 0 0.
  entailer!.
  repeat rewrite <- global_u32_v_addr_eq; cancel.
  apply sm2p_mont_inv_phase1_init_nonzero; assumption.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_5_non_alias_split_goal_1 : MontgInvModp_entail_wit_5_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_5_non_alias : MontgInvModp_entail_wit_5_non_alias.
Proof.
  right.
  intros.
  assert (Hueven : Z.land Un 1 = 0).
  {
    rewrite PreH12, u256_low_bit.
    exact PreH2.
  }
  assert (H2s : 2 * Sn < U256_MOD).
  {
    pose proof PreH45 as Hstate_bounds.
    unfold sm2p_mont_inv_phase1_state in Hstate_bounds.
    destruct Hstate_bounds as
      (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hoverflow & _).
    unfold fieldOp_lib.sm2p_mont_inv_phase1_overflow_reach in Hoverflow.
    destruct Hoverflow as [_ Hoverflow].
    specialize (Hoverflow PreH43).
    destruct Hoverflow as (_ & _ & Hdouble_s & _).
    apply Hdouble_s.
    left.
    exact Hueven.
  }
  destruct (u256_shl_result_no_overflow
    (u256_of_limbs x0 x1 x2 x3) Y retval_2 PreH1)
    as [HY _].
  { rewrite <- PreH30. exact H2s. }
  rewrite <- PreH30 in HY.
  assert (Hnext := sm2p_mont_inv_phase1_halve_u
    A_non_alias Un Vn Rn Sn k carry Y
    PreH45 PreH43 Hueven HY).
  assert (HUn : 0 <= Un).
  {
    rewrite PreH12.
    pose proof (u256_of_limbs_range
      x0_3 x1_3 x2_3 x3_3
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    lia.
  }
  entailer!.
  rewrite Z.quot_div_nonneg by lia.
  exact Hnext.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_6_in_place_split_goal_1 : MontgInvModp_entail_wit_6_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_6_in_place : MontgInvModp_entail_wit_6_in_place.
Proof.
  right.
  intros.
  assert (Hueven : Z.land Ui 1 = 0).
  {
    rewrite PreH12, u256_low_bit.
    exact PreH2.
  }
  assert (H2s : 2 * Si < U256_MOD).
  {
    pose proof PreH46 as Hstate_bounds.
    unfold sm2p_mont_inv_phase1_state in Hstate_bounds.
    destruct Hstate_bounds as
      (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hoverflow & _).
    unfold fieldOp_lib.sm2p_mont_inv_phase1_overflow_reach in Hoverflow.
    destruct Hoverflow as [_ Hoverflow].
    specialize (Hoverflow PreH43).
    destruct Hoverflow as (_ & _ & Hdouble_s & _).
    apply Hdouble_s.
    left.
    exact Hueven.
  }
  destruct (u256_shl_result_no_overflow
    (u256_of_limbs x0 x1 x2 x3) Y retval_2 PreH1)
    as [HY _].
  { rewrite <- PreH30. exact H2s. }
  rewrite <- PreH30 in HY.
  assert (Hnext := sm2p_mont_inv_phase1_halve_u
    A_in_place Ui Vi Ri Si k carry Y
    PreH46 PreH43 Hueven HY).
  assert (HUi : 0 <= Ui).
  {
    rewrite PreH12.
    pose proof (u256_of_limbs_range
      x0_3 x1_3 x2_3 x3_3
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    lia.
  }
  entailer!.
  rewrite Z.quot_div_nonneg by lia.
  exact Hnext.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_7_non_alias_split_goal_1 : MontgInvModp_entail_wit_7_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_7_non_alias : MontgInvModp_entail_wit_7_non_alias.
Proof.
  right.
  intros.
  assert (Huodd : Z.land Un 1 = 1).
  {
    rewrite PreH13, u256_low_bit.
    rewrite land_one_eq_mod_two in PreH3 |- *.
    pose proof (Z.mod_pos_bound x0_3 2 ltac:(lia)).
    lia.
  }
  assert (Hveven : Z.land Vn 1 = 0).
  {
    rewrite PreH4, u256_low_bit.
    exact PreH2.
  }
  assert (H2r : 2 * Rn < U256_MOD).
  {
    pose proof PreH46 as Hstate_bounds.
    unfold sm2p_mont_inv_phase1_state in Hstate_bounds.
    destruct Hstate_bounds as
      (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hoverflow & _).
    unfold fieldOp_lib.sm2p_mont_inv_phase1_overflow_reach in Hoverflow.
    destruct Hoverflow as [_ Hoverflow].
    specialize (Hoverflow PreH44).
    destruct Hoverflow as (_ & _ & _ & Hdouble_r).
    apply Hdouble_r.
    split; [exact Huodd |].
    left.
    exact Hveven.
  }
  destruct (u256_shl_result_no_overflow
    (u256_of_limbs x0_2 x1_2 x2_2 x3_2) Y retval_2 PreH1)
    as [HY _].
  { rewrite <- PreH22. exact H2r. }
  rewrite <- PreH22 in HY.
  assert (Hnext := sm2p_mont_inv_phase1_halve_v
    A_non_alias Un Vn Rn Sn k carry Y
    PreH46 PreH44 Huodd Hveven HY).
  assert (HVn : 0 <= Vn).
  {
    rewrite PreH4.
    pose proof (u256_of_limbs_range
      x0_4 x1_4 x2_4 x3_4
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    lia.
  }
  entailer!.
  rewrite Z.quot_div_nonneg by lia.
  exact Hnext.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_8_in_place_split_goal_1 : MontgInvModp_entail_wit_8_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_8_in_place : MontgInvModp_entail_wit_8_in_place.
Proof.
  right.
  intros.
  assert (Huodd : Z.land Ui 1 = 1).
  {
    rewrite PreH13, u256_low_bit.
    rewrite land_one_eq_mod_two in PreH3 |- *.
    pose proof (Z.mod_pos_bound x0_3 2 ltac:(lia)).
    lia.
  }
  assert (Hveven : Z.land Vi 1 = 0).
  {
    rewrite PreH4, u256_low_bit.
    exact PreH2.
  }
  assert (H2r : 2 * Ri < U256_MOD).
  {
    pose proof PreH47 as Hstate_bounds.
    unfold sm2p_mont_inv_phase1_state in Hstate_bounds.
    destruct Hstate_bounds as
      (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hoverflow & _).
    unfold fieldOp_lib.sm2p_mont_inv_phase1_overflow_reach in Hoverflow.
    destruct Hoverflow as [_ Hoverflow].
    specialize (Hoverflow PreH44).
    destruct Hoverflow as (_ & _ & _ & Hdouble_r).
    apply Hdouble_r.
    split; [exact Huodd |].
    left.
    exact Hveven.
  }
  destruct (u256_shl_result_no_overflow
    (u256_of_limbs x0_2 x1_2 x2_2 x3_2) Y retval_2 PreH1)
    as [HY _].
  { rewrite <- PreH22. exact H2r. }
  rewrite <- PreH22 in HY.
  assert (Hnext := sm2p_mont_inv_phase1_halve_v
    A_in_place Ui Vi Ri Si k carry Y
    PreH47 PreH44 Huodd Hveven HY).
  assert (HVi : 0 <= Vi).
  {
    rewrite PreH4.
    pose proof (u256_of_limbs_range
      x0_4 x1_4 x2_4 x3_4
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    lia.
  }
  entailer!.
  rewrite Z.quot_div_nonneg by lia.
  exact Hnext.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_11_non_alias : MontgInvModp_entail_wit_11_non_alias.
Proof.
  right.
  intros.
  assert (Huodd : Z.land Un 1 = 1).
  {
    rewrite PreH27, u256_low_bit.
    rewrite land_one_eq_mod_two in PreH17 |- *.
    pose proof (Z.mod_pos_bound x0_3 2 ltac:(lia)).
    lia.
  }
  assert (Hvodd : Z.land Vn 1 = 1).
  {
    rewrite PreH18, u256_low_bit.
    rewrite land_one_eq_mod_two in PreH16 |- *.
    pose proof (Z.mod_pos_bound x0_4 2 ltac:(lia)).
    lia.
  }
  assert (Huv : Un > Vn).
  { rewrite PreH27, PreH18. exact PreH15. }
  pose proof PreH60 as Hstate_bounds.
  unfold sm2p_mont_inv_phase1_state in Hstate_bounds.
  destruct Hstate_bounds as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hoverflow & _).
  unfold fieldOp_lib.sm2p_mont_inv_phase1_overflow_reach in Hoverflow.
  destruct Hoverflow as [_ Hoverflow].
  specialize (Hoverflow PreH58).
  destruct Hoverflow as (_ & Hrs & Hdouble_s & _).
  assert (HS : S = Un - Vn).
  {
    unfold U256_MOD in PreH8, PreH11 |- *.
    lia.
  }
  assert (HS2 : S_2 = Rn + Sn).
  {
    unfold U256_MOD in Hrs, PreH3, PreH6 |- *.
    lia.
  }
  assert (H2s : 2 * Sn < U256_MOD).
  {
    apply Hdouble_s.
    right.
    repeat split; assumption.
  }
  destruct (u256_shl_result_no_overflow Sn Y retval_4 PreH1 H2s)
    as [HY _].
  assert (Hnext := sm2p_mont_inv_phase1_sub_halve_u
    A_non_alias Un Vn Rn Sn k carry
    PreH60 PreH58 Huodd Hvodd Huv).
  assert (Hadd :
    u256_of_limbs x0_2 x1_2 x2_2 x3_2 +
    u256_of_limbs x0 x1 x2 x3 =
    S_2 + retval_3 * U256_MOD).
  {
    rewrite <- PreH36, <- PreH45.
    exact PreH6.
  }
  assert (Hphase :
    sm2p_mont_inv_phase1_state
      A_non_alias (S ÷ 2)
      (u256_of_limbs x0_4 x1_4 x2_4 x3_4)
      S_2 Y
      (unsigned_last_nbits (k + 1) 64) carry).
  {
    rewrite <- PreH18.
    rewrite HS2, HY.
    rewrite Z.quot_div_nonneg by lia.
    rewrite HS.
    exact Hnext.
  }
  Exists retval_3 borrow_2 S.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_12_in_place : MontgInvModp_entail_wit_12_in_place.
Proof.
  right.
  intros.
  assert (Huodd : Z.land Ui 1 = 1).
  {
    rewrite PreH27, u256_low_bit.
    rewrite land_one_eq_mod_two in PreH17 |- *.
    pose proof (Z.mod_pos_bound x0_3 2 ltac:(lia)).
    lia.
  }
  assert (Hvodd : Z.land Vi 1 = 1).
  {
    rewrite PreH18, u256_low_bit.
    rewrite land_one_eq_mod_two in PreH16 |- *.
    pose proof (Z.mod_pos_bound x0_4 2 ltac:(lia)).
    lia.
  }
  assert (Huv : Ui > Vi).
  { rewrite PreH27, PreH18. exact PreH15. }
  pose proof PreH61 as Hstate_bounds.
  unfold sm2p_mont_inv_phase1_state in Hstate_bounds.
  destruct Hstate_bounds as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hoverflow & _).
  unfold fieldOp_lib.sm2p_mont_inv_phase1_overflow_reach in Hoverflow.
  destruct Hoverflow as [_ Hoverflow].
  specialize (Hoverflow PreH58).
  destruct Hoverflow as (_ & Hrs & Hdouble_s & _).
  assert (HS : S = Ui - Vi).
  {
    unfold U256_MOD in PreH8, PreH11 |- *.
    lia.
  }
  assert (HS2 : S_2 = Ri + Si).
  {
    unfold U256_MOD in Hrs, PreH3, PreH6 |- *.
    lia.
  }
  assert (H2s : 2 * Si < U256_MOD).
  {
    apply Hdouble_s.
    right.
    repeat split; assumption.
  }
  destruct (u256_shl_result_no_overflow Si Y retval_4 PreH1 H2s)
    as [HY _].
  assert (Hnext := sm2p_mont_inv_phase1_sub_halve_u
    A_in_place Ui Vi Ri Si k carry
    PreH61 PreH58 Huodd Hvodd Huv).
  assert (Hadd :
    u256_of_limbs x0_2 x1_2 x2_2 x3_2 +
    u256_of_limbs x0 x1 x2 x3 =
    S_2 + retval_3 * U256_MOD).
  {
    rewrite <- PreH36, <- PreH45.
    exact PreH6.
  }
  assert (Hphase :
    sm2p_mont_inv_phase1_state
      A_in_place (S ÷ 2)
      (u256_of_limbs x0_4 x1_4 x2_4 x3_4)
      S_2 Y
      (unsigned_last_nbits (k + 1) 64) carry).
  {
    rewrite <- PreH18.
    rewrite HS2, HY.
    rewrite Z.quot_div_nonneg by lia.
    rewrite HS.
    exact Hnext.
  }
  Exists retval_3 borrow_2 S.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_13_non_alias : MontgInvModp_entail_wit_13_non_alias.
Proof.
  right.
  intros.
  assert (Huodd : Z.land Un 1 = 1).
  {
    rewrite PreH27, u256_low_bit.
    rewrite land_one_eq_mod_two in PreH17 |- *.
    pose proof (Z.mod_pos_bound x0_3 2 ltac:(lia)).
    lia.
  }
  assert (Hvodd : Z.land Vn 1 = 1).
  {
    rewrite PreH18, u256_low_bit.
    rewrite land_one_eq_mod_two in PreH16 |- *.
    pose proof (Z.mod_pos_bound x0_4 2 ltac:(lia)).
    lia.
  }
  assert (Huv : Un <= Vn).
  { rewrite PreH27, PreH18. exact PreH15. }
  pose proof PreH60 as Hstate_bounds.
  unfold sm2p_mont_inv_phase1_state in Hstate_bounds.
  destruct Hstate_bounds as
    (_ & Hu & Hv & _ & _ & _ & _ & _ & _ & _ & Hoverflow & _).
  unfold fieldOp_lib.sm2p_mont_inv_phase1_overflow_reach in Hoverflow.
  destruct Hoverflow as [_ Hoverflow].
  specialize (Hoverflow PreH58).
  destruct Hoverflow as (_ & Hrs & _).
  assert (HS : S = Vn - Un).
  {
    unfold U256_MOD in Hu, Hv, PreH8, PreH11 |- *.
    lia.
  }
  assert (HS2 : S_2 = Rn + Sn).
  {
    unfold U256_MOD in Hrs, PreH3, PreH6 |- *.
    lia.
  }
  assert (Hnext := sm2p_mont_inv_phase1_sub_halve_v
    A_non_alias Un Vn Rn Sn k carry Y retval
    PreH60 PreH58 Huodd Hvodd Huv PreH1).
  assert (Hadd :
    u256_of_limbs x0_2 x1_2 x2_2 x3_2 +
    u256_of_limbs x0 x1 x2 x3 =
    S_2 + retval_4 * U256_MOD).
  {
    rewrite <- PreH36, <- PreH45.
    exact PreH6.
  }
  assert (Hphase :
    sm2p_mont_inv_phase1_state
      A_non_alias
      (u256_of_limbs x0_3 x1_3 x2_3 x3_3) (S ÷ 2)
      Y S_2
      (unsigned_last_nbits (k + 1) 64)
      (unsigned_last_nbits (carry + retval) 8)).
  {
    rewrite <- PreH27.
    rewrite HS2.
    rewrite Z.quot_div_nonneg by lia.
    rewrite HS.
    exact Hnext.
  }
  Exists retval_4 borrow_2 S.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_14_in_place : MontgInvModp_entail_wit_14_in_place.
Proof.
  right.
  intros.
  assert (Huodd : Z.land Ui 1 = 1).
  {
    rewrite PreH27, u256_low_bit.
    rewrite land_one_eq_mod_two in PreH17 |- *.
    pose proof (Z.mod_pos_bound x0_3 2 ltac:(lia)).
    lia.
  }
  assert (Hvodd : Z.land Vi 1 = 1).
  {
    rewrite PreH18, u256_low_bit.
    rewrite land_one_eq_mod_two in PreH16 |- *.
    pose proof (Z.mod_pos_bound x0_4 2 ltac:(lia)).
    lia.
  }
  assert (Huv : Ui <= Vi).
  { rewrite PreH27, PreH18. exact PreH15. }
  pose proof PreH61 as Hstate_bounds.
  unfold sm2p_mont_inv_phase1_state in Hstate_bounds.
  destruct Hstate_bounds as
    (_ & Hu & Hv & _ & _ & _ & _ & _ & _ & _ & Hoverflow & _).
  unfold fieldOp_lib.sm2p_mont_inv_phase1_overflow_reach in Hoverflow.
  destruct Hoverflow as [_ Hoverflow].
  specialize (Hoverflow PreH58).
  destruct Hoverflow as (_ & Hrs & _).
  assert (HS : S = Vi - Ui).
  {
    unfold U256_MOD in Hu, Hv, PreH8, PreH11 |- *.
    lia.
  }
  assert (HS2 : S_2 = Ri + Si).
  {
    unfold U256_MOD in Hrs, PreH3, PreH6 |- *.
    lia.
  }
  assert (Hnext := sm2p_mont_inv_phase1_sub_halve_v
    A_in_place Ui Vi Ri Si k carry Y retval
    PreH61 PreH58 Huodd Hvodd Huv PreH1).
  assert (Hadd :
    u256_of_limbs x0_2 x1_2 x2_2 x3_2 +
    u256_of_limbs x0 x1 x2 x3 =
    S_2 + retval_4 * U256_MOD).
  {
    rewrite <- PreH36, <- PreH45.
    exact PreH6.
  }
  assert (Hphase :
    sm2p_mont_inv_phase1_state
      A_in_place
      (u256_of_limbs x0_3 x1_3 x2_3 x3_3) (S ÷ 2)
      Y S_2
      (unsigned_last_nbits (k + 1) 64)
      (unsigned_last_nbits (carry + retval) 8)).
  {
    rewrite <- PreH27.
    rewrite HS2.
    rewrite Z.quot_div_nonneg by lia.
    rewrite HS.
    exact Hnext.
  }
  Exists retval_4 borrow_2 S.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_17_non_alias_split_goal_1 : MontgInvModp_entail_wit_17_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_17_non_alias_split_goal_2 : MontgInvModp_entail_wit_17_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_17_non_alias_split_goal_3 : MontgInvModp_entail_wit_17_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_17_non_alias_split_goal_4 : MontgInvModp_entail_wit_17_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_17_non_alias_split_goal_5 : MontgInvModp_entail_wit_17_non_alias_split_goal_5.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_17_non_alias : MontgInvModp_entail_wit_17_non_alias.
Proof.
  right.
  intros.
  pose proof PreH7 as Hstate.
  unfold sm2p_mont_inv_phase1_state in Hstate.
  destruct Hstate as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit).
  specialize (Hexit PreH5).
  destruct Hexit as [_ Hexit].
  pose proof Hexit as Hexit_facts.
  unfold sm2p_mont_inv_phase1_exit_carry in Hexit_facts.
  destruct Hexit_facts as (_ & _ & Hcarry & _ & Hk & _).
  clear - Hexit Hcarry Hk.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_18_in_place_split_goal_1 : MontgInvModp_entail_wit_18_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_18_in_place_split_goal_2 : MontgInvModp_entail_wit_18_in_place_split_goal_2.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_18_in_place_split_goal_3 : MontgInvModp_entail_wit_18_in_place_split_goal_3.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_18_in_place_split_goal_4 : MontgInvModp_entail_wit_18_in_place_split_goal_4.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_18_in_place_split_goal_5 : MontgInvModp_entail_wit_18_in_place_split_goal_5.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_18_in_place : MontgInvModp_entail_wit_18_in_place.
Proof.
  right.
  intros.
  pose proof PreH8 as Hstate.
  unfold sm2p_mont_inv_phase1_state in Hstate.
  destruct Hstate as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hexit).
  specialize (Hexit PreH5).
  destruct Hexit as [_ Hexit].
  pose proof Hexit as Hexit_facts.
  unfold sm2p_mont_inv_phase1_exit_carry in Hexit_facts.
  destruct Hexit_facts as (_ & _ & Hcarry & _ & Hk & _).
  clear - Hexit Hcarry Hk.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_21_non_alias_split_goal_1 : MontgInvModp_entail_wit_21_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_21_non_alias : MontgInvModp_entail_wit_21_non_alias.
Proof.
  right.
  intros.
  assert (Hcarry1 : carry = 1) by lia.
  pose proof PreH49 as Hexit.
  unfold sm2p_mont_inv_phase1_exit_carry in Hexit.
  destruct Hexit as
    (Ha & Hr & Hcarry & Hgcd & Hkrange & Hmod & Hzero & Hone).
  specialize (Hone Hcarry1).
  assert (Hborrow1 : borrow = 1).
  {
    pose proof (proj1 sm2_p_montgomery_bounds) as Hn.
    unfold U256_MOD in PreH2, PreH5 |- *.
    lia.
  }
  assert (HS : S = Rn + U256_MOD - SM2_P_Z).
  { lia. }
  assert (Hres : sm2p_mont_inv_post_loop_residue A_non_alias S k).
  {
    unfold sm2p_mont_inv_post_loop_residue.
    split; [exact Ha |].
    split.
    - pose proof (proj1 sm2_p_montgomery_bounds) as Hn.
      pose proof sm2_p_more_than_half as Hhalf.
      lia.
    - split; [exact Hgcd |].
      split; [exact Hkrange |].
      rewrite HS.
      rewrite mul_sub_modulus_mod.
      rewrite Hcarry1 in Hmod.
      exact Hmod.
  }
  clear - Hres.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_22_in_place_split_goal_1 : MontgInvModp_entail_wit_22_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_22_in_place : MontgInvModp_entail_wit_22_in_place.
Proof.
  right.
  intros.
  assert (Hcarry1 : carry = 1) by lia.
  pose proof PreH50 as Hexit.
  unfold sm2p_mont_inv_phase1_exit_carry in Hexit.
  destruct Hexit as
    (Ha & Hr & Hcarry & Hgcd & Hkrange & Hmod & Hzero & Hone).
  specialize (Hone Hcarry1).
  assert (Hborrow1 : borrow = 1).
  {
    pose proof (proj1 sm2_p_montgomery_bounds) as Hn.
    unfold U256_MOD in PreH2, PreH5 |- *.
    lia.
  }
  assert (HS : S = Ri + U256_MOD - SM2_P_Z).
  { lia. }
  assert (Hres : sm2p_mont_inv_post_loop_residue A_in_place S k).
  {
    unfold sm2p_mont_inv_post_loop_residue.
    split; [exact Ha |].
    split.
    - pose proof (proj1 sm2_p_montgomery_bounds) as Hn.
      pose proof sm2_p_more_than_half as Hhalf.
      lia.
    - split; [exact Hgcd |].
      split; [exact Hkrange |].
      rewrite HS.
      rewrite mul_sub_modulus_mod.
      rewrite Hcarry1 in Hmod.
      exact Hmod.
  }
  clear - Hres.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_23_2_non_alias_split_goal_1 : MontgInvModp_entail_wit_23_2_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_23_2_non_alias : MontgInvModp_entail_wit_23_2_non_alias.
Proof.
  right.
  intros.
  assert (Hcarry0 : carry = 0) by lia.
  pose proof PreH8 as Hexit.
  unfold sm2p_mont_inv_phase1_exit_carry in Hexit.
  destruct Hexit as
    (Ha & Hr & Hcarry & Hgcd & Hkrange & Hmod & Hzero & Hone).
  specialize (Hzero Hcarry0).
  assert (Hres : sm2p_mont_inv_post_loop_residue A_non_alias Rn k).
  {
    unfold sm2p_mont_inv_post_loop_residue.
    split; [exact Ha |].
    split; [exact Hzero |].
    split; [exact Hgcd |].
    split; [exact Hkrange |].
    rewrite Hcarry0 in Hmod.
    replace (Rn + 0 * U256_MOD) with Rn in Hmod by ring.
    exact Hmod.
  }
  clear - Hres.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_24_2_in_place_split_goal_1 : MontgInvModp_entail_wit_24_2_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_24_2_in_place : MontgInvModp_entail_wit_24_2_in_place.
Proof.
  right.
  intros.
  assert (Hcarry0 : carry = 0) by lia.
  pose proof PreH9 as Hexit.
  unfold sm2p_mont_inv_phase1_exit_carry in Hexit.
  destruct Hexit as
    (Ha & Hr & Hcarry & Hgcd & Hkrange & Hmod & Hzero & Hone).
  specialize (Hzero Hcarry0).
  assert (Hres : sm2p_mont_inv_post_loop_residue A_in_place Ri k).
  {
    unfold sm2p_mont_inv_post_loop_residue.
    split; [exact Ha |].
    split; [exact Hzero |].
    split; [exact Hgcd |].
    split; [exact Hkrange |].
    rewrite Hcarry0 in Hmod.
    replace (Ri + 0 * U256_MOD) with Ri in Hmod by ring.
    exact Hmod.
  }
  clear - Hres.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_30_non_alias_split_goal_1 : MontgInvModp_entail_wit_30_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_30_non_alias : MontgInvModp_entail_wit_30_non_alias.
Proof.
  right.
  intros.
  rewrite u64_list_value_four in PreH27.
  rewrite <- PreH46 in PreH27.
  change (R2n >= SM2_P_Z) in PreH27.
  assert (Hge : SM2_P_Z <= R2n) by lia.
  assert (Hborrow : borrow = 0).
  {
    destruct (Z.eq_dec borrow 0) as [-> | Hne]; [reflexivity |].
    assert (borrow = 1) by lia.
    subst borrow.
    lia.
  }
  assert (Hs : S = R2n - SM2_P_Z) by (subst borrow; lia).
  pose proof
    (sm2p_residue_sub_modulus_norm
       A_non_alias R2n S k PreH69 Hge Hs) as Hnorm.
  clear - Hnorm.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_31_in_place_split_goal_1 : MontgInvModp_entail_wit_31_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_31_in_place : MontgInvModp_entail_wit_31_in_place.
Proof.
  right.
  intros.
  rewrite u64_list_value_four in PreH27.
  rewrite <- PreH46 in PreH27.
  change (R2i >= SM2_P_Z) in PreH27.
  assert (Hge : SM2_P_Z <= R2i) by lia.
  assert (Hborrow : borrow = 0).
  {
    destruct (Z.eq_dec borrow 0) as [-> | Hne]; [reflexivity |].
    assert (borrow = 1) by lia.
    subst borrow.
    lia.
  }
  assert (Hs : S = R2i - SM2_P_Z) by (subst borrow; lia).
  pose proof
    (sm2p_residue_sub_modulus_norm
       A_in_place R2i S k PreH70 Hge Hs) as Hnorm.
  clear - Hnorm.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_32_2_non_alias_split_goal_1 : MontgInvModp_entail_wit_32_2_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_32_2_non_alias_split_goal_2 : MontgInvModp_entail_wit_32_2_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_32_2_non_alias : MontgInvModp_entail_wit_32_2_non_alias.
Proof.
  right.
  intros.
  rewrite u64_list_value_four in PreH4.
  rewrite <- PreH23 in PreH4.
  change (R2n < SM2_P_Z) in PreH4.
  pose proof
    (sm2p_residue_below_modulus_norm
       A_non_alias R2n k PreH46 PreH4) as Hnorm.
  clear - Hnorm.
  rewrite u64_list_value_four.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_33_2_in_place_split_goal_1 : MontgInvModp_entail_wit_33_2_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_33_2_in_place_split_goal_2 : MontgInvModp_entail_wit_33_2_in_place_split_goal_2.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_33_2_in_place : MontgInvModp_entail_wit_33_2_in_place.
Proof.
  right.
  intros.
  rewrite u64_list_value_four in PreH4.
  rewrite <- PreH23 in PreH4.
  change (R2i < SM2_P_Z) in PreH4.
  pose proof
    (sm2p_residue_below_modulus_norm
       A_in_place R2i k PreH47 PreH4) as Hnorm.
  clear - Hnorm.
  rewrite u64_list_value_four.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_36_non_alias_split_goal_1 : MontgInvModp_entail_wit_36_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_36_non_alias_split_goal_2 : MontgInvModp_entail_wit_36_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_36_non_alias : MontgInvModp_entail_wit_36_non_alias.
Proof.
  right.
  intros.
  assert (Hr : 0 < R4n < SM2_P_Z).
  { unfold sm2p_mont_inv_post_loop_norm in PreH47; tauto. }
  assert (Hborrow : borrow = 0).
  {
    destruct (Z.eq_dec borrow 0) as [-> | Hne]; [reflexivity |].
    assert (borrow = 1) by lia.
    subst borrow.
    lia.
  }
  assert (Hs : S = SM2_P_Z - R4n) by (subst borrow; lia).
  pose proof
    (sm2p_norm_complement_result
       A_non_alias R4n S k PreH47 Hs) as Hresult.
  pose proof Hresult as Hresult_bounds.
  unfold sm2p_mont_inv_phase1_result in Hresult_bounds.
  destruct Hresult_bounds as (_ & HSrange & _).
  assert (HSlt : S < SM2_P_Z) by exact (proj2 HSrange).
  clear - Hresult HSlt.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_37_in_place_split_goal_1 : MontgInvModp_entail_wit_37_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_37_in_place_split_goal_2 : MontgInvModp_entail_wit_37_in_place_split_goal_2.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_37_in_place : MontgInvModp_entail_wit_37_in_place.
Proof.
  right.
  intros.
  assert (Hr : 0 < R4i < SM2_P_Z).
  { unfold sm2p_mont_inv_post_loop_norm in PreH48; tauto. }
  assert (Hborrow : borrow = 0).
  {
    destruct (Z.eq_dec borrow 0) as [-> | Hne]; [reflexivity |].
    assert (borrow = 1) by lia.
    subst borrow.
    lia.
  }
  assert (Hs : S = SM2_P_Z - R4i) by (subst borrow; lia).
  pose proof
    (sm2p_norm_complement_result
       A_in_place R4i S k PreH48 Hs) as Hresult.
  pose proof Hresult as Hresult_bounds.
  unfold sm2p_mont_inv_phase1_result in Hresult_bounds.
  destruct Hresult_bounds as (_ & HSrange & _).
  assert (HSlt : S < SM2_P_Z) by exact (proj2 HSrange).
  clear - Hresult HSlt.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_40_non_alias_split_goal_1 : MontgInvModp_entail_wit_40_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_40_non_alias_split_goal_2 : MontgInvModp_entail_wit_40_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_40_non_alias_split_goal_3 : MontgInvModp_entail_wit_40_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_40_non_alias_split_goal_4 : MontgInvModp_entail_wit_40_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_40_non_alias_split_goal_5 : MontgInvModp_entail_wit_40_non_alias_split_goal_5.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_40_non_alias_split_goal_spatial : MontgInvModp_entail_wit_40_non_alias_split_goal_spatial.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_40_non_alias : MontgInvModp_entail_wit_40_non_alias.
Proof.
  right.
  intros.
  destruct (sm2p_mont_inv_phase2_index_bounds K0n ltac:(lia) PreH7)
    as [Hindex [Hi Hk]].
  rewrite !Z.quot_div_nonneg by lia.
  rewrite !Z.rem_mod_nonneg by lia.
  unfold store_u256, store_u256_limbs.
  Intros x0 x1 x2 x3.
  destruct H as [Hx0 [Hx1 [Hx2 [Hx3 Hzero]]]].
  symmetry in Hzero.
  apply u256_of_limbs_eq_zero_iff__eq_zero in Hzero; try lia.
  destruct Hzero as [E0 [E1 [E2 E3]]].
  subst x0 x1 x2 x3.
  repeat rewrite <- global_u32_v_addr_eq.
  entailer!.
  unfold UInt64Array.full, store_array.
  cbn [store_array_rec].
  csimpl.
  simpl.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_41_in_place_split_goal_1 : MontgInvModp_entail_wit_41_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_41_in_place_split_goal_2 : MontgInvModp_entail_wit_41_in_place_split_goal_2.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_41_in_place_split_goal_3 : MontgInvModp_entail_wit_41_in_place_split_goal_3.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_41_in_place_split_goal_4 : MontgInvModp_entail_wit_41_in_place_split_goal_4.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_41_in_place_split_goal_5 : MontgInvModp_entail_wit_41_in_place_split_goal_5.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_41_in_place_split_goal_spatial : MontgInvModp_entail_wit_41_in_place_split_goal_spatial.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_41_in_place : MontgInvModp_entail_wit_41_in_place.
Proof.
  right.
  intros.
  destruct (sm2p_mont_inv_phase2_index_bounds K0i ltac:(lia) PreH8)
    as [Hindex [Hi Hk]].
  rewrite !Z.quot_div_nonneg by lia.
  rewrite !Z.rem_mod_nonneg by lia.
  unfold store_u256, store_u256_limbs.
  Intros x0 x1 x2 x3.
  destruct H as [Hx0 [Hx1 [Hx2 [Hx3 Hzero]]]].
  symmetry in Hzero.
  apply u256_of_limbs_eq_zero_iff__eq_zero in Hzero; try lia.
  destruct Hzero as [E0 [E1 [E2 E3]]].
  subst x0 x1 x2 x3.
  repeat rewrite <- global_u32_v_addr_eq.
  entailer!.
  unfold UInt64Array.full, store_array.
  cbn [store_array_rec].
  csimpl.
  simpl.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_42_non_alias_split_goal_1 : MontgInvModp_entail_wit_42_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_42_non_alias_split_goal_2 : MontgInvModp_entail_wit_42_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_42_non_alias_split_goal_3 : MontgInvModp_entail_wit_42_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_42_non_alias : MontgInvModp_entail_wit_42_non_alias.
Proof.
  right.
  intros.
  destruct
    (sm2p_mont_inv_phase2_one_hot_value K0n i k PreH8
       ltac:(lia) ltac:(lia)) as [Hrange Hvalue].
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_43_in_place_split_goal_1 : MontgInvModp_entail_wit_43_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_43_in_place_split_goal_2 : MontgInvModp_entail_wit_43_in_place_split_goal_2.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_43_in_place_split_goal_3 : MontgInvModp_entail_wit_43_in_place_split_goal_3.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_43_in_place : MontgInvModp_entail_wit_43_in_place.
Proof.
  right.
  intros.
  destruct
    (sm2p_mont_inv_phase2_one_hot_value K0i i k PreH9
       ltac:(lia) ltac:(lia)) as [Hrange Hvalue].
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_44_non_alias : MontgInvModp_entail_wit_44_non_alias.
Proof.
  right.
  intros.
  destruct
    (sm2p_mont_inv_phase2_product_equation
       A_non_alias R5n K0n Tn R K
       ltac:(lia) PreH12 PreH14 PreH3) as [Kout HKout].
  Exists Kout K.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_45_in_place : MontgInvModp_entail_wit_45_in_place.
Proof.
  right.
  intros.
  destruct
    (sm2p_mont_inv_phase2_product_equation
       A_in_place R5i K0i Ti R K
       ltac:(lia) PreH13 PreH15 PreH3) as [Kout HKout].
  Exists Kout K.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_47_in_place_split_goal_spatial : MontgInvModp_entail_wit_47_in_place_split_goal_spatial.
Proof. Abort.

Lemma proof_of_MontgInvModp_entail_wit_47_in_place : MontgInvModp_entail_wit_47_in_place.
Proof.
  right.
  intros.
  subst k.
  subst result_pre.
  unfold store_fp, store_mod.
  entailer!.
  unfold store_u256, UndefStructPredu32.
  sep_apply store_u256_limbs_to_undef_full.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_48_non_alias : MontgInvModp_entail_wit_48_non_alias.
Proof.
  right.
  intros.
  destruct
    (sm2p_mont_inv_phase1_k256_equation
       A_non_alias R5n PreH8)
    as [Kout Hout].
  Exists Kout.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_49_in_place : MontgInvModp_entail_wit_49_in_place.
Proof.
  right.
  intros.
  destruct
    (sm2p_mont_inv_phase1_k256_equation
       A_in_place R5i PreH9)
    as [Kout Hout].
  Exists Kout.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_50_1_non_alias : MontgInvModp_entail_wit_50_1_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists Kout_2 Out_2.
  assert (Hundef : forall p x,
    store_u256 p x |-- UndefStructPredu32 p).
  {
    intros p x.
    unfold store_u256, UndefStructPredu32.
    apply store_u256_limbs_to_undef_full.
  }
  sep_apply (Hundef (&("u")) Un).
  sep_apply (Hundef (&("v")) 0).
  sep_apply (Hundef (&("r")) R5n).
  sep_apply (Hundef (&("s")) Sn).
  sep_apply (Hundef (&("t")) Tn).
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_50_2_non_alias : MontgInvModp_entail_wit_50_2_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists Kout_2 R5n.
  assert (Hundef : forall p x,
    store_u256 p x |-- UndefStructPredu32 p).
  {
    intros p x.
    unfold store_u256, UndefStructPredu32.
    apply store_u256_limbs_to_undef_full.
  }
  sep_apply (Hundef (&("u")) Un).
  sep_apply (Hundef (&("v")) 0).
  sep_apply (Hundef (&("r")) R5n).
  sep_apply (Hundef (&("s")) Sn).
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_51_1_in_place : MontgInvModp_entail_wit_51_1_in_place.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists Kout_2 Out_2.
  assert (Hundef : forall p x,
    store_u256 p x |-- UndefStructPredu32 p).
  {
    intros p x.
    unfold store_u256, UndefStructPredu32.
    apply store_u256_limbs_to_undef_full.
  }
  sep_apply (Hundef (&("u")) Ui).
  sep_apply (Hundef (&("v")) 0).
  sep_apply (Hundef (&("r")) R5i).
  sep_apply (Hundef (&("s")) Si).
  sep_apply (Hundef (&("t")) Ti).
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_entail_wit_51_2_in_place : MontgInvModp_entail_wit_51_2_in_place.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists Kout_2 R5i.
  assert (Hundef : forall p x,
    store_u256 p x |-- UndefStructPredu32 p).
  {
    intros p x.
    unfold store_u256, UndefStructPredu32.
    apply store_u256_limbs_to_undef_full.
  }
  sep_apply (Hundef (&("u")) Ui).
  sep_apply (Hundef (&("v")) 0).
  sep_apply (Hundef (&("r")) R5i).
  sep_apply (Hundef (&("s")) Si).
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_return_wit_1_non_alias : MontgInvModp_return_wit_1_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists Kout Out.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_return_wit_2_in_place : MontgInvModp_return_wit_2_in_place.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists Kout Out.
  entailer!.
Qed. 

Lemma proof_of_MontgInvModp_partial_solve_wit_1_non_alias_pure_split_goal_1 : MontgInvModp_partial_solve_wit_1_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_partial_solve_wit_1_non_alias_pure : MontgInvModp_partial_solve_wit_1_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_MontgInvModp_partial_solve_wit_2_in_place_pure_split_goal_1 : MontgInvModp_partial_solve_wit_2_in_place_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_partial_solve_wit_2_in_place_pure : MontgInvModp_partial_solve_wit_2_in_place_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_MontgInvModp_partial_solve_wit_37_non_alias_pure_split_goal_1 : MontgInvModp_partial_solve_wit_37_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_partial_solve_wit_37_non_alias_pure : MontgInvModp_partial_solve_wit_37_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia).
Qed. 

Lemma proof_of_MontgInvModp_partial_solve_wit_38_in_place_pure_split_goal_1 : MontgInvModp_partial_solve_wit_38_in_place_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_partial_solve_wit_38_in_place_pure : MontgInvModp_partial_solve_wit_38_in_place_pure.
Proof.
  LLM_pre_process ltac:(lia).
Qed. 

Lemma proof_of_MontgInvModp_partial_solve_wit_41_non_alias_pure_split_goal_1 : MontgInvModp_partial_solve_wit_41_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_partial_solve_wit_41_non_alias_pure : MontgInvModp_partial_solve_wit_41_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia).
Qed. 

Lemma proof_of_MontgInvModp_partial_solve_wit_42_in_place_pure_split_goal_1 : MontgInvModp_partial_solve_wit_42_in_place_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_partial_solve_wit_42_in_place_pure : MontgInvModp_partial_solve_wit_42_in_place_pure.
Proof.
  LLM_pre_process ltac:(lia).
Qed. 

Lemma proof_of_MontgInvModp_partial_solve_wit_43_non_alias_pure_split_goal_1 : MontgInvModp_partial_solve_wit_43_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_partial_solve_wit_43_non_alias_pure : MontgInvModp_partial_solve_wit_43_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia).
Qed. 

Lemma proof_of_MontgInvModp_partial_solve_wit_44_in_place_pure_split_goal_1 : MontgInvModp_partial_solve_wit_44_in_place_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_MontgInvModp_partial_solve_wit_44_in_place_pure : MontgInvModp_partial_solve_wit_44_in_place_pure.
Proof.
  LLM_pre_process ltac:(lia).
Qed. 

Lemma proof_of_MontgInvModp_derive_mont_in_place_by_in_place : MontgInvModp_derive_mont_in_place_by_in_place.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_fp, store_mod.
  Intros.
  Exists A_mont_in_place.
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    Intros K Z.
    destruct (sm2p_scaled_inverse_is_montgomery
      A_mont_in_place Z K) as [Ainv [HAinv [Hinverse Hresult]]].
    + assumption.
    + assumption.
    + lia.
    + assumption.
    + Exists Ainv.
      rewrite Hresult.
      entailer!.
Qed. 

Lemma proof_of_MontgInvModp_derive_mont_non_alias_by_non_alias : MontgInvModp_derive_mont_non_alias_by_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_fp, store_mod.
  Intros.
  Exists A_mont_non_alias.
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    Intros K Z.
    destruct (sm2p_scaled_inverse_is_montgomery
      A_mont_non_alias Z K) as [Ainv [HAinv [Hinverse Hresult]]].
    + assumption.
    + assumption.
    + lia.
    + assumption.
    + Exists Ainv.
      rewrite Hresult.
      entailer!.
Qed. 
