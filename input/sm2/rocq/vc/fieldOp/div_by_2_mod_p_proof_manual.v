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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import div_by_2_mod_p_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import div_by_2_mod_p_proof_auto.
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

Lemma proof_of_div_by_2_mod_p_entail_wit_4_non_alias_split_goal_1 : div_by_2_mod_p_entail_wit_4_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_entail_wit_4_non_alias_split_goal_2 : div_by_2_mod_p_entail_wit_4_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_entail_wit_4_non_alias_split_goal_3 : div_by_2_mod_p_entail_wit_4_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_entail_wit_4_non_alias_split_goal_4 : div_by_2_mod_p_entail_wit_4_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_entail_wit_4_non_alias : div_by_2_mod_p_entail_wit_4_non_alias.
Proof.
  unfold div_by_2_mod_p_entail_wit_4_non_alias; right; intros.
  change (x0 + SM2_P_LIMB_0 + 0 =
          out + retval_2 * U64_MOD) in PreH20.
  change (x1 + SM2_P_LIMB_1 + retval_2 =
          out_2 + retval_3 * U64_MOD) in PreH15.
  change (x2 + SM2_P_LIMB_2 + retval_3 =
          out_3 + retval_4 * U64_MOD) in PreH10.
  change (x3 + SM2_P_LIMB_3 + retval_4 =
          out_4 + retval * U64_MOD) in PreH5.
  change (Z.land x0 1 <> 0) in PreH33.
  assert (Hout_list :
    replace_Znth 3 out_4
      (replace_Znth 2 out_3
        (replace_Znth 1 out_2
          (replace_Znth 0 out (x0 :: x1 :: x2 :: x3 :: nil)))) =
    out :: out_2 :: out_3 :: out_4 :: nil) by reflexivity.
  rewrite Hout_list, !u64_list_value_four.
  pose proof (add_sm2_p_carry_chain
    A_non_alias x0 x1 x2 x3 out out_2 out_3 out_4
    retval_2 retval_3 retval_4 retval
    PreH21 ltac:(lia) PreH15 PreH10 PreH5) as Hadd.
  pose proof (fp_div2_adjusted_odd
    A_non_alias x0 x1 x2 x3 PreH21 PreH33) as Hadj.
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    (conj PreH16 PreH17) (conj PreH11 PreH12)
    (conj PreH6 PreH7) (conj PreH1 PreH2)) as Hrange.
  entailer!.
Qed. 

Lemma proof_of_div_by_2_mod_p_entail_wit_5_in_place : div_by_2_mod_p_entail_wit_5_in_place.
Proof.
  unfold div_by_2_mod_p_entail_wit_5_in_place; right; intros.
  change (x0 + SM2_P_LIMB_0 + 0 =
          out + retval_2 * U64_MOD) in PreH20.
  change (x1 + SM2_P_LIMB_1 + retval_2 =
          out_2 + retval_3 * U64_MOD) in PreH15.
  change (x2 + SM2_P_LIMB_2 + retval_3 =
          out_3 + retval_4 * U64_MOD) in PreH10.
  change (x3 + SM2_P_LIMB_3 + retval_4 =
          out_4 + retval * U64_MOD) in PreH5.
  change (Z.land x0 1 <> 0) in PreH33.
  assert (Hout_list :
    replace_Znth 3 out_4
      (replace_Znth 2 out_3
        (replace_Znth 1 out_2
          (replace_Znth 0 out (x0 :: x1 :: x2 :: x3 :: nil)))) =
    out :: out_2 :: out_3 :: out_4 :: nil) by reflexivity.
  rewrite Hout_list, !u64_list_value_four.
  pose proof (add_sm2_p_carry_chain
    A_in_place x0 x1 x2 x3 out out_2 out_3 out_4
    retval_2 retval_3 retval_4 retval
    PreH21 ltac:(lia) PreH15 PreH10 PreH5) as Hadd.
  pose proof (fp_div2_adjusted_odd
    A_in_place x0 x1 x2 x3 PreH21 PreH33) as Hadj.
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    (conj PreH16 PreH17) (conj PreH11 PreH12)
    (conj PreH6 PreH7) (conj PreH1 PreH2)) as Hrange.
  subst result_pre.
  unfold UInt64Array.full, store_array.
  cbn [store_array_rec].
  Exists x3 x2 x1 x0.
  csimpl.
  entailer!.
  replace (0 + 1) with 1 by lia.
  replace (1 + 1) with 2 by lia.
  replace (2 + 1) with 3 by lia.
  cancel.
Qed. 

Lemma proof_of_div_by_2_mod_p_return_wit_1_in_place_split_goal_1 : div_by_2_mod_p_return_wit_1_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_1_in_place_split_goal_2 : div_by_2_mod_p_return_wit_1_in_place_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_1_in_place_split_goal_3 : div_by_2_mod_p_return_wit_1_in_place_split_goal_3.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_1_in_place_split_goal_4 : div_by_2_mod_p_return_wit_1_in_place_split_goal_4.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_1_in_place_split_goal_5 : div_by_2_mod_p_return_wit_1_in_place_split_goal_5.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_1_in_place_split_goal_6 : div_by_2_mod_p_return_wit_1_in_place_split_goal_6.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_1_in_place_split_goal_7 : div_by_2_mod_p_return_wit_1_in_place_split_goal_7.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_1_in_place_split_goal_8 : div_by_2_mod_p_return_wit_1_in_place_split_goal_8.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_1_in_place_split_goal_9 : div_by_2_mod_p_return_wit_1_in_place_split_goal_9.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_1_in_place_split_goal_10 : div_by_2_mod_p_return_wit_1_in_place_split_goal_10.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_1_in_place_split_goal_11 : div_by_2_mod_p_return_wit_1_in_place_split_goal_11.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_1_in_place : div_by_2_mod_p_return_wit_1_in_place.
Proof.
  unfold div_by_2_mod_p_return_wit_1_in_place; right; intros.
  assert (HC : C = 1) by lia.
  pose proof (fp_div2_bounds A_in_place (conj PreH20 PreH19)) as Hfp.
  pose proof (u64_shift_join_range x0 x1 (conj PreH18 PreH17) (conj PreH16 PreH15)) as Hr0.
  pose proof (u64_shift_join_range x1 x2 (conj PreH16 PreH15) (conj PreH14 PreH13)) as Hr1.
  pose proof (u64_shift_join_range x2 x3 (conj PreH14 PreH13) (conj PreH12 PreH11)) as Hr2.
  pose proof (u64_shift_top_carry_range x3 (conj PreH12 PreH11)) as Hr3.
  pose proof (u256_shift_right_one_with_carry x0 x1 x2 x3
    (conj PreH18 PreH17) (conj PreH16 PreH15)
    (conj PreH14 PreH13) (conj PreH12 PreH11)) as Hshift.
  pose proof (fp_div2_adjusted_twice A_in_place) as Htwice.
  assert (Hvalue : fp_div2 A_in_place =
    u256_of_limbs
      (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits (Z.shiftl x1 63) 64))
      (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits (Z.shiftl x2 63) 64))
      (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits (Z.shiftl x3 63) 64))
      (Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63))).
  { rewrite Hshift.
    assert (Hadjust : fp_div2_adjusted A_in_place =
      u256_of_limbs x0 x1 x2 x3 + U256_MOD).
    { rewrite PreH26, PreH10, HC; ring. }
    rewrite <- Hadjust, Htwice.
    rewrite Z.mul_comm, Z.div_mul by lia.
    reflexivity. }
  entailer!.
Qed. 

Lemma proof_of_div_by_2_mod_p_return_wit_2_non_alias_split_goal_1 : div_by_2_mod_p_return_wit_2_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_2_non_alias_split_goal_2 : div_by_2_mod_p_return_wit_2_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_2_non_alias_split_goal_3 : div_by_2_mod_p_return_wit_2_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_2_non_alias_split_goal_4 : div_by_2_mod_p_return_wit_2_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_2_non_alias_split_goal_5 : div_by_2_mod_p_return_wit_2_non_alias_split_goal_5.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_2_non_alias_split_goal_6 : div_by_2_mod_p_return_wit_2_non_alias_split_goal_6.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_2_non_alias_split_goal_7 : div_by_2_mod_p_return_wit_2_non_alias_split_goal_7.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_2_non_alias_split_goal_8 : div_by_2_mod_p_return_wit_2_non_alias_split_goal_8.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_2_non_alias_split_goal_9 : div_by_2_mod_p_return_wit_2_non_alias_split_goal_9.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_2_non_alias_split_goal_10 : div_by_2_mod_p_return_wit_2_non_alias_split_goal_10.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_2_non_alias_split_goal_11 : div_by_2_mod_p_return_wit_2_non_alias_split_goal_11.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_2_non_alias : div_by_2_mod_p_return_wit_2_non_alias.
Proof.
  unfold div_by_2_mod_p_return_wit_2_non_alias; right; intros.
  assert (HC : C = 1) by lia.
  pose proof (fp_div2_bounds A_non_alias (conj PreH20 PreH19)) as Hfp.
  pose proof (u64_shift_join_range x0 x1 (conj PreH18 PreH17) (conj PreH16 PreH15)) as Hr0.
  pose proof (u64_shift_join_range x1 x2 (conj PreH16 PreH15) (conj PreH14 PreH13)) as Hr1.
  pose proof (u64_shift_join_range x2 x3 (conj PreH14 PreH13) (conj PreH12 PreH11)) as Hr2.
  pose proof (u64_shift_top_carry_range x3 (conj PreH12 PreH11)) as Hr3.
  pose proof (u256_shift_right_one_with_carry x0 x1 x2 x3
    (conj PreH18 PreH17) (conj PreH16 PreH15)
    (conj PreH14 PreH13) (conj PreH12 PreH11)) as Hshift.
  pose proof (fp_div2_adjusted_twice A_non_alias) as Htwice.
  assert (Hvalue : fp_div2 A_non_alias =
    u256_of_limbs
      (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits (Z.shiftl x1 63) 64))
      (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits (Z.shiftl x2 63) 64))
      (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits (Z.shiftl x3 63) 64))
      (Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63))).
  { rewrite Hshift.
    assert (Hadjust : fp_div2_adjusted A_non_alias =
      u256_of_limbs x0 x1 x2 x3 + U256_MOD).
    { rewrite PreH25, PreH10, HC; ring. }
    rewrite <- Hadjust, Htwice.
    rewrite Z.mul_comm, Z.div_mul by lia.
    reflexivity. }
  entailer!.
Qed. 

Lemma proof_of_div_by_2_mod_p_return_wit_3_in_place_split_goal_1 : div_by_2_mod_p_return_wit_3_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_3_in_place_split_goal_2 : div_by_2_mod_p_return_wit_3_in_place_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_3_in_place_split_goal_3 : div_by_2_mod_p_return_wit_3_in_place_split_goal_3.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_3_in_place_split_goal_4 : div_by_2_mod_p_return_wit_3_in_place_split_goal_4.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_3_in_place_split_goal_5 : div_by_2_mod_p_return_wit_3_in_place_split_goal_5.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_3_in_place_split_goal_6 : div_by_2_mod_p_return_wit_3_in_place_split_goal_6.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_3_in_place_split_goal_7 : div_by_2_mod_p_return_wit_3_in_place_split_goal_7.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_3_in_place_split_goal_8 : div_by_2_mod_p_return_wit_3_in_place_split_goal_8.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_3_in_place_split_goal_9 : div_by_2_mod_p_return_wit_3_in_place_split_goal_9.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_3_in_place_split_goal_10 : div_by_2_mod_p_return_wit_3_in_place_split_goal_10.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_3_in_place_split_goal_11 : div_by_2_mod_p_return_wit_3_in_place_split_goal_11.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_3_in_place : div_by_2_mod_p_return_wit_3_in_place.
Proof.
  unfold div_by_2_mod_p_return_wit_3_in_place; right; intros.
  pose proof (fp_div2_bounds A_in_place (conj PreH20 PreH19)) as Hfp.
  pose proof (u64_shift_join_range x0 x1 (conj PreH18 PreH17) (conj PreH16 PreH15)) as Hr0.
  pose proof (u64_shift_join_range x1 x2 (conj PreH16 PreH15) (conj PreH14 PreH13)) as Hr1.
  pose proof (u64_shift_join_range x2 x3 (conj PreH14 PreH13) (conj PreH12 PreH11)) as Hr2.
  assert (Hr3 : 0 <= Z.shiftr x3 1 < U64_MOD).
  { rewrite Z.shiftr_div_pow2 by lia; unfold U64_MOD in *;
    split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  pose proof (u256_shift_right_one x0 x1 x2 x3
    (conj PreH18 PreH17) (conj PreH16 PreH15)
    (conj PreH14 PreH13) (conj PreH12 PreH11)) as Hshift.
  pose proof (fp_div2_adjusted_twice A_in_place) as Htwice.
  assert (Hvalue : fp_div2 A_in_place =
    u256_of_limbs
      (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits (Z.shiftl x1 63) 64))
      (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits (Z.shiftl x2 63) 64))
      (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits (Z.shiftl x3 63) 64))
      (Z.shiftr x3 1)).
  { rewrite Hshift.
    assert (Hadjust : fp_div2_adjusted A_in_place =
      u256_of_limbs x0 x1 x2 x3).
    { rewrite PreH26, PreH10, PreH27; ring. }
    rewrite <- Hadjust, Htwice.
    rewrite Z.mul_comm, Z.div_mul by lia.
    reflexivity. }
  entailer!.
Qed. 

Lemma proof_of_div_by_2_mod_p_return_wit_4_non_alias_split_goal_1 : div_by_2_mod_p_return_wit_4_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_4_non_alias_split_goal_2 : div_by_2_mod_p_return_wit_4_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_4_non_alias_split_goal_3 : div_by_2_mod_p_return_wit_4_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_4_non_alias_split_goal_4 : div_by_2_mod_p_return_wit_4_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_4_non_alias_split_goal_5 : div_by_2_mod_p_return_wit_4_non_alias_split_goal_5.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_4_non_alias_split_goal_6 : div_by_2_mod_p_return_wit_4_non_alias_split_goal_6.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_4_non_alias_split_goal_7 : div_by_2_mod_p_return_wit_4_non_alias_split_goal_7.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_4_non_alias_split_goal_8 : div_by_2_mod_p_return_wit_4_non_alias_split_goal_8.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_4_non_alias_split_goal_9 : div_by_2_mod_p_return_wit_4_non_alias_split_goal_9.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_4_non_alias_split_goal_10 : div_by_2_mod_p_return_wit_4_non_alias_split_goal_10.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_4_non_alias_split_goal_11 : div_by_2_mod_p_return_wit_4_non_alias_split_goal_11.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_4_non_alias : div_by_2_mod_p_return_wit_4_non_alias.
Proof.
  unfold div_by_2_mod_p_return_wit_4_non_alias; right; intros.
  pose proof (fp_div2_bounds A_non_alias (conj PreH20 PreH19)) as Hfp.
  pose proof (u64_shift_join_range x0 x1 (conj PreH18 PreH17) (conj PreH16 PreH15)) as Hr0.
  pose proof (u64_shift_join_range x1 x2 (conj PreH16 PreH15) (conj PreH14 PreH13)) as Hr1.
  pose proof (u64_shift_join_range x2 x3 (conj PreH14 PreH13) (conj PreH12 PreH11)) as Hr2.
  assert (Hr3 : 0 <= Z.shiftr x3 1 < U64_MOD).
  { rewrite Z.shiftr_div_pow2 by lia; unfold U64_MOD in *;
    split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  pose proof (u256_shift_right_one x0 x1 x2 x3
    (conj PreH18 PreH17) (conj PreH16 PreH15)
    (conj PreH14 PreH13) (conj PreH12 PreH11)) as Hshift.
  pose proof (fp_div2_adjusted_twice A_non_alias) as Htwice.
  assert (Hvalue : fp_div2 A_non_alias =
    u256_of_limbs
      (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits (Z.shiftl x1 63) 64))
      (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits (Z.shiftl x2 63) 64))
      (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits (Z.shiftl x3 63) 64))
      (Z.shiftr x3 1)).
  { rewrite Hshift.
    assert (Hadjust : fp_div2_adjusted A_non_alias =
      u256_of_limbs x0 x1 x2 x3).
    { rewrite PreH25, PreH10, PreH26; ring. }
    rewrite <- Hadjust, Htwice.
    rewrite Z.mul_comm, Z.div_mul by lia.
    reflexivity. }
  entailer!.
Qed. 

Lemma proof_of_div_by_2_mod_p_return_wit_5_in_place_split_goal_1 : div_by_2_mod_p_return_wit_5_in_place_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_5_in_place_split_goal_2 : div_by_2_mod_p_return_wit_5_in_place_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_5_in_place_split_goal_3 : div_by_2_mod_p_return_wit_5_in_place_split_goal_3.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_5_in_place_split_goal_4 : div_by_2_mod_p_return_wit_5_in_place_split_goal_4.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_5_in_place_split_goal_5 : div_by_2_mod_p_return_wit_5_in_place_split_goal_5.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_5_in_place_split_goal_6 : div_by_2_mod_p_return_wit_5_in_place_split_goal_6.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_5_in_place_split_goal_7 : div_by_2_mod_p_return_wit_5_in_place_split_goal_7.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_5_in_place_split_goal_8 : div_by_2_mod_p_return_wit_5_in_place_split_goal_8.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_5_in_place_split_goal_9 : div_by_2_mod_p_return_wit_5_in_place_split_goal_9.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_5_in_place_split_goal_10 : div_by_2_mod_p_return_wit_5_in_place_split_goal_10.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_5_in_place_split_goal_11 : div_by_2_mod_p_return_wit_5_in_place_split_goal_11.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_5_in_place_split_goal_spatial : div_by_2_mod_p_return_wit_5_in_place_split_goal_spatial.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_5_in_place : div_by_2_mod_p_return_wit_5_in_place.
Proof.
  unfold div_by_2_mod_p_return_wit_5_in_place; right; intros.
  pose proof (fp_div2_bounds A_in_place (conj PreH19 PreH18)) as Hfp.
  pose proof (u64_shift_join_range x0 x1
    (conj PreH17 PreH16) (conj PreH15 PreH14)) as Hr0.
  pose proof (u64_shift_join_range x1 x2
    (conj PreH15 PreH14) (conj PreH13 PreH12)) as Hr1.
  pose proof (u64_shift_join_range x2 x3
    (conj PreH13 PreH12) (conj PreH11 PreH10)) as Hr2.
  assert (Hr3 : 0 <= Z.shiftr x3 1 < U64_MOD).
  { rewrite Z.shiftr_div_pow2 by lia; unfold U64_MOD in *;
    split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  pose proof (fp_div2_even A_in_place x0 x1 x2 x3
    PreH9 PreH21 (conj PreH17 PreH16) (conj PreH15 PreH14)
    (conj PreH13 PreH12) (conj PreH11 PreH10)) as Hvalue.
  entailer!.
  unfold store_sm2_p, store_u256_limbs.
  Exists SM2_P_LIMB_0 SM2_P_LIMB_1 SM2_P_LIMB_2 SM2_P_LIMB_3.
  pose proof sm2_p_limbs as Hp.
  simpl.
  entailer!.
  repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia].
  cancel.
Qed. 

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_1 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_2 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_3 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_4 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_5 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_5.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_6 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_6.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_7 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_7.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_8 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_8.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_9 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_9.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_10 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_10.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_11 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_11.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_12 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_12.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_13 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_13.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_14 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_14.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_15 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_15.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_16 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_16.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_17 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_17.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_18 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_18.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_19 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_19.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_20 : div_by_2_mod_p_return_wit_6_non_alias_split_goal_20.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias_split_goal_spatial : div_by_2_mod_p_return_wit_6_non_alias_split_goal_spatial.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_return_wit_6_non_alias : div_by_2_mod_p_return_wit_6_non_alias.
Proof.
  unfold div_by_2_mod_p_return_wit_6_non_alias; right; intros.
  pose proof (fp_div2_bounds A_non_alias (conj PreH19 PreH18)) as Hfp.
  pose proof (u64_shift_join_range x0 x1
    (conj PreH17 PreH16) (conj PreH15 PreH14)) as Hr0.
  pose proof (u64_shift_join_range x1 x2
    (conj PreH15 PreH14) (conj PreH13 PreH12)) as Hr1.
  pose proof (u64_shift_join_range x2 x3
    (conj PreH13 PreH12) (conj PreH11 PreH10)) as Hr2.
  assert (Hr3 : 0 <= Z.shiftr x3 1 < U64_MOD).
  { rewrite Z.shiftr_div_pow2 by lia; unfold U64_MOD in *;
    split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  pose proof (fp_div2_even A_non_alias x0 x1 x2 x3
    PreH9 PreH21 (conj PreH17 PreH16) (conj PreH15 PreH14)
    (conj PreH13 PreH12) (conj PreH11 PreH10)) as Hvalue.
  entailer!.
  unfold store_sm2_p, store_u256_limbs.
  Exists SM2_P_LIMB_0 SM2_P_LIMB_1 SM2_P_LIMB_2 SM2_P_LIMB_3.
  pose proof sm2_p_limbs as Hp.
  simpl.
  entailer!.
  repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia].
  cancel.
Qed. 

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_7_in_place_pure_split_goal_1 : div_by_2_mod_p_partial_solve_wit_7_in_place_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_7_in_place_pure_split_goal_2 : div_by_2_mod_p_partial_solve_wit_7_in_place_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_7_in_place_pure : div_by_2_mod_p_partial_solve_wit_7_in_place_pure.
Proof. unfold div_by_2_mod_p_partial_solve_wit_7_in_place_pure; right; intros; pose proof sm2_p_limbs; entailer!. Qed. 

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_1 : div_by_2_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_2 : div_by_2_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_10_non_alias_pure : div_by_2_mod_p_partial_solve_wit_10_non_alias_pure.
Proof. unfold div_by_2_mod_p_partial_solve_wit_10_non_alias_pure; right; intros; pose proof sm2_p_limbs; entailer!. Qed. 

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_13_in_place_pure_split_goal_1 : div_by_2_mod_p_partial_solve_wit_13_in_place_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_13_in_place_pure_split_goal_2 : div_by_2_mod_p_partial_solve_wit_13_in_place_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_13_in_place_pure_split_goal_3 : div_by_2_mod_p_partial_solve_wit_13_in_place_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_13_in_place_pure_split_goal_4 : div_by_2_mod_p_partial_solve_wit_13_in_place_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_13_in_place_pure : div_by_2_mod_p_partial_solve_wit_13_in_place_pure.
Proof. unfold div_by_2_mod_p_partial_solve_wit_13_in_place_pure; right; intros; pose proof sm2_p_limbs; entailer!. Qed. 

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_16_non_alias_pure_split_goal_1 : div_by_2_mod_p_partial_solve_wit_16_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_16_non_alias_pure_split_goal_2 : div_by_2_mod_p_partial_solve_wit_16_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_16_non_alias_pure_split_goal_3 : div_by_2_mod_p_partial_solve_wit_16_non_alias_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_16_non_alias_pure_split_goal_4 : div_by_2_mod_p_partial_solve_wit_16_non_alias_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_16_non_alias_pure : div_by_2_mod_p_partial_solve_wit_16_non_alias_pure.
Proof. unfold div_by_2_mod_p_partial_solve_wit_16_non_alias_pure; right; intros; pose proof sm2_p_limbs; entailer!. Qed. 

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_19_in_place_pure_split_goal_1 : div_by_2_mod_p_partial_solve_wit_19_in_place_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_19_in_place_pure_split_goal_2 : div_by_2_mod_p_partial_solve_wit_19_in_place_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_19_in_place_pure_split_goal_3 : div_by_2_mod_p_partial_solve_wit_19_in_place_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_19_in_place_pure_split_goal_4 : div_by_2_mod_p_partial_solve_wit_19_in_place_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_19_in_place_pure : div_by_2_mod_p_partial_solve_wit_19_in_place_pure.
Proof. unfold div_by_2_mod_p_partial_solve_wit_19_in_place_pure; right; intros; pose proof sm2_p_limbs; entailer!. Qed. 

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_1 : div_by_2_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_2 : div_by_2_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_3 : div_by_2_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_4 : div_by_2_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_22_non_alias_pure : div_by_2_mod_p_partial_solve_wit_22_non_alias_pure.
Proof. unfold div_by_2_mod_p_partial_solve_wit_22_non_alias_pure; right; intros; pose proof sm2_p_limbs; entailer!. Qed. 

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_25_in_place_pure_split_goal_1 : div_by_2_mod_p_partial_solve_wit_25_in_place_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_25_in_place_pure_split_goal_2 : div_by_2_mod_p_partial_solve_wit_25_in_place_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_25_in_place_pure_split_goal_3 : div_by_2_mod_p_partial_solve_wit_25_in_place_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_25_in_place_pure_split_goal_4 : div_by_2_mod_p_partial_solve_wit_25_in_place_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_25_in_place_pure : div_by_2_mod_p_partial_solve_wit_25_in_place_pure.
Proof. unfold div_by_2_mod_p_partial_solve_wit_25_in_place_pure; right; intros; pose proof sm2_p_limbs; entailer!. Qed. 

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_28_non_alias_pure_split_goal_1 : div_by_2_mod_p_partial_solve_wit_28_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_28_non_alias_pure_split_goal_2 : div_by_2_mod_p_partial_solve_wit_28_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_28_non_alias_pure_split_goal_3 : div_by_2_mod_p_partial_solve_wit_28_non_alias_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_28_non_alias_pure_split_goal_4 : div_by_2_mod_p_partial_solve_wit_28_non_alias_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_div_by_2_mod_p_partial_solve_wit_28_non_alias_pure : div_by_2_mod_p_partial_solve_wit_28_non_alias_pure.
Proof. unfold div_by_2_mod_p_partial_solve_wit_28_non_alias_pure; right; intros; pose proof sm2_p_limbs; entailer!. Qed. 

Lemma proof_of_div_by_2_mod_p_derive_mont_non_alias_by_non_alias : div_by_2_mod_p_derive_mont_non_alias_by_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename A_mont_non_alias into A.
  Exists (mont_p A).
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    rewrite ec_math_refinement.fp_div2_mont.
    entailer!.
Qed. 
