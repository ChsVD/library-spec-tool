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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import double_mod_p_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import double_mod_p_proof_auto.
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

Lemma proof_of_double_mod_p_return_wit_1_non_alias_split_goal_1 : double_mod_p_return_wit_1_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_1_non_alias_split_goal_2 : double_mod_p_return_wit_1_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_1_non_alias_split_goal_3 : double_mod_p_return_wit_1_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_1_non_alias_split_goal_4 : double_mod_p_return_wit_1_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_1_non_alias_split_goal_5 : double_mod_p_return_wit_1_non_alias_split_goal_5.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_1_non_alias_split_goal_6 : double_mod_p_return_wit_1_non_alias_split_goal_6.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_1_non_alias_split_goal_7 : double_mod_p_return_wit_1_non_alias_split_goal_7.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_1_non_alias_split_goal_8 : double_mod_p_return_wit_1_non_alias_split_goal_8.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_1_non_alias_split_goal_9 : double_mod_p_return_wit_1_non_alias_split_goal_9.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_1_non_alias_split_goal_10 : double_mod_p_return_wit_1_non_alias_split_goal_10.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_1_non_alias_split_goal_11 : double_mod_p_return_wit_1_non_alias_split_goal_11.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_1_non_alias : double_mod_p_return_wit_1_non_alias.
Proof.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct sm2_p_limbs as [HP0 [HP1 [HP2 [HP3 HPvalue]]]].
  rewrite Znth0_cons in PreH22.
  repeat rewrite Znth_cons in PreH17 by lia.
  rewrite Znth0_cons in PreH17.
  repeat rewrite Znth_cons in PreH12 by lia.
  rewrite Znth0_cons in PreH12.
  repeat rewrite Znth_cons in PreH7 by lia.
  rewrite Znth0_cons in PreH7.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_0 HP0) in PreH22.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_1 HP1) in PreH17.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_2 HP2) in PreH12.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_3 HP3) in PreH7.
  pose proof (u64_double_u128 x0 x1 ltac:(lia) ltac:(lia)) as Hlow.
  pose proof (u64_double_u128 x2 x3 ltac:(lia) ltac:(lia)) as Hhigh.
  destruct (u64_double_low_even x2) as [k2 Heven2].
  pose proof (u64_shiftr63_bit x1 ltac:(lia)) as Hbit1.
  pose proof
    (u64_lor_even_bit
       (unsigned_last_nbits (Z.shiftl x2 1) 64)
       (Z.shiftr x1 63) (ex_intro _ k2 Heven2) Hbit1) as Hmiddle.
  assert (Hdouble :
    2 * A_non_alias =
      u256_of_limbs
        (unsigned_last_nbits (Z.shiftl x0 1) 64)
        (Z.lor (unsigned_last_nbits (Z.shiftl x1 1) 64)
          (Z.shiftr x0 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x2 1) 64)
          (Z.shiftr x1 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x3 1) 64)
          (Z.shiftr x2 63)) +
      Z.shiftr x3 63 * U256_MOD).
  {
    rewrite PreH23.
    cbv [u256_of_limbs U64_MOD U256_MOD] in Hlow, Hhigh |- *.
    nia.
  }
  pose proof (u64_shiftr63_bit x3 ltac:(lia)) as Hbit3.
  assert (Hlast :
    unsigned_last_nbits (Z.shiftr x3 63) 8 = Z.shiftr x3 63).
  {
    apply unsigned_last_nbits_eq.
    destruct Hbit3; subst; lia.
  }
  rewrite Hlast in PreH2.
  assert (Hover : Z.shiftr x3 63 = 0) by (destruct Hbit3; lia).
  assert (Hsubtract :
    u256_of_limbs
        (unsigned_last_nbits (Z.shiftl x0 1) 64)
        (Z.lor (unsigned_last_nbits (Z.shiftl x1 1) 64)
          (Z.shiftr x0 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x2 1) 64)
          (Z.shiftr x1 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x3 1) 64)
          (Z.shiftr x2 63)) - SM2_P_Z =
      u256_of_limbs out out_2 out_3 out_4 +
        (retval_4 - 1) * U256_MOD).
  {
    rewrite HPvalue.
    pose proof
      (addcarry4_weighted_bridge U64_MOD
        (unsigned_last_nbits (Z.shiftl x0 1) 64)
        (Z.lor (unsigned_last_nbits (Z.shiftl x1 1) 64)
          (Z.shiftr x0 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x2 1) 64)
          (Z.shiftr x1 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x3 1) 64)
          (Z.shiftr x2 63))
        (U64_MOD - SM2_P_LIMB_0)
        (U64_MOD - 1 - SM2_P_LIMB_1)
        (U64_MOD - 1 - SM2_P_LIMB_2)
        (U64_MOD - 1 - SM2_P_LIMB_3)
        out out_2 out_3 out_4
        retval retval_2 retval_3 retval_4
        ltac:(lia) PreH17 PreH12 PreH7) as Hweighted.
    cbv [u256_of_limbs U64_MOD U256_MOD] in Hweighted |- *.
    nia.
  }
  pose proof
    (unsigned_Lastnbits_range (Z.shiftl x0 1) 64 ltac:(lia)) as Ht0.
  change (0 <= unsigned_last_nbits (Z.shiftl x0 1) 64 < U64_MOD) in Ht0.
  pose proof (u64_double_lor_range x1 x0 ltac:(lia) ltac:(lia)) as Ht1.
  pose proof (u64_double_lor_range x2 x1 ltac:(lia) ltac:(lia)) as Ht2.
  pose proof (u64_double_lor_range x3 x2 ltac:(lia) ltac:(lia)) as Ht3.
  pose proof
    (u256_of_limbs_range
      (unsigned_last_nbits (Z.shiftl x0 1) 64)
      (Z.lor (unsigned_last_nbits (Z.shiftl x1 1) 64)
        (Z.shiftr x0 63))
      (Z.lor (unsigned_last_nbits (Z.shiftl x2 1) 64)
        (Z.shiftr x1 63))
      (Z.lor (unsigned_last_nbits (Z.shiftl x3 1) 64)
        (Z.shiftr x2 63)) Ht0 Ht1 Ht2 Ht3) as Htmp_range.
  pose proof
    (u256_of_limbs_range out out_2 out_3 out_4
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hout_range.
  assert (Htmp_lt_p :
    u256_of_limbs
        (unsigned_last_nbits (Z.shiftl x0 1) 64)
        (Z.lor (unsigned_last_nbits (Z.shiftl x1 1) 64)
          (Z.shiftr x0 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x2 1) 64)
          (Z.shiftr x1 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x3 1) 64)
          (Z.shiftr x2 63)) < SM2_P_Z) by nia.
  assert (Hmod :
    Zmod (2 * A_non_alias) SM2_P_Z =
      u256_of_limbs
        (unsigned_last_nbits (Z.shiftl x0 1) 64)
        (Z.lor (unsigned_last_nbits (Z.shiftl x1 1) 64)
          (Z.shiftr x0 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x2 1) 64)
          (Z.shiftr x1 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x3 1) 64)
          (Z.shiftr x2 63))).
  {
    symmetry.
    apply (Zmod_unique
      (2 * A_non_alias) SM2_P_Z 0
      (u256_of_limbs
        (unsigned_last_nbits (Z.shiftl x0 1) 64)
        (Z.lor (unsigned_last_nbits (Z.shiftl x1 1) 64)
          (Z.shiftr x0 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x2 1) 64)
          (Z.shiftr x1 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x3 1) 64)
          (Z.shiftr x2 63)))); nia.
  }
  entailer!.
Qed. 

Lemma proof_of_double_mod_p_return_wit_2_non_alias_split_goal_1 : double_mod_p_return_wit_2_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_2_non_alias_split_goal_2 : double_mod_p_return_wit_2_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_2_non_alias_split_goal_3 : double_mod_p_return_wit_2_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_2_non_alias : double_mod_p_return_wit_2_non_alias.
Proof.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct sm2_p_limbs as [HP0 [HP1 [HP2 [HP3 HPvalue]]]].
  rewrite Znth0_cons in PreH21.
  repeat rewrite Znth_cons in PreH16 by lia.
  rewrite Znth0_cons in PreH16.
  repeat rewrite Znth_cons in PreH11 by lia.
  rewrite Znth0_cons in PreH11.
  repeat rewrite Znth_cons in PreH6 by lia.
  rewrite Znth0_cons in PreH6.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_0 HP0) in PreH21.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_1 HP1) in PreH16.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_2 HP2) in PreH11.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_3 HP3) in PreH6.
  pose proof (u64_double_u128 x0 x1 ltac:(lia) ltac:(lia)) as Hlow.
  pose proof (u64_double_u128 x2 x3 ltac:(lia) ltac:(lia)) as Hhigh.
  destruct (u64_double_low_even x2) as [k2 Heven2].
  pose proof (u64_shiftr63_bit x1 ltac:(lia)) as Hbit1.
  pose proof
    (u64_lor_even_bit
       (unsigned_last_nbits (Z.shiftl x2 1) 64)
       (Z.shiftr x1 63) (ex_intro _ k2 Heven2) Hbit1) as Hmiddle.
  assert (Hdouble :
    2 * A_non_alias =
      u256_of_limbs
        (unsigned_last_nbits (Z.shiftl x0 1) 64)
        (Z.lor (unsigned_last_nbits (Z.shiftl x1 1) 64)
          (Z.shiftr x0 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x2 1) 64)
          (Z.shiftr x1 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x3 1) 64)
          (Z.shiftr x2 63)) +
      Z.shiftr x3 63 * U256_MOD).
  {
    rewrite PreH22.
    cbv [u256_of_limbs U64_MOD U256_MOD] in Hlow, Hhigh |- *.
    nia.
  }
  pose proof (u64_shiftr63_bit x3 ltac:(lia)) as Hbit3.
  assert (Hlast :
    unsigned_last_nbits (Z.shiftr x3 63) 8 = Z.shiftr x3 63).
  {
    apply unsigned_last_nbits_eq.
    destruct Hbit3; subst; lia.
  }
  rewrite Hlast in PreH1.
  assert (Hover : Z.shiftr x3 63 = 1) by (destruct Hbit3; lia).
  assert (Hsubtract :
    u256_of_limbs
        (unsigned_last_nbits (Z.shiftl x0 1) 64)
        (Z.lor (unsigned_last_nbits (Z.shiftl x1 1) 64)
          (Z.shiftr x0 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x2 1) 64)
          (Z.shiftr x1 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x3 1) 64)
          (Z.shiftr x2 63)) - SM2_P_Z =
      u256_of_limbs out out_2 out_3 out_4 +
        (retval_4 - 1) * U256_MOD).
  {
    rewrite HPvalue.
    pose proof
      (addcarry4_weighted_bridge U64_MOD
        (unsigned_last_nbits (Z.shiftl x0 1) 64)
        (Z.lor (unsigned_last_nbits (Z.shiftl x1 1) 64)
          (Z.shiftr x0 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x2 1) 64)
          (Z.shiftr x1 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x3 1) 64)
          (Z.shiftr x2 63))
        (U64_MOD - SM2_P_LIMB_0)
        (U64_MOD - 1 - SM2_P_LIMB_1)
        (U64_MOD - 1 - SM2_P_LIMB_2)
        (U64_MOD - 1 - SM2_P_LIMB_3)
        out out_2 out_3 out_4
        retval retval_2 retval_3 retval_4
        ltac:(lia) PreH16 PreH11 PreH6) as Hweighted.
    cbv [u256_of_limbs U64_MOD U256_MOD] in Hweighted |- *.
    nia.
  }
  pose proof sm2_p_montgomery_bounds as [[HPpos HPupper] HPmorehalf].
  assert (Htmp_lt_p :
    u256_of_limbs
        (unsigned_last_nbits (Z.shiftl x0 1) 64)
        (Z.lor (unsigned_last_nbits (Z.shiftl x1 1) 64)
          (Z.shiftr x0 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x2 1) 64)
          (Z.shiftr x1 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x3 1) 64)
          (Z.shiftr x2 63)) < SM2_P_Z) by nia.
  pose proof
    (u256_of_limbs_range out out_2 out_3 out_4
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hout_range.
  assert (HU256 : 0 < U256_MOD) by (cbv [U256_MOD]; lia).
  assert (Hcarry : retval_4 = 0).
  {
    nia.
  }
  assert (Hresult :
    u256_of_limbs out out_2 out_3 out_4 =
      2 * A_non_alias - SM2_P_Z) by nia.
  assert (Hresult_range :
    0 <= u256_of_limbs out out_2 out_3 out_4 < SM2_P_Z).
  {
    split.
    - exact (proj1 Hout_range).
    - nia.
  }
  assert (Hmod :
    Zmod (2 * A_non_alias) SM2_P_Z =
      u256_of_limbs out out_2 out_3 out_4).
  {
    symmetry.
    apply (Zmod_unique
      (2 * A_non_alias) SM2_P_Z 1
      (u256_of_limbs out out_2 out_3 out_4)); lia.
  }
  entailer!.
Qed. 

Lemma proof_of_double_mod_p_return_wit_3_non_alias_split_goal_1 : double_mod_p_return_wit_3_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_3_non_alias_split_goal_2 : double_mod_p_return_wit_3_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_3_non_alias_split_goal_3 : double_mod_p_return_wit_3_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_double_mod_p_return_wit_3_non_alias : double_mod_p_return_wit_3_non_alias.
Proof.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct sm2_p_limbs as [HP0 [HP1 [HP2 [HP3 HPvalue]]]].
  rewrite Znth0_cons in PreH22.
  repeat rewrite Znth_cons in PreH17 by lia.
  rewrite Znth0_cons in PreH17.
  repeat rewrite Znth_cons in PreH12 by lia.
  rewrite Znth0_cons in PreH12.
  repeat rewrite Znth_cons in PreH7 by lia.
  rewrite Znth0_cons in PreH7.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_0 HP0) in PreH22.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_1 HP1) in PreH17.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_2 HP2) in PreH12.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_3 HP3) in PreH7.
  pose proof (u64_double_u128 x0 x1 ltac:(lia) ltac:(lia)) as Hlow.
  pose proof (u64_double_u128 x2 x3 ltac:(lia) ltac:(lia)) as Hhigh.
  destruct (u64_double_low_even x2) as [k2 Heven2].
  pose proof (u64_shiftr63_bit x1 ltac:(lia)) as Hbit1.
  pose proof
    (u64_lor_even_bit
       (unsigned_last_nbits (Z.shiftl x2 1) 64)
       (Z.shiftr x1 63) (ex_intro _ k2 Heven2) Hbit1) as Hmiddle.
  assert (Hdouble :
    2 * A_non_alias =
      u256_of_limbs
        (unsigned_last_nbits (Z.shiftl x0 1) 64)
        (Z.lor (unsigned_last_nbits (Z.shiftl x1 1) 64)
          (Z.shiftr x0 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x2 1) 64)
          (Z.shiftr x1 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x3 1) 64)
          (Z.shiftr x2 63)) +
      Z.shiftr x3 63 * U256_MOD).
  {
    rewrite PreH23.
    cbv [u256_of_limbs U64_MOD U256_MOD] in Hlow, Hhigh |- *.
    nia.
  }
  pose proof (u64_shiftr63_bit x3 ltac:(lia)) as Hbit3.
  assert (Hlast :
    unsigned_last_nbits (Z.shiftr x3 63) 8 = Z.shiftr x3 63).
  {
    apply unsigned_last_nbits_eq.
    destruct Hbit3; subst; lia.
  }
  rewrite Hlast in PreH2.
  assert (Hover : Z.shiftr x3 63 = 0) by (destruct Hbit3; lia).
  assert (Hsubtract :
    u256_of_limbs
        (unsigned_last_nbits (Z.shiftl x0 1) 64)
        (Z.lor (unsigned_last_nbits (Z.shiftl x1 1) 64)
          (Z.shiftr x0 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x2 1) 64)
          (Z.shiftr x1 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x3 1) 64)
          (Z.shiftr x2 63)) - SM2_P_Z =
      u256_of_limbs out out_2 out_3 out_4 +
        (retval_4 - 1) * U256_MOD).
  {
    rewrite HPvalue.
    pose proof
      (addcarry4_weighted_bridge U64_MOD
        (unsigned_last_nbits (Z.shiftl x0 1) 64)
        (Z.lor (unsigned_last_nbits (Z.shiftl x1 1) 64)
          (Z.shiftr x0 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x2 1) 64)
          (Z.shiftr x1 63))
        (Z.lor (unsigned_last_nbits (Z.shiftl x3 1) 64)
          (Z.shiftr x2 63))
        (U64_MOD - SM2_P_LIMB_0)
        (U64_MOD - 1 - SM2_P_LIMB_1)
        (U64_MOD - 1 - SM2_P_LIMB_2)
        (U64_MOD - 1 - SM2_P_LIMB_3)
        out out_2 out_3 out_4
        retval retval_2 retval_3 retval_4
        ltac:(lia) PreH17 PreH12 PreH7) as Hweighted.
    cbv [u256_of_limbs U64_MOD U256_MOD] in Hweighted |- *.
    nia.
  }
  assert (Hcarry : retval_4 = 1) by lia.
  assert (Hresult :
    u256_of_limbs out out_2 out_3 out_4 =
      2 * A_non_alias - SM2_P_Z) by nia.
  pose proof
    (u256_of_limbs_range out out_2 out_3 out_4
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hout_range.
  assert (Hresult_range :
    0 <= u256_of_limbs out out_2 out_3 out_4 < SM2_P_Z) by nia.
  assert (Hmod :
    Zmod (2 * A_non_alias) SM2_P_Z =
      u256_of_limbs out out_2 out_3 out_4).
  {
    symmetry.
    apply (Zmod_unique
      (2 * A_non_alias) SM2_P_Z 1
      (u256_of_limbs out out_2 out_3 out_4)); lia.
  }
  entailer!.
Qed. 

Lemma proof_of_double_mod_p_partial_solve_wit_6_non_alias_pure_split_goal_1 : double_mod_p_partial_solve_wit_6_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_double_mod_p_partial_solve_wit_6_non_alias_pure_split_goal_2 : double_mod_p_partial_solve_wit_6_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_double_mod_p_partial_solve_wit_6_non_alias_pure_split_goal_3 : double_mod_p_partial_solve_wit_6_non_alias_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_double_mod_p_partial_solve_wit_6_non_alias_pure : double_mod_p_partial_solve_wit_6_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof sm2_p_limbs as HP.
  pose proof (unsigned_lnot_u64_range SM2_P_LIMB_0 ltac:(lia)) as Hnot.
  pose proof
    (unsigned_Lastnbits_range (Z.shiftl x0 1) 64 ltac:(lia)) as Hshift.
  entailer!.
Qed. 

Lemma proof_of_double_mod_p_partial_solve_wit_8_non_alias_pure_split_goal_1 : double_mod_p_partial_solve_wit_8_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_double_mod_p_partial_solve_wit_8_non_alias_pure_split_goal_2 : double_mod_p_partial_solve_wit_8_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_double_mod_p_partial_solve_wit_8_non_alias_pure_split_goal_3 : double_mod_p_partial_solve_wit_8_non_alias_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_double_mod_p_partial_solve_wit_8_non_alias_pure : double_mod_p_partial_solve_wit_8_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof sm2_p_limbs as HP.
  pose proof (unsigned_lnot_u64_range SM2_P_LIMB_1 ltac:(lia)) as Hnot.
  pose proof (u64_double_lor_range x1 x0 ltac:(lia) ltac:(lia)) as Hlor.
  entailer!.
Qed. 

Lemma proof_of_double_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_1 : double_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_double_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_2 : double_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_double_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_3 : double_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_double_mod_p_partial_solve_wit_10_non_alias_pure : double_mod_p_partial_solve_wit_10_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof sm2_p_limbs as HP.
  pose proof (unsigned_lnot_u64_range SM2_P_LIMB_2 ltac:(lia)) as Hnot.
  pose proof (u64_double_lor_range x2 x1 ltac:(lia) ltac:(lia)) as Hlor.
  entailer!.
Qed. 

Lemma proof_of_double_mod_p_partial_solve_wit_12_non_alias_pure_split_goal_1 : double_mod_p_partial_solve_wit_12_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_double_mod_p_partial_solve_wit_12_non_alias_pure_split_goal_2 : double_mod_p_partial_solve_wit_12_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_double_mod_p_partial_solve_wit_12_non_alias_pure_split_goal_3 : double_mod_p_partial_solve_wit_12_non_alias_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_double_mod_p_partial_solve_wit_12_non_alias_pure : double_mod_p_partial_solve_wit_12_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof sm2_p_limbs as HP.
  pose proof (unsigned_lnot_u64_range SM2_P_LIMB_3 ltac:(lia)) as Hnot.
  pose proof (u64_double_lor_range x3 x2 ltac:(lia) ltac:(lia)) as Hlor.
  entailer!.
Qed. 
