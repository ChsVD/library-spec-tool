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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import add_mod_p_def.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import add_mod_p_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import add_mod_p_proof_auto.
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

Lemma proof_of_add_mod_p_entail_wit_8_1_non_alias : add_mod_p_entail_wit_8_1_non_alias.
Proof.
  unfold add_mod_p_entail_wit_8_1_non_alias.
  right; intros.
  repeat first [rewrite Znth0_cons in * | rewrite Znth_cons in * by lia].
  rewrite Z.lor_eq_0_iff in PreH9.
  destruct PreH9 as [Hcarry Hborrow].
  pose proof sm2_p_limbs as (HP0 & HP1 & HP2 & HP3 & HPvalue).
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_0 HP0) in PreH29.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_1 HP1) in PreH24.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_2 HP2) in PreH19.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_3 HP3) in PreH14.
  assert (Hadd : A_non_alias + B_non_alias =
    u256_of_limbs out out_2 out_3 out_4 + retval_4 * U256_MOD).
  {
    rewrite PreH59, PreH50.
    apply (u256_add_carry_chain
      x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
      out out_2 out_3 out_4 retval retval_2 retval_3 retval_4); lia.
  }
  assert (Hsub :
    u256_of_limbs out out_2 out_3 out_4 + U256_MOD - SM2_P_Z =
    u256_of_limbs out_5 out_6 out_7 out_8 + retval_8 * U256_MOD).
  {
    rewrite HPvalue.
    cbv [u256_of_limbs U64_MOD U256_MOD] in *.
    lia.
  }
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HT.
  pose proof (u256_of_limbs_range out_5 out_6 out_7 out_8
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  assert (Hvalue : Zmod (A_non_alias + B_non_alias) SM2_P_Z =
    u256_of_limbs out out_2 out_3 out_4).
  {
    rewrite Hcarry in Hadd.
    rewrite Hborrow in Hsub.
    cbn in Hadd, Hsub.
    rewrite Hadd.
    replace (u256_of_limbs out out_2 out_3 out_4 + 0)
      with (u256_of_limbs out out_2 out_3 out_4) by lia.
    apply Z.mod_small.
    destruct sm2_p_montgomery_bounds as [[HPpos HPlt] HPhalf].
    cbv [U256_MOD SM2_P_Z] in HT, HD |- *; lia.
  }
  assert (Htmpmod : Zmod (A_non_alias + B_non_alias) U256_MOD =
    u256_of_limbs out out_2 out_3 out_4).
  {
    rewrite Hcarry in Hadd.
    cbn in Hadd.
    rewrite Hadd.
    replace (u256_of_limbs out out_2 out_3 out_4 + 0)
      with (u256_of_limbs out out_2 out_3 out_4) by lia.
    apply Z.mod_small. exact HT.
  }
  assert (Hbounded :
    u64_list_bounded (out :: out_2 :: out_3 :: out_4 :: nil)).
  {
    unfold u64_list_bounded.
    repeat rewrite limb_list_bounded_cons_iff.
    repeat split; try lia.
    unfold limb_list_bounded.
    all: rewrite Zlength_nil in H; lia.
  }
  assert (Hlistvalue :
    u64_list_value (out :: out_2 :: out_3 :: out_4 :: nil) =
    u256_of_limbs out out_2 out_3 out_4).
  {
    unfold u64_list_value, u256_of_limbs.
    repeat rewrite limb_list_value_cons.
    rewrite limb_list_value_nil. ring.
  }
  Exists (out :: out_2 :: out_3 :: out_4 :: nil).
  unfold StructPredu32, UInt64Array.full, store_array.
  cbn [store_array_rec].
  entailer_with ltac:(
    try rewrite Hvalue; try rewrite Htmpmod; try rewrite Hlistvalue;
    try assumption; try lia).
  cbn [u32_v store_array_rec].
  rewrite sizeof_uint64.
  assert (Htmp_addr :
    eval_addr_expr
      (RE_addr_of (LE_arrow_field (RE_addr_of (LE_var "tmp")) "v")) =
    eval_addr_expr
      (RE_addr_of
        (LE_arrow_field
          (RE_const
            (eval_addr_expr (RE_addr_of (LE_var "tmp")))
            (FET_alias "u32"))
          "v"))).
  { csimpl. reflexivity. }
  rewrite <- Htmp_addr.
  simpl; cancel.
  entailer!.
Qed. 

Lemma proof_of_add_mod_p_entail_wit_8_2_non_alias : add_mod_p_entail_wit_8_2_non_alias.
Proof.
  unfold add_mod_p_entail_wit_8_2_non_alias.
  right; intros.
  repeat first [rewrite Znth0_cons in * | rewrite Znth_cons in * by lia].
  assert (Hadd : A_non_alias + B_non_alias =
    u256_of_limbs out out_2 out_3 out_4 + retval_4 * U256_MOD).
  {
    rewrite PreH59, PreH50.
    apply (u256_add_carry_chain
      x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
      out out_2 out_3 out_4 retval retval_2 retval_3 retval_4); lia.
  }
  assert (Hsub :
    u256_of_limbs out out_2 out_3 out_4 + U256_MOD - SM2_P_Z =
    u256_of_limbs out_5 out_6 out_7 out_8 + retval_8 * U256_MOD).
  {
    apply (add_mod_p_sub_carry_chain
      out out_2 out_3 out_4 out_5 out_6 out_7 out_8
      retval_5 retval_6 retval_7 retval_8); assumption.
  }
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HT.
  pose proof (u256_of_limbs_range out_5 out_6 out_7 out_8
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof (add_mod_p_reduction_arithmetic
    A_non_alias B_non_alias
    (u256_of_limbs out out_2 out_3 out_4)
    (u256_of_limbs out_5 out_6 out_7 out_8)
    retval_4 retval_8
    ltac:(lia) ltac:(lia) HT HD ltac:(lia) ltac:(lia)
    Hadd Hsub PreH9) as [Hvalue Htmpmod].
  assert (Hbounded :
    u64_list_bounded (out :: out_2 :: out_3 :: out_4 :: nil)).
  {
    unfold u64_list_bounded.
    repeat rewrite limb_list_bounded_cons_iff.
    repeat split; try lia.
    unfold limb_list_bounded.
    all: rewrite Zlength_nil in H; lia.
  }
  assert (Hlistvalue :
    u64_list_value (out :: out_2 :: out_3 :: out_4 :: nil) =
    u256_of_limbs out out_2 out_3 out_4).
  {
    unfold u64_list_value, u256_of_limbs.
    repeat rewrite limb_list_value_cons.
    rewrite limb_list_value_nil. ring.
  }
  Exists (out :: out_2 :: out_3 :: out_4 :: nil).
  unfold StructPredu32, UInt64Array.full, store_array.
  cbn [store_array_rec].
  entailer_with ltac:(
    try rewrite Hvalue; try rewrite Htmpmod; try rewrite Hlistvalue;
    try assumption; try lia).
  cbn [u32_v store_array_rec].
  rewrite sizeof_uint64.
  assert (Htmp_addr :
    eval_addr_expr
      (RE_addr_of (LE_arrow_field (RE_addr_of (LE_var "tmp")) "v")) =
    eval_addr_expr
      (RE_addr_of
        (LE_arrow_field
          (RE_const
            (eval_addr_expr (RE_addr_of (LE_var "tmp")))
            (FET_alias "u32"))
          "v"))).
  { csimpl. reflexivity. }
  rewrite <- Htmp_addr.
  simpl; cancel.
  entailer!.
  destruct sm2_p_montgomery_bounds as [[HPpos HPlt] HPhalf].
  apply Z.mod_pos_bound. exact HPpos.
Qed. 

Lemma proof_of_add_mod_p_entail_wit_9_1_a_eq_b : add_mod_p_entail_wit_9_1_a_eq_b.
Proof.
  unfold add_mod_p_entail_wit_9_1_a_eq_b.
  right; intros.
  repeat first [rewrite Znth0_cons in * | rewrite Znth_cons in * by lia].
  assert (Hadd : A_a_eq_b + A_a_eq_b =
    u256_of_limbs out out_2 out_3 out_4 + retval_4 * U256_MOD).
  {
    rewrite PreH50.
    apply (u256_add_carry_chain
      x0 x1 x2 x3 x0 x1 x2 x3
      out out_2 out_3 out_4 retval retval_2 retval_3 retval_4); lia.
  }
  assert (Hsub :
    u256_of_limbs out out_2 out_3 out_4 + U256_MOD - SM2_P_Z =
    u256_of_limbs out_5 out_6 out_7 out_8 + retval_8 * U256_MOD).
  {
    apply (add_mod_p_sub_carry_chain
      out out_2 out_3 out_4 out_5 out_6 out_7 out_8
      retval_5 retval_6 retval_7 retval_8); assumption.
  }
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HT.
  pose proof (u256_of_limbs_range out_5 out_6 out_7 out_8
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof (add_mod_p_no_reduction_arithmetic
    A_a_eq_b A_a_eq_b
    (u256_of_limbs out out_2 out_3 out_4)
    (u256_of_limbs out_5 out_6 out_7 out_8)
    retval_4 retval_8
    ltac:(lia) ltac:(lia) HT HD ltac:(lia) ltac:(lia)
    Hadd Hsub PreH9) as [Hvalue Htmpmod].
  finish_add_mod_p_tmp (A_a_eq_b + A_a_eq_b)
    out out_2 out_3 out_4 Hvalue Htmpmod.
Qed. 

Lemma proof_of_add_mod_p_entail_wit_9_2_a_eq_b : add_mod_p_entail_wit_9_2_a_eq_b.
Proof.
  unfold add_mod_p_entail_wit_9_2_a_eq_b.
  right; intros.
  repeat first [rewrite Znth0_cons in * | rewrite Znth_cons in * by lia].
  assert (Hadd : A_a_eq_b + A_a_eq_b =
    u256_of_limbs out out_2 out_3 out_4 + retval_4 * U256_MOD).
  {
    rewrite PreH50.
    apply (u256_add_carry_chain
      x0 x1 x2 x3 x0 x1 x2 x3
      out out_2 out_3 out_4 retval retval_2 retval_3 retval_4); lia.
  }
  assert (Hsub :
    u256_of_limbs out out_2 out_3 out_4 + U256_MOD - SM2_P_Z =
    u256_of_limbs out_5 out_6 out_7 out_8 + retval_8 * U256_MOD).
  {
    apply (add_mod_p_sub_carry_chain
      out out_2 out_3 out_4 out_5 out_6 out_7 out_8
      retval_5 retval_6 retval_7 retval_8); assumption.
  }
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HT.
  pose proof (u256_of_limbs_range out_5 out_6 out_7 out_8
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof (add_mod_p_reduction_arithmetic
    A_a_eq_b A_a_eq_b
    (u256_of_limbs out out_2 out_3 out_4)
    (u256_of_limbs out_5 out_6 out_7 out_8)
    retval_4 retval_8
    ltac:(lia) ltac:(lia) HT HD ltac:(lia) ltac:(lia)
    Hadd Hsub PreH9) as [Hvalue Htmpmod].
  finish_add_mod_p_tmp (A_a_eq_b + A_a_eq_b)
    out out_2 out_3 out_4 Hvalue Htmpmod.
Qed. 

Lemma proof_of_add_mod_p_entail_wit_10_1_r_eq_a : add_mod_p_entail_wit_10_1_r_eq_a.
Proof.
  unfold add_mod_p_entail_wit_10_1_r_eq_a.
  right; intros.
  repeat first [rewrite Znth0_cons in * | rewrite Znth_cons in * by lia].
  assert (Hadd : A_r_eq_a + B_r_eq_a =
    u256_of_limbs out out_2 out_3 out_4 + retval_4 * U256_MOD).
  {
    rewrite PreH59, PreH50.
    apply (u256_add_carry_chain
      x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
      out out_2 out_3 out_4 retval retval_2 retval_3 retval_4); lia.
  }
  assert (Hsub :
    u256_of_limbs out out_2 out_3 out_4 + U256_MOD - SM2_P_Z =
    u256_of_limbs out_5 out_6 out_7 out_8 + retval_8 * U256_MOD).
  {
    apply (add_mod_p_sub_carry_chain
      out out_2 out_3 out_4 out_5 out_6 out_7 out_8
      retval_5 retval_6 retval_7 retval_8); assumption.
  }
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HT.
  pose proof (u256_of_limbs_range out_5 out_6 out_7 out_8
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof (add_mod_p_no_reduction_arithmetic
    A_r_eq_a B_r_eq_a
    (u256_of_limbs out out_2 out_3 out_4)
    (u256_of_limbs out_5 out_6 out_7 out_8)
    retval_4 retval_8
    ltac:(lia) ltac:(lia) HT HD ltac:(lia) ltac:(lia)
    Hadd Hsub PreH9) as [Hvalue Htmpmod].
  finish_add_mod_p_tmp (A_r_eq_a + B_r_eq_a)
    out out_2 out_3 out_4 Hvalue Htmpmod.
Qed. 

Lemma proof_of_add_mod_p_entail_wit_10_2_r_eq_a : add_mod_p_entail_wit_10_2_r_eq_a.
Proof.
  unfold add_mod_p_entail_wit_10_2_r_eq_a.
  right; intros.
  repeat first [rewrite Znth0_cons in * | rewrite Znth_cons in * by lia].
  assert (Hadd : A_r_eq_a + B_r_eq_a =
    u256_of_limbs out out_2 out_3 out_4 + retval_4 * U256_MOD).
  {
    rewrite PreH59, PreH50.
    apply (u256_add_carry_chain
      x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
      out out_2 out_3 out_4 retval retval_2 retval_3 retval_4); lia.
  }
  assert (Hsub :
    u256_of_limbs out out_2 out_3 out_4 + U256_MOD - SM2_P_Z =
    u256_of_limbs out_5 out_6 out_7 out_8 + retval_8 * U256_MOD).
  {
    apply (add_mod_p_sub_carry_chain
      out out_2 out_3 out_4 out_5 out_6 out_7 out_8
      retval_5 retval_6 retval_7 retval_8); assumption.
  }
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HT.
  pose proof (u256_of_limbs_range out_5 out_6 out_7 out_8
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof (add_mod_p_reduction_arithmetic
    A_r_eq_a B_r_eq_a
    (u256_of_limbs out out_2 out_3 out_4)
    (u256_of_limbs out_5 out_6 out_7 out_8)
    retval_4 retval_8
    ltac:(lia) ltac:(lia) HT HD ltac:(lia) ltac:(lia)
    Hadd Hsub PreH9) as [Hvalue Htmpmod].
  finish_add_mod_p_tmp (A_r_eq_a + B_r_eq_a)
    out out_2 out_3 out_4 Hvalue Htmpmod.
Qed. 

Lemma proof_of_add_mod_p_entail_wit_11_1_r_eq_b : add_mod_p_entail_wit_11_1_r_eq_b.
Proof.
  unfold add_mod_p_entail_wit_11_1_r_eq_b.
  right; intros.
  repeat first [rewrite Znth0_cons in * | rewrite Znth_cons in * by lia].
  assert (Hadd : A_r_eq_b + B_r_eq_b =
    u256_of_limbs out out_2 out_3 out_4 + retval_4 * U256_MOD).
  {
    rewrite PreH59, PreH50.
    apply (u256_add_carry_chain
      x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
      out out_2 out_3 out_4 retval retval_2 retval_3 retval_4); lia.
  }
  assert (Hsub :
    u256_of_limbs out out_2 out_3 out_4 + U256_MOD - SM2_P_Z =
    u256_of_limbs out_5 out_6 out_7 out_8 + retval_8 * U256_MOD).
  {
    apply (add_mod_p_sub_carry_chain
      out out_2 out_3 out_4 out_5 out_6 out_7 out_8
      retval_5 retval_6 retval_7 retval_8); assumption.
  }
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HT.
  pose proof (u256_of_limbs_range out_5 out_6 out_7 out_8
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof (add_mod_p_no_reduction_arithmetic
    A_r_eq_b B_r_eq_b
    (u256_of_limbs out out_2 out_3 out_4)
    (u256_of_limbs out_5 out_6 out_7 out_8)
    retval_4 retval_8
    ltac:(lia) ltac:(lia) HT HD ltac:(lia) ltac:(lia)
    Hadd Hsub PreH9) as [Hvalue Htmpmod].
  finish_add_mod_p_tmp (A_r_eq_b + B_r_eq_b)
    out out_2 out_3 out_4 Hvalue Htmpmod.
Qed. 

Lemma proof_of_add_mod_p_entail_wit_11_2_r_eq_b : add_mod_p_entail_wit_11_2_r_eq_b.
Proof.
  unfold add_mod_p_entail_wit_11_2_r_eq_b.
  right; intros.
  repeat first [rewrite Znth0_cons in * | rewrite Znth_cons in * by lia].
  assert (Hadd : A_r_eq_b + B_r_eq_b =
    u256_of_limbs out out_2 out_3 out_4 + retval_4 * U256_MOD).
  {
    rewrite PreH59, PreH50.
    apply (u256_add_carry_chain
      x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
      out out_2 out_3 out_4 retval retval_2 retval_3 retval_4); lia.
  }
  assert (Hsub :
    u256_of_limbs out out_2 out_3 out_4 + U256_MOD - SM2_P_Z =
    u256_of_limbs out_5 out_6 out_7 out_8 + retval_8 * U256_MOD).
  {
    apply (add_mod_p_sub_carry_chain
      out out_2 out_3 out_4 out_5 out_6 out_7 out_8
      retval_5 retval_6 retval_7 retval_8); assumption.
  }
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HT.
  pose proof (u256_of_limbs_range out_5 out_6 out_7 out_8
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof (add_mod_p_reduction_arithmetic
    A_r_eq_b B_r_eq_b
    (u256_of_limbs out out_2 out_3 out_4)
    (u256_of_limbs out_5 out_6 out_7 out_8)
    retval_4 retval_8
    ltac:(lia) ltac:(lia) HT HD ltac:(lia) ltac:(lia)
    Hadd Hsub PreH9) as [Hvalue Htmpmod].
  finish_add_mod_p_tmp (A_r_eq_b + B_r_eq_b)
    out out_2 out_3 out_4 Hvalue Htmpmod.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_1 : add_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_2 : add_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_22_non_alias_pure : add_mod_p_partial_solve_wit_22_non_alias_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_22_non_alias_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_0.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_0) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_24_a_eq_b_pure_split_goal_1 : add_mod_p_partial_solve_wit_24_a_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_24_a_eq_b_pure_split_goal_2 : add_mod_p_partial_solve_wit_24_a_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_24_a_eq_b_pure : add_mod_p_partial_solve_wit_24_a_eq_b_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_24_a_eq_b_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_0.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_0) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_26_r_eq_a_pure_split_goal_1 : add_mod_p_partial_solve_wit_26_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_26_r_eq_a_pure_split_goal_2 : add_mod_p_partial_solve_wit_26_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_26_r_eq_a_pure : add_mod_p_partial_solve_wit_26_r_eq_a_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_26_r_eq_a_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_0.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_0) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_28_r_eq_b_pure_split_goal_1 : add_mod_p_partial_solve_wit_28_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_28_r_eq_b_pure_split_goal_2 : add_mod_p_partial_solve_wit_28_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_28_r_eq_b_pure : add_mod_p_partial_solve_wit_28_r_eq_b_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_28_r_eq_b_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_0.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_0) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_30_non_alias_pure_split_goal_1 : add_mod_p_partial_solve_wit_30_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_30_non_alias_pure_split_goal_2 : add_mod_p_partial_solve_wit_30_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_30_non_alias_pure : add_mod_p_partial_solve_wit_30_non_alias_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_30_non_alias_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_1.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_1) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_32_a_eq_b_pure_split_goal_1 : add_mod_p_partial_solve_wit_32_a_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_32_a_eq_b_pure_split_goal_2 : add_mod_p_partial_solve_wit_32_a_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_32_a_eq_b_pure : add_mod_p_partial_solve_wit_32_a_eq_b_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_32_a_eq_b_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_1.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_1) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_34_r_eq_a_pure_split_goal_1 : add_mod_p_partial_solve_wit_34_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_34_r_eq_a_pure_split_goal_2 : add_mod_p_partial_solve_wit_34_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_34_r_eq_a_pure : add_mod_p_partial_solve_wit_34_r_eq_a_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_34_r_eq_a_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_1.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_1) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_36_r_eq_b_pure_split_goal_1 : add_mod_p_partial_solve_wit_36_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_36_r_eq_b_pure_split_goal_2 : add_mod_p_partial_solve_wit_36_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_36_r_eq_b_pure : add_mod_p_partial_solve_wit_36_r_eq_b_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_36_r_eq_b_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_1.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_1) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_38_non_alias_pure_split_goal_1 : add_mod_p_partial_solve_wit_38_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_38_non_alias_pure_split_goal_2 : add_mod_p_partial_solve_wit_38_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_38_non_alias_pure : add_mod_p_partial_solve_wit_38_non_alias_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_38_non_alias_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_2.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_2) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_40_a_eq_b_pure_split_goal_1 : add_mod_p_partial_solve_wit_40_a_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_40_a_eq_b_pure_split_goal_2 : add_mod_p_partial_solve_wit_40_a_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_40_a_eq_b_pure : add_mod_p_partial_solve_wit_40_a_eq_b_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_40_a_eq_b_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_2.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_2) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_42_r_eq_a_pure_split_goal_1 : add_mod_p_partial_solve_wit_42_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_42_r_eq_a_pure_split_goal_2 : add_mod_p_partial_solve_wit_42_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_42_r_eq_a_pure : add_mod_p_partial_solve_wit_42_r_eq_a_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_42_r_eq_a_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_2.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_2) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_44_r_eq_b_pure_split_goal_1 : add_mod_p_partial_solve_wit_44_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_44_r_eq_b_pure_split_goal_2 : add_mod_p_partial_solve_wit_44_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_44_r_eq_b_pure : add_mod_p_partial_solve_wit_44_r_eq_b_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_44_r_eq_b_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_2.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_2) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_46_non_alias_pure_split_goal_1 : add_mod_p_partial_solve_wit_46_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_46_non_alias_pure_split_goal_2 : add_mod_p_partial_solve_wit_46_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_46_non_alias_pure : add_mod_p_partial_solve_wit_46_non_alias_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_46_non_alias_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_3.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_3) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_48_a_eq_b_pure_split_goal_1 : add_mod_p_partial_solve_wit_48_a_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_48_a_eq_b_pure_split_goal_2 : add_mod_p_partial_solve_wit_48_a_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_48_a_eq_b_pure : add_mod_p_partial_solve_wit_48_a_eq_b_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_48_a_eq_b_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_3.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_3) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_50_r_eq_a_pure_split_goal_1 : add_mod_p_partial_solve_wit_50_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_50_r_eq_a_pure_split_goal_2 : add_mod_p_partial_solve_wit_50_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_50_r_eq_a_pure : add_mod_p_partial_solve_wit_50_r_eq_a_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_50_r_eq_a_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_3.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_3) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_partial_solve_wit_52_r_eq_b_pure_split_goal_1 : add_mod_p_partial_solve_wit_52_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_52_r_eq_b_pure_split_goal_2 : add_mod_p_partial_solve_wit_52_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_p_partial_solve_wit_52_r_eq_b_pure : add_mod_p_partial_solve_wit_52_r_eq_b_pure.
Proof.
  unfold add_mod_p_partial_solve_wit_52_r_eq_b_pure.
  solve_add_mod_p_lnot_range SM2_P_LIMB_3.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    pose proof (unsigned_Lastnbits_range
      (Z.lnot SM2_P_LIMB_3) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia.
Qed. 

Lemma proof_of_add_mod_p_derive_mont_non_alias_by_non_alias : add_mod_p_derive_mont_non_alias_by_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename B_mont_non_alias into B.
  rename A_mont_non_alias into A.
  Exists (mont_p A) (mont_p B).
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    rewrite ec_math_refinement.mont_p_add.
    entailer!.
Qed. 
