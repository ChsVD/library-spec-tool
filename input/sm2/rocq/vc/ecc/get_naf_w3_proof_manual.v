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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import get_naf_w3_def.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import get_naf_w3_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import get_naf_w3_proof_auto.
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

Lemma proof_of_get_naf_w3_safety_wit_9_non_alias_split_goal_1 : get_naf_w3_safety_wit_9_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_get_naf_w3_safety_wit_9_non_alias_split_goal_2 : get_naf_w3_safety_wit_9_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_get_naf_w3_safety_wit_9_non_alias : get_naf_w3_safety_wit_9_non_alias.
Proof.
  aggressive_pre_process.
  - LLM_pre_process ltac:(lia || nia || int_auto).
    dump_pre_spatial.
    change (Z.land (signed_last_nbits x0 8) (Z.ones 3) - 8 <= 127).
    rewrite Z.land_ones; [|lia].
    pose proof
      (Z.mod_pos_bound (signed_last_nbits x0 8) (2 ^ 3) ltac:(lia)).
    lia.
  - LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_get_naf_w3_safety_wit_17_non_alias_split_goal_1 : get_naf_w3_safety_wit_17_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_get_naf_w3_safety_wit_17_non_alias : get_naf_w3_safety_wit_17_non_alias.
Proof.
  aggressive_pre_process.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof
    (signed_Lastnbits_range
      (Z.land (signed_last_nbits x0 8) 7 - 8) 8 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_get_naf_w3_safety_wit_18_non_alias_split_goal_1 : get_naf_w3_safety_wit_18_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_get_naf_w3_safety_wit_18_non_alias : get_naf_w3_safety_wit_18_non_alias.
Proof.
  aggressive_pre_process.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  change (Z.land (signed_last_nbits x0 8) (Z.ones 3) < 0) in PreH1.
  rewrite Z.land_ones in PreH1; [|lia].
  pose proof
    (Z.mod_pos_bound (signed_last_nbits x0 8) (2 ^ 3) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_get_naf_w3_entail_wit_1_non_alias_split_goal_1 : get_naf_w3_entail_wit_1_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_1_non_alias_split_goal_2 : get_naf_w3_entail_wit_1_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_1_non_alias_split_goal_3 : get_naf_w3_entail_wit_1_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_1_non_alias_split_goal_4 : get_naf_w3_entail_wit_1_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_1_non_alias_split_goal_5 : get_naf_w3_entail_wit_1_non_alias_split_goal_5.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_1_non_alias_split_goal_6 : get_naf_w3_entail_wit_1_non_alias_split_goal_6.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_1_non_alias_split_goal_7 : get_naf_w3_entail_wit_1_non_alias_split_goal_7.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_1_non_alias_split_goal_8 : get_naf_w3_entail_wit_1_non_alias_split_goal_8.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_1_non_alias : get_naf_w3_entail_wit_1_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists 0 K_non_alias (@nil Z).
  sep_apply_l_atomic
    (CharArray.undef_full_to_undef_seg naf_w3_pre 257).
  rewrite (CharArray.full_empty naf_w3_pre 0).
  split_pure_spatial.
  - sep_apply
      (uint64_full4_to_store_u256_limbs
        &( &( "x") ->ₛ "v")
        (u32_v {| u32_v := repeat_Z 0 4 |})).
    cbv [repeat_Z u64_list_value limb_list_value u256_of_limbs] in *.
    unfold store_u256.
    cancel.
    rewrite (global_u32_v_addr_eq "x"), u32_v_field_address_eq.
    change (store_u256_limbs &( "x") 0 |--
            store_u256_limbs &( "x") 0).
    reflexivity.
  - unfold store_u256, store_u256_limbs at 1.
    Intros x0 x1 x2 x3.
    entailer!.
    + unfold wnaf3_separated.
      intros index Hindex.
      rewrite Zlength_nil in Hindex.
      lia.
    + assert (Hw : wnaf3_value nil = 0).
      {
        unfold wnaf3_value, Sum.sum.
        simpl.
        lia.
      }
      rewrite Hw.
      lia.
    + pose proof
        (u256_of_limbs_range x0 x1 x2 x3
          ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto)).
      cbv [U256_MOD] in *.
      lia.
    + pose proof
        (u256_of_limbs_range x0 x1 x2 x3
          ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto)).
      lia.
Qed.

Lemma proof_of_get_naf_w3_entail_wit_5_1_non_alias_split_goal_1 : get_naf_w3_entail_wit_5_1_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_1_non_alias_split_goal_2 : get_naf_w3_entail_wit_5_1_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_1_non_alias_split_goal_3 : get_naf_w3_entail_wit_5_1_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_1_non_alias_split_goal_4 : get_naf_w3_entail_wit_5_1_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_1_non_alias_split_goal_5 : get_naf_w3_entail_wit_5_1_non_alias_split_goal_5.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_1_non_alias_split_goal_6 : get_naf_w3_entail_wit_5_1_non_alias_split_goal_6.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_1_non_alias_split_goal_7 : get_naf_w3_entail_wit_5_1_non_alias_split_goal_7.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_1_non_alias_split_goal_8 : get_naf_w3_entail_wit_5_1_non_alias_split_goal_8.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_1_non_alias_split_goal_9 : get_naf_w3_entail_wit_5_1_non_alias_split_goal_9.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_1_non_alias_split_goal_10 : get_naf_w3_entail_wit_5_1_non_alias_split_goal_10.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_1_non_alias : get_naf_w3_entail_wit_5_1_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (m := Z.land (signed_last_nbits x0_2 8) 7) in *.
  assert (Hm : 0 <= m < 8).
  {
    subst m.
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia.
    apply Z.mod_pos_bound.
    lia.
  }
  assert (Hs : signed_last_nbits (m - 8) 8 = m - 8).
  {
    apply signed_last_nbits_eq; lia.
  }
  rewrite Hs in PreH6.
  lia.
Qed.

Lemma proof_of_get_naf_w3_entail_wit_5_2_non_alias_split_goal_1 : get_naf_w3_entail_wit_5_2_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_2_non_alias_split_goal_2 : get_naf_w3_entail_wit_5_2_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_2_non_alias_split_goal_3 : get_naf_w3_entail_wit_5_2_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_2_non_alias_split_goal_4 : get_naf_w3_entail_wit_5_2_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_2_non_alias_split_goal_5 : get_naf_w3_entail_wit_5_2_non_alias_split_goal_5.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_2_non_alias_split_goal_6 : get_naf_w3_entail_wit_5_2_non_alias_split_goal_6.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_2_non_alias_split_goal_7 : get_naf_w3_entail_wit_5_2_non_alias_split_goal_7.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_2_non_alias_split_goal_8 : get_naf_w3_entail_wit_5_2_non_alias_split_goal_8.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_2_non_alias_split_goal_9 : get_naf_w3_entail_wit_5_2_non_alias_split_goal_9.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_2_non_alias_split_goal_10 : get_naf_w3_entail_wit_5_2_non_alias_split_goal_10.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_2_non_alias : get_naf_w3_entail_wit_5_2_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (m := Z.land (signed_last_nbits x0_2 8) 7) in *.
  assert (Hm_mod2 : m mod 2 = 1).
  {
    replace 1 with (Z.ones 1) in PreH8 by reflexivity.
    rewrite Z.land_ones in PreH8 by lia.
    change (m mod 2 <> 0) in PreH8.
    pose proof (Z.mod_pos_bound m 2 ltac:(lia)).
    lia.
  }
  assert (Hm_cases : m = 1 \/ m = 3).
  {
    pose proof (Z.mod_pos_bound m 2 ltac:(lia)).
    assert (Hcases : m = 0 \/ m = 1 \/ m = 2 \/ m = 3) by lia.
    destruct Hcases as [-> | [-> | [-> | ->]]];
      cbn in Hm_mod2; tauto.
  }
  assert (Hlow_mod8 : x0_2 mod 8 = m).
  {
    subst m.
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia.
    unfold signed_last_nbits.
    destruct (Coqlib.zlt (x0_2 mod 2 ^ 8) (2 ^ (8 - 1))).
    - change (2 ^ 3) with 8.
      change (2 ^ 8) with 256.
      replace 256 with (32 * 8) by ring.
      rewrite Zaux.Zmod_mod_mult by lia.
      reflexivity.
    - change (2 ^ 3) with 8.
      change (2 ^ 8) with 256.
      rewrite Zminus_mod.
      change (256 mod 8) with 0.
      rewrite Z.sub_0_r.
      replace 256 with (32 * 8) by ring.
      rewrite Zaux.Zmod_mod_mult by lia.
      rewrite Z.mod_mod by lia.
      reflexivity.
  }
  assert (HK_mod8 : Kcur_2 mod 8 = m).
  {
    rewrite PreH9.
    unfold u256_of_limbs.
    change U64_MOD with (8 * 2305843009213693952).
    replace
      (x0_2 + x1_2 * (8 * 2305843009213693952) +
       x2_2 * (8 * 2305843009213693952) ^ 2 +
       x3_2 * (8 * 2305843009213693952) ^ 3)
      with
      (x0_2 + 8 *
        (x1_2 * 2305843009213693952 +
         x2_2 * 8 * 2305843009213693952 ^ 2 +
         x3_2 * 8 ^ 2 * 2305843009213693952 ^ 3)) by ring.
    rewrite Z.add_mod, Z.mul_mod, Hlow_mod8.
    cbn.
    rewrite Z.mod_small by (destruct Hm_cases; lia).
    all: lia.
  }
  assert (Hx_high : x1 = 0 /\ x2 = 0 /\ x3 = 0).
  {
    cbv [u256_of_limbs U64_MOD] in PreH18, PreH40.
    nia.
  }
  destruct Hx_high as [Hx1 [Hx2 Hx3]].
  assert (HXnew : u256_of_limbs m x1 x2 x3 = m).
  {
    subst x1 x2 x3.
    unfold u256_of_limbs.
    ring.
  }
  assert (HK_ge_m : m <= Kcur_2).
  {
    rewrite <- HK_mod8.
    apply Z.mod_le; lia.
  }
  assert (Hborrow : borrow = 0).
  {
    rewrite <- PreH9, HXnew in PreH5.
    assert (borrow = 0 \/ borrow = 1) by lia.
    destruct H as [-> | ->]; [reflexivity | nia].
  }
  assert (HS : S = Kcur_2 - m) by lia.
  assert (HS_mod8 : S mod 8 = 0).
  {
    rewrite HS, Zminus_mod, HK_mod8.
    replace (m mod 8) with m by
      (symmetry; apply Z.mod_small; lia).
    replace (m - m) with 0 by ring.
    reflexivity.
  }
  assert (HS_even : S mod 2 = 0).
  {
    apply Z.mod_divide; [lia|].
    apply Z.mod_divide in HS_mod8; [|lia].
    destruct HS_mod8 as [q Hq].
    exists (4 * q).
    nia.
  }
  assert (HK_shift : Kcur_2 = m + 2 * (S ÷ 2)).
  {
    pose proof (Z.quot_rem S 2 ltac:(lia)) as Hqr.
    rewrite Z.rem_mod_nonneg in Hqr by lia.
    rewrite HS_even in Hqr.
    lia.
  }
  assert (Hshift_nonneg : 0 <= S ÷ 2).
  {
    pose proof (Z.quot_rem S 2 ltac:(lia)) as Hqr.
    rewrite Z.rem_mod_nonneg in Hqr by lia.
    pose proof (Z.mod_pos_bound S 2 ltac:(lia)).
    lia.
  }
  assert (Hshift_mod4 : (S ÷ 2) mod 4 = 0).
  {
    apply Z.mod_divide; [lia|].
    apply Z.mod_divide in HS_mod8; [|lia].
    destruct HS_mod8 as [q Hq].
    exists q.
    pose proof (Z.quot_rem S 2 ltac:(lia)) as Hqr.
    rewrite Z.rem_mod_nonneg in Hqr by lia.
    rewrite HS_even in Hqr.
    nia.
  }
  assert (Hprev_zero :
    i >= 1 -> Znth (i - 1) digits_2 0 = 0).
  {
    intros Hi.
    destruct (Z.eq_dec (Znth (i - 1) digits_2 0) 0)
      as [Hz | Hnz]; [exact Hz|].
    pose proof (PreH37 ltac:(tauto)) as Hfour.
    rewrite Z.rem_mod_nonneg in Hfour by lia.
    apply Z.mod_divide in Hfour; [|lia].
    apply Z.mod_divide in Hshift_mod4; [|lia].
    destruct Hfour as [q Hq].
    destruct Hshift_mod4 as [r Hr].
    destruct Hm_cases; lia.
  }
  assert (Hprev2_zero :
    i >= 2 -> Znth (i - 2) digits_2 0 = 0).
  {
    intros Hi.
    destruct (Z.eq_dec (Znth (i - 2) digits_2 0) 0)
      as [Hz | Hnz]; [exact Hz|].
    pose proof (PreH38 ltac:(tauto)) as Heven.
    rewrite Z.rem_mod_nonneg in Heven by lia.
    apply Z.mod_divide in Heven; [|lia].
    destruct Heven as [q Hq].
    destruct Hm_cases; lia.
  }
  Exists m (S ÷ 2) (digits_2 +:: m).
  split_pure_spatial.
  - rewrite HXnew.
    entailer!.
    apply store_char_undef_store_char.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    + intros Hi.
      pose proof (PreH32 ltac:(lia)) as Hbound.
      assert (Hpow :
        2 ^ (256 - i) = 2 * 2 ^ (256 - (i + 1))).
      {
        replace (256 - i) with ((256 - (i + 1)) + 1) by lia.
        rewrite Z.pow_add_r by lia.
        change (2 ^ 1) with 2.
        ring.
      }
      rewrite Hpow in Hbound.
      rewrite HK_shift in Hbound.
      nia.
    + intros Hlast.
      assert (Hi : i = 256) by lia.
      pose proof (PreH32 ltac:(lia)) as Hbound.
      replace (256 - i) with 0 in Hbound by lia.
      change (2 ^ 0) with 1 in Hbound.
      destruct Hm_cases; lia.
    + assert (Hvalue :
        wnaf3_value (digits_2 +:: m) =
        wnaf3_value digits_2 + m * 2 ^ Zlength digits_2).
      {
        unfold wnaf3_value.
        rewrite
          (ZRange.sum_Z_range_Znth_app_single_indexed
            0 m digits_2 (fun index digit => digit * 2 ^ index)).
        ring.
      }
      rewrite Hvalue, <- PreH30, PreH34.
      rewrite Z.pow_add_r by lia.
      change (2 ^ 1) with 2.
      rewrite HK_shift.
      ring.
    + intros j Hj.
      destruct (Z_lt_ge_dec j i) as [Hji | Hji].
      * rewrite app_Znth1 by (rewrite <- PreH30; lia).
        apply PreH35.
        lia.
      * assert (Hjeq : j = i) by lia.
        subst j.
        rewrite app_Znth2 by (rewrite <- PreH30; lia).
        replace (i - Zlength digits_2) with 0 by lia.
        cbn.
        unfold wnaf3_digit.
        destruct Hm_cases; lia.
    + unfold wnaf3_separated in *.
      intros index Hindex Hnonzero.
      rewrite Zlength_app, Zlength_cons, Zlength_nil in Hindex.
      destruct (Z_lt_ge_dec index i) as [Hlt | Hge].
      * assert (Hindex_old : 0 <= index < Zlength digits_2) by lia.
        rewrite app_Znth1 in Hnonzero by lia.
        specialize (PreH36 index Hindex_old Hnonzero).
        destruct PreH36 as [Hnext Hnext2].
        split; intros Hinside.
        -- destruct (Z_lt_ge_dec (index + 1) i) as [Hin | Hin].
           ++ rewrite app_Znth1.
              apply Hnext; lia.
              rewrite <- PreH30; lia.
           ++ assert (Heq : index + 1 = i) by lia.
              rewrite app_Znth2.
              2: rewrite <- PreH30; lia.
              replace (index + 1 - Zlength digits_2) with 0 by lia.
              cbn.
              exfalso.
              apply Hnonzero.
              replace index with (i - 1) by lia.
              apply Hprev_zero.
              lia.
        -- destruct (Z_lt_ge_dec (index + 2) i) as [Hin | Hin].
           ++ rewrite app_Znth1.
              2: rewrite <- PreH30; lia.
              apply Hnext2.
              rewrite <- PreH30.
              exact Hin.
           ++ rewrite Zlength_app, Zlength_cons, Zlength_nil in Hinside.
              assert (Heq2 : index + 2 = i) by lia.
              rewrite app_Znth2.
              2: rewrite <- PreH30; lia.
              replace (index + 2 - Zlength digits_2) with 0 by
                (rewrite <- PreH30; lia).
              cbn.
              exfalso.
              apply Hnonzero.
              replace index with (i - 2) by lia.
              apply Hprev2_zero.
              clear - Hindex_old Heq2.
              lia.
      * assert (Heq : index = i) by lia.
        subst index.
        split; intros Hinside;
          rewrite Zlength_app, Zlength_cons, Zlength_nil in Hinside;
          lia.
    + intros _.
      rewrite Z.rem_mod_nonneg by lia.
      exact Hshift_mod4.
    + intros [Hi2 Hnz].
      replace (i + 1 - 2) with (i - 1) in Hnz by lia.
      rewrite app_Znth1 in Hnz.
      2: rewrite <- PreH30; lia.
      exfalso.
      apply Hnz.
      apply Hprev_zero.
      lia.
    + unfold U64_MOD.
      lia.
Qed.

Lemma proof_of_get_naf_w3_entail_wit_5_3_non_alias_split_goal_1 : get_naf_w3_entail_wit_5_3_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_3_non_alias_split_goal_2 : get_naf_w3_entail_wit_5_3_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_3_non_alias_split_goal_3 : get_naf_w3_entail_wit_5_3_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_3_non_alias_split_goal_4 : get_naf_w3_entail_wit_5_3_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_3_non_alias_split_goal_5 : get_naf_w3_entail_wit_5_3_non_alias_split_goal_5.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_3_non_alias_split_goal_6 : get_naf_w3_entail_wit_5_3_non_alias_split_goal_6.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_3_non_alias_split_goal_7 : get_naf_w3_entail_wit_5_3_non_alias_split_goal_7.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_3_non_alias_split_goal_8 : get_naf_w3_entail_wit_5_3_non_alias_split_goal_8.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_3_non_alias_split_goal_9 : get_naf_w3_entail_wit_5_3_non_alias_split_goal_9.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_3_non_alias_split_goal_10 : get_naf_w3_entail_wit_5_3_non_alias_split_goal_10.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_3_non_alias : get_naf_w3_entail_wit_5_3_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hstore_range :
    store_fn pk_pre K_non_alias |-- “ 0 <= K_non_alias < SM2_N_Z ”).
  {
    unfold store_fn, store_mod.
    apply derivable1_andp_elim1.
  }
  prop_apply_p Hstore_range.
  Intros_p HKinput.
  set (m := Z.land (signed_last_nbits x0_2 8) 7) in *.
  set (d := signed_last_nbits (m - 8) 8) in *.
  set (a := unsigned_last_nbits (- d) 64) in *.
  assert (Hm_mod2 : m mod 2 = 1).
  {
    replace 1 with (Z.ones 1) in PreH8 by reflexivity.
    rewrite Z.land_ones in PreH8 by lia.
    change (m mod 2 <> 0) in PreH8.
    pose proof (Z.mod_pos_bound m 2 ltac:(lia)).
    lia.
  }
  assert (Hm_range : 0 <= m < 8).
  {
    subst m.
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia.
    apply Z.mod_pos_bound.
    lia.
  }
  assert (Hm_cases : m = 5 \/ m = 7).
  {
    pose proof (Z.mod_pos_bound m 2 ltac:(lia)).
    assert (Hcases : m = 4 \/ m = 5 \/ m = 6 \/ m = 7) by lia.
    destruct Hcases as [-> | [-> | [-> | ->]]];
      cbn in Hm_mod2; tauto.
  }
  assert (Hd : d = m - 8).
  {
    subst d.
    apply signed_last_nbits_eq; destruct Hm_cases; lia.
  }
  assert (Ha : a = 8 - m).
  {
    subst a.
    rewrite Hd.
    replace (8 - m) with (- (m - 8)) by ring.
    apply unsigned_last_nbits_eq; destruct Hm_cases; lia.
  }
  assert (Hlow_mod8 : x0_2 mod 8 = m).
  {
    subst m.
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia.
    unfold signed_last_nbits.
    destruct (Coqlib.zlt (x0_2 mod 2 ^ 8) (2 ^ (8 - 1))).
    - change (2 ^ 3) with 8.
      change (2 ^ 8) with 256.
      replace 256 with (32 * 8) by ring.
      rewrite Zaux.Zmod_mod_mult by lia.
      reflexivity.
    - change (2 ^ 3) with 8.
      change (2 ^ 8) with 256.
      rewrite Zminus_mod.
      change (256 mod 8) with 0.
      rewrite Z.sub_0_r.
      replace 256 with (32 * 8) by ring.
      rewrite Zaux.Zmod_mod_mult by lia.
      rewrite Z.mod_mod by lia.
      reflexivity.
  }
  assert (HK_mod8 : Kcur_2 mod 8 = m).
  {
    rewrite PreH9.
    unfold u256_of_limbs.
    change U64_MOD with (8 * 2305843009213693952).
    replace
      (x0_2 + x1_2 * (8 * 2305843009213693952) +
       x2_2 * (8 * 2305843009213693952) ^ 2 +
       x3_2 * (8 * 2305843009213693952) ^ 3)
      with
      (x0_2 + 8 *
        (x1_2 * 2305843009213693952 +
         x2_2 * 8 * 2305843009213693952 ^ 2 +
         x3_2 * 8 ^ 2 * 2305843009213693952 ^ 3)) by ring.
    rewrite Z.add_mod, Z.mul_mod, Hlow_mod8.
    cbn.
    rewrite Z.mod_small by (destruct Hm_cases; lia).
    all: lia.
  }
  assert (Hx_high : x1 = 0 /\ x2 = 0 /\ x3 = 0).
  {
    cbv [u256_of_limbs U64_MOD] in PreH18, PreH40.
    change (2 ^ 64) with 18446744073709551616 in PreH18, PreH40.
    assert (Hx1 : x1 = 0).
    {
      clear - PreH18 PreH40 PreH20 PreH22 PreH24 PreH26.
      nia.
    }
    subst x1.
    assert (Hx2 : x2 = 0).
    {
      clear - PreH18 PreH40 PreH20 PreH22 PreH26.
      nia.
    }
    subst x2.
    assert (Hx3 : x3 = 0).
    {
      clear - PreH18 PreH40 PreH20 PreH26.
      nia.
    }
    tauto.
  }
  destruct Hx_high as [Hx1 [Hx2 Hx3]].
  assert (HXnew : u256_of_limbs a x1 x2 x3 = a).
  {
    subst x1 x2 x3.
    unfold u256_of_limbs.
    ring.
  }
  assert (Hsum_lt : Kcur_2 + a < U256_MOD).
  {
    destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
    - assert (Hdigits : digits_2 = nil).
      {
        destruct digits_2 as [|x xs]; [reflexivity|].
        rewrite Zlength_cons in PreH30.
        pose proof (Zlength_nonneg xs).
        lia.
      }
      subst digits_2.
      unfold wnaf3_value in PreH34.
      rewrite Zlength_nil in PreH34.
      rewrite ZRange.sum_Z_range_empty in PreH34 by lia.
      rewrite Hi0 in PreH34.
      cbn in PreH34.
      assert (HKinput_strong : K_non_alias + 3 < U256_MOD).
      {
        destruct HKinput as [HKinput0 HKinput1].
        assert (SM2_N_Z + 3 < U256_MOD).
        {
          cbv [SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
            u256_of_limbs U32_MOD U64_MOD U256_MOD].
          lia.
        }
        lia.
      }
      destruct Hm_cases; rewrite Ha; lia.
    - pose proof (PreH32 ltac:(lia)) as Hbound.
      assert (2 ^ (256 - i) <= 2 ^ 255).
      {
        apply Z.pow_le_mono_r; lia.
      }
      assert (2 ^ 255 + 3 < U256_MOD) by
        (unfold U256_MOD; nia).
      destruct Hm_cases; rewrite Ha; lia.
  }
  assert (HK_ge_m : m <= Kcur_2).
  {
    rewrite <- HK_mod8.
    apply Z.mod_le; lia.
  }
  assert (Hretval : retval = 0).
  {
    rewrite <- PreH9, HXnew in PreH5.
    assert (retval = 0 \/ retval = 1) by lia.
    destruct H as [-> | ->]; [reflexivity | nia].
  }
  assert (HS : S = Kcur_2 + a) by lia.
  assert (HS_mod8 : S mod 8 = 0).
  {
    apply Z.mod_divide; [lia|].
    pose proof (Z.div_mod Kcur_2 8 ltac:(lia)) as Hdm.
    rewrite HK_mod8 in Hdm.
    exists (Kcur_2 / 8 + 1).
    rewrite HS, Ha.
    lia.
  }
  assert (HS_even : S mod 2 = 0).
  {
    apply Z.mod_divide; [lia|].
    apply Z.mod_divide in HS_mod8; [|lia].
    destruct HS_mod8 as [q Hq].
    exists (4 * q).
    nia.
  }
  assert (HK_shift : Kcur_2 = d + 2 * (S ÷ 2)).
  {
    pose proof (Z.quot_rem S 2 ltac:(lia)) as Hqr.
    rewrite Z.rem_mod_nonneg in Hqr by lia.
    rewrite HS_even in Hqr.
    rewrite Hd, Ha in *.
    lia.
  }
  assert (Hshift_nonneg : 0 <= S ÷ 2).
  {
    pose proof (Z.quot_rem S 2 ltac:(lia)) as Hqr.
    rewrite Z.rem_mod_nonneg in Hqr by lia.
    pose proof (Z.mod_pos_bound S 2 ltac:(lia)).
    lia.
  }
  assert (Hshift_mod4 : (S ÷ 2) mod 4 = 0).
  {
    apply Z.mod_divide; [lia|].
    apply Z.mod_divide in HS_mod8; [|lia].
    destruct HS_mod8 as [q Hq].
    exists q.
    pose proof (Z.quot_rem S 2 ltac:(lia)) as Hqr.
    rewrite Z.rem_mod_nonneg in Hqr by lia.
    rewrite HS_even in Hqr.
    nia.
  }
  assert (Hprev_zero :
    i >= 1 -> Znth (i - 1) digits_2 0 = 0).
  {
    intros Hi.
    destruct (Z.eq_dec (Znth (i - 1) digits_2 0) 0)
      as [Hz | Hnz]; [exact Hz|].
    pose proof (PreH37 ltac:(tauto)) as Hfour.
    rewrite Z.rem_mod_nonneg in Hfour by lia.
    apply Z.mod_divide in Hfour; [|lia].
    apply Z.mod_divide in Hshift_mod4; [|lia].
    destruct Hfour as [q Hq].
    destruct Hshift_mod4 as [r Hr].
    rewrite Hd in HK_shift.
    destruct Hm_cases; lia.
  }
  assert (Hprev2_zero :
    i >= 2 -> Znth (i - 2) digits_2 0 = 0).
  {
    intros Hi.
    destruct (Z.eq_dec (Znth (i - 2) digits_2 0) 0)
      as [Hz | Hnz]; [exact Hz|].
    pose proof (PreH38 ltac:(tauto)) as Heven.
    rewrite Z.rem_mod_nonneg in Heven by lia.
    apply Z.mod_divide in Heven; [|lia].
    destruct Heven as [q Hq].
    rewrite Hd in HK_shift.
    destruct Hm_cases; lia.
  }
  Exists a (S ÷ 2) (digits_2 +:: d).
  split_pure_spatial.
  - rewrite HXnew.
    entailer!.
    apply store_char_undef_store_char.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    + intros Hi.
      pose proof (PreH32 ltac:(lia)) as Hbound.
      assert (Hpow :
        2 ^ (256 - i) = 2 * 2 ^ (256 - (i + 1))).
      {
        replace (256 - i) with ((256 - (i + 1)) + 1) by lia.
        rewrite Z.pow_add_r by lia.
        change (2 ^ 1) with 2.
        ring.
      }
      destruct (Z_lt_ge_dec (256 - (i + 1)) 2)
        as [Hsmall | Hlarge].
      * assert (256 - (i + 1) = 0 \/ 256 - (i + 1) = 1) by lia.
        destruct H as [He | He].
        -- replace i with 255 in Hbound by lia.
           cbn in Hbound.
           rewrite HS, Ha.
           destruct Hm_cases; lia.
        -- replace i with 254 in Hbound by lia.
           cbn in Hbound.
           rewrite HS, Ha.
           destruct Hm_cases; lia.
      * assert (HBmod : 2 ^ (256 - (i + 1)) mod 4 = 0).
        {
          assert (HBfactor :
            2 ^ (256 - (i + 1)) =
            4 * 2 ^ (256 - (i + 1) - 2)).
          {
            replace (256 - (i + 1)) with
              ((256 - (i + 1) - 2) + 2) at 1 by lia.
            rewrite Z.pow_add_r by lia.
            change (2 ^ 2) with 4.
            ring.
          }
          apply Z.mod_divide; [lia|].
          exists (2 ^ (256 - (i + 1) - 2)).
          rewrite Z.mul_comm.
          exact HBfactor.
        }
        apply Z.mod_divide in HS_mod8; [|lia].
        apply Z.mod_divide in HBmod; [|lia].
        destruct HS_mod8 as [q Hq].
        destruct HBmod as [r Hr].
        rewrite Hpow in Hbound.
        destruct Hm_cases; rewrite Ha in *; nia.
    + intros Hlast.
      assert (Hi : i = 256) by lia.
      pose proof (PreH32 ltac:(lia)) as Hbound.
      replace (256 - i) with 0 in Hbound by lia.
      change (2 ^ 0) with 1 in Hbound.
      rewrite HS, Ha.
      destruct Hm_cases; lia.
    + assert (Hvalue :
        wnaf3_value (digits_2 +:: d) =
        wnaf3_value digits_2 + d * 2 ^ Zlength digits_2).
      {
        unfold wnaf3_value.
        rewrite
          (ZRange.sum_Z_range_Znth_app_single_indexed
            0 d digits_2 (fun index digit => digit * 2 ^ index)).
        ring.
      }
      rewrite Hvalue, <- PreH30, PreH34.
      rewrite Z.pow_add_r by lia.
      change (2 ^ 1) with 2.
      rewrite HK_shift.
      ring.
    + intros j Hj.
      destruct (Z_lt_ge_dec j i) as [Hji | Hji].
      * rewrite app_Znth1 by (rewrite <- PreH30; lia).
        apply PreH35.
        lia.
      * assert (Hjeq : j = i) by lia.
        subst j.
        rewrite app_Znth2 by (rewrite <- PreH30; lia).
        replace (i - Zlength digits_2) with 0 by lia.
        cbn.
        unfold wnaf3_digit.
        rewrite Hd.
        destruct Hm_cases; lia.
    + unfold wnaf3_separated in *.
      intros index Hindex Hnonzero.
      rewrite Zlength_app, Zlength_cons, Zlength_nil in Hindex.
      destruct (Z_lt_ge_dec index i) as [Hlt | Hge].
      * assert (Hindex_old : 0 <= index < Zlength digits_2) by lia.
        rewrite app_Znth1 in Hnonzero by lia.
        specialize (PreH36 index Hindex_old Hnonzero).
        destruct PreH36 as [Hnext Hnext2].
        split; intros Hinside.
        -- destruct (Z_lt_ge_dec (index + 1) i) as [Hin | Hin].
           ++ rewrite app_Znth1.
              2: rewrite <- PreH30; lia.
              apply Hnext.
              rewrite <- PreH30.
              exact Hin.
           ++ assert (Heq : index + 1 = i) by lia.
              rewrite app_Znth2.
              2: rewrite <- PreH30; lia.
              replace (index + 1 - Zlength digits_2) with 0 by
                (rewrite <- PreH30; lia).
              cbn.
              exfalso.
              apply Hnonzero.
              replace index with (i - 1) by lia.
              apply Hprev_zero.
              clear - Hindex_old Heq.
              lia.
        -- destruct (Z_lt_ge_dec (index + 2) i) as [Hin | Hin].
           ++ rewrite app_Znth1.
              2: rewrite <- PreH30; lia.
              apply Hnext2.
              rewrite <- PreH30.
              exact Hin.
           ++ rewrite Zlength_app, Zlength_cons, Zlength_nil in Hinside.
              assert (Heq2 : index + 2 = i) by lia.
              rewrite app_Znth2.
              2: rewrite <- PreH30; lia.
              replace (index + 2 - Zlength digits_2) with 0 by
                (rewrite <- PreH30; lia).
              cbn.
              exfalso.
              apply Hnonzero.
              replace index with (i - 2) by lia.
              apply Hprev2_zero.
              clear - Hindex_old Heq2.
              lia.
      * assert (Heq : index = i) by lia.
        subst index.
        split; intros Hinside;
          rewrite Zlength_app, Zlength_cons, Zlength_nil in Hinside;
          lia.
    + intros _.
      rewrite Z.rem_mod_nonneg by lia.
      exact Hshift_mod4.
    + intros [Hi2 Hnz].
      replace (i + 1 - 2) with (i - 1) in Hnz by lia.
      rewrite app_Znth1 in Hnz.
      2: rewrite <- PreH30; lia.
      exfalso.
      apply Hnz.
      apply Hprev_zero.
      lia.
    + rewrite Ha.
      unfold U64_MOD.
      destruct Hm_cases; lia.
Qed.

Lemma proof_of_get_naf_w3_entail_wit_5_4_non_alias_split_goal_1 : get_naf_w3_entail_wit_5_4_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_4_non_alias_split_goal_2 : get_naf_w3_entail_wit_5_4_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_4_non_alias_split_goal_3 : get_naf_w3_entail_wit_5_4_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_4_non_alias_split_goal_4 : get_naf_w3_entail_wit_5_4_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_4_non_alias_split_goal_5 : get_naf_w3_entail_wit_5_4_non_alias_split_goal_5.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_4_non_alias_split_goal_6 : get_naf_w3_entail_wit_5_4_non_alias_split_goal_6.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_4_non_alias_split_goal_7 : get_naf_w3_entail_wit_5_4_non_alias_split_goal_7.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_4_non_alias_split_goal_8 : get_naf_w3_entail_wit_5_4_non_alias_split_goal_8.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_4_non_alias_split_goal_9 : get_naf_w3_entail_wit_5_4_non_alias_split_goal_9.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_4_non_alias_split_goal_10 : get_naf_w3_entail_wit_5_4_non_alias_split_goal_10.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_4_non_alias : get_naf_w3_entail_wit_5_4_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace 7 with (Z.ones 3) in PreH6 by reflexivity.
  rewrite Z.land_ones in PreH6 by lia.
  cbn in PreH6.
  pose proof
    (Z.mod_pos_bound (signed_last_nbits x0_2 8) 8 ltac:(lia)) as Hmod.
  assert (Hfalse : False) by lia.
  exact (False_rect _ Hfalse).
Qed.

Lemma proof_of_get_naf_w3_entail_wit_5_5_non_alias_split_goal_1 : get_naf_w3_entail_wit_5_5_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_5_non_alias_split_goal_2 : get_naf_w3_entail_wit_5_5_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_5_non_alias_split_goal_3 : get_naf_w3_entail_wit_5_5_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_5_non_alias_split_goal_4 : get_naf_w3_entail_wit_5_5_non_alias_split_goal_4.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_5_non_alias_split_goal_5 : get_naf_w3_entail_wit_5_5_non_alias_split_goal_5.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_5_non_alias_split_goal_6 : get_naf_w3_entail_wit_5_5_non_alias_split_goal_6.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_5_non_alias_split_goal_7 : get_naf_w3_entail_wit_5_5_non_alias_split_goal_7.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_5_non_alias_split_goal_8 : get_naf_w3_entail_wit_5_5_non_alias_split_goal_8.
Proof. Abort.

Lemma proof_of_get_naf_w3_entail_wit_5_5_non_alias : get_naf_w3_entail_wit_5_5_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlow8_even : ((x0_2 mod 256) mod 2) = 0).
  {
    rewrite Zland_land in PreH1.
    change (Z.land 7 1) with 1 in PreH1.
    rewrite <- Z.land_assoc, Z.land_diag in PreH1.
    change (Z.land (signed_last_nbits x0_2 8) 1 = 0) in PreH1.
    replace 1 with (Z.ones 1) in PreH1 by reflexivity.
    rewrite Z.land_ones in PreH1 by lia.
    unfold signed_last_nbits in PreH1.
    destruct (Coqlib.zlt (x0_2 mod 2 ^ 8) (2 ^ (8 - 1))).
    - exact PreH1.
    - rewrite Zminus_mod in PreH1.
      change (2 ^ 8 mod 2) with 0 in PreH1.
      rewrite Z.sub_0_r, Z.mod_mod in PreH1 by lia.
      exact PreH1.
  }
  assert (Hlow_even : x0_2 mod 2 = 0).
  {
    apply Z.mod_divide; [lia|].
    apply Z.mod_divide in Hlow8_even; [|lia].
    destruct Hlow8_even as [q Hq].
    exists (128 * (x0_2 / 256) + q).
    pose proof (Z_div_mod_eq_full x0_2 256).
    nia.
  }
  assert (HK_even : Kcur_2 mod 2 = 0).
  {
    rewrite PreH2.
    unfold u256_of_limbs.
    change U64_MOD with (2 * 9223372036854775808).
    replace
      (x0_2 + x1_2 * (2 * 9223372036854775808) +
       x2_2 * (2 * 9223372036854775808) ^ 2 +
       x3_2 * (2 * 9223372036854775808) ^ 3)
      with
      (x0_2 + 2 *
        (x1_2 * 9223372036854775808 +
         x2_2 * 2 * 9223372036854775808 ^ 2 +
         x3_2 * 2 ^ 2 * 9223372036854775808 ^ 3)) by ring.
    rewrite Z.add_mod, Z.mul_mod, Hlow_even.
    cbn.
    all: lia.
  }
  assert (HK_shift : Kcur_2 = 2 * (Kcur_2 ÷ 2)).
  {
    pose proof (Z.quot_rem Kcur_2 2 ltac:(lia)) as Hqr.
    rewrite Z.rem_mod_nonneg in Hqr by lia.
    rewrite HK_even in Hqr.
    lia.
  }
  assert (Hshift_nonneg : 0 <= Kcur_2 ÷ 2).
  {
    pose proof (Z.quot_rem Kcur_2 2 ltac:(lia)) as Hqr.
    rewrite Z.rem_mod_nonneg in Hqr by lia.
    pose proof (Z.mod_pos_bound Kcur_2 2 ltac:(lia)).
    lia.
  }
  Exists X_2 (Kcur_2 ÷ 2) (digits_2 +:: 0).
  split_pure_spatial.
  - rewrite <- PreH2.
    repeat cancel.
    cancel (store_fn pk_pre K_non_alias).
    cancel (store_u256 &( "k") (Kcur_2 ÷ 2)).
    unfold store_u256, store_u256_limbs.
    rewrite (global_u32_v_addr_eq "x"), u32_v_field_address_eq.
    Exists x0 x1 x2 x3.
    split_pure_spatial.
    + entailer!.
      subst X_2.
      apply store_char_undef_store_char.
    + entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    + intros Hi.
      pose proof (PreH25 ltac:(lia)) as Hbound.
      assert (Hpow :
        2 ^ (256 - i) = 2 * 2 ^ (256 - (i + 1))).
      {
        replace (256 - i) with ((256 - (i + 1)) + 1) by lia.
        rewrite Z.pow_add_r by lia.
        change (2 ^ 1) with 2.
        ring.
      }
      rewrite Hpow in Hbound.
      rewrite HK_shift in Hbound.
      nia.
    + intros Hlast.
      assert (Hi : i = 256) by lia.
      pose proof (PreH25 ltac:(lia)) as Hbound.
      replace (256 - i) with 0 in Hbound by lia.
      change (2 ^ 0) with 1 in Hbound.
      lia.
    + assert (Hvalue :
        wnaf3_value (digits_2 +:: 0) = wnaf3_value digits_2).
      {
        unfold wnaf3_value.
        rewrite
          (ZRange.sum_Z_range_Znth_app_single_indexed
            0 0 digits_2 (fun index digit => digit * 2 ^ index)).
        ring.
      }
      rewrite Hvalue, PreH27.
      rewrite Z.pow_add_r by lia.
      change (2 ^ 1) with 2.
      replace ((Kcur_2 ÷ 2) * (2 ^ i * 2)) with
        ((2 * (Kcur_2 ÷ 2)) * 2 ^ i) by ring.
      rewrite <- HK_shift.
      reflexivity.
    + intros j Hj.
      destruct (Z_lt_ge_dec j i) as [Hji | Hji].
      * rewrite app_Znth1 by (rewrite <- PreH23; lia).
        apply PreH28.
        lia.
      * assert (Hjeq : j = i) by lia.
        subst j.
        rewrite app_Znth2 by (rewrite <- PreH23; lia).
        replace (i - Zlength digits_2) with 0 by lia.
        cbn.
        unfold wnaf3_digit.
        tauto.
    + unfold wnaf3_separated in *.
      intros index Hindex Hnonzero.
      rewrite Zlength_app, Zlength_cons, Zlength_nil in Hindex.
      destruct (Z_lt_ge_dec index i) as [Hlt | Hge].
      * assert (Hindex_old : 0 <= index < Zlength digits_2) by lia.
        rewrite app_Znth1 in Hnonzero by lia.
        specialize (PreH29 index Hindex_old Hnonzero).
        destruct PreH29 as [Hnext Hnext2].
        split; intros Hinside.
        -- destruct (Z_lt_ge_dec (index + 1) i) as [Hin | Hin].
           ++ rewrite app_Znth1.
              2: rewrite <- PreH23; lia.
              apply Hnext.
              rewrite <- PreH23.
              exact Hin.
           ++ assert (Heq : index + 1 = i) by lia.
              rewrite app_Znth2.
              2: rewrite <- PreH23; lia.
              replace (index + 1 - Zlength digits_2) with 0 by lia.
              cbn.
              reflexivity.
        -- destruct (Z_lt_ge_dec (index + 2) i) as [Hin | Hin].
           ++ rewrite app_Znth1.
              2: rewrite <- PreH23; lia.
              apply Hnext2.
              rewrite <- PreH23.
              exact Hin.
           ++ rewrite Zlength_app, Zlength_cons, Zlength_nil in Hinside.
              assert (Heq : index + 2 = i) by lia.
              rewrite app_Znth2.
              2: rewrite <- PreH23; lia.
              replace (index + 2 - Zlength digits_2) with 0 by lia.
              cbn.
              reflexivity.
      * assert (Heq : index = i) by lia.
        subst index.
        rewrite app_Znth2 in Hnonzero.
        2: rewrite <- PreH23; lia.
        replace (i - Zlength digits_2) with 0 in Hnonzero by lia.
        cbn in Hnonzero.
        contradiction.
    + intros [_ Hnz].
      rewrite app_Znth2 in Hnz.
      2: rewrite <- PreH23; lia.
      replace (i + 1 - 1 - Zlength digits_2) with 0 in Hnz by lia.
      cbn in Hnz.
      contradiction.
    + intros [Hi2 Hnz].
      replace (i + 1 - 2) with (i - 1) in Hnz by lia.
      rewrite app_Znth1 in Hnz.
      2: rewrite <- PreH23; lia.
      assert (Hi1 : i >= 1) by lia.
      pose proof (PreH30 (conj Hi1 Hnz)) as Hfour.
      rewrite Z.rem_mod_nonneg in Hfour by lia.
      apply Z.mod_divide in Hfour; [|lia].
      destruct Hfour as [q Hq].
      assert (HKdiv : Kcur_2 ÷ 2 = 2 * q).
      {
        rewrite Hq.
        replace (q * 4) with ((2 * q) * 2) by ring.
        apply Z.quot_mul.
        lia.
      }
      rewrite HKdiv.
      replace (2 * q) with (q * 2) by ring.
      assert (0 <= q) by lia.
      rewrite Z.rem_mod_nonneg by lia.
      apply Z.mod_mul.
      lia.
Qed.

Lemma proof_of_get_naf_w3_return_wit_1_non_alias_split_goal_spatial : get_naf_w3_return_wit_1_non_alias_split_goal_spatial.
Proof. Abort.

Lemma proof_of_get_naf_w3_return_wit_1_non_alias : get_naf_w3_return_wit_1_non_alias.
Proof.
  aggressive_pre_process.
  assert (i = 257) by lia.
  subst i.
  assert (Hstore :
    CharArray.full naf_w3_pre 257 digits |--
      store_wnaf3 naf_w3_pre K_non_alias).
  {
    unfold store_wnaf3.
    Exists digits.
    unfold WNAF3_LENGTH.
    change (CharArray.full naf_w3_pre 257 digits |--
      “ wnaf3_representation K_non_alias digits ” &&
      CharArray.full naf_w3_pre 257 digits).
    split_pure_spatial.
    - cancel (CharArray.full naf_w3_pre 257 digits).
    - unfold wnaf3_representation.
      split.
      + exact H.
      + split.
        * intros index Hindex.
          apply PreH9.
          lia.
        * split.
          -- exact PreH10.
          -- pose proof (PreH7 ltac:(lia)) as HKcur.
             rewrite HKcur in PreH8.
             simpl in PreH8.
             lia.
  }
  rewrite H.
  sep_apply_l_atomic Hstore.
  reflexivity.
Qed.

Lemma proof_of_get_naf_w3_partial_solve_wit_2_non_alias_pure_split_goal_1 : get_naf_w3_partial_solve_wit_2_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_get_naf_w3_partial_solve_wit_2_non_alias_pure : get_naf_w3_partial_solve_wit_2_non_alias_pure.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  unfold U64_MOD.
  lia.
Qed.

Lemma proof_of_get_naf_w3_partial_solve_wit_3_non_alias_pure_split_goal_1 : get_naf_w3_partial_solve_wit_3_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_get_naf_w3_partial_solve_wit_3_non_alias_pure : get_naf_w3_partial_solve_wit_3_non_alias_pure.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  unfold U64_MOD.
  lia.
Qed.

Lemma proof_of_get_naf_w3_partial_solve_wit_4_non_alias_pure_split_goal_1 : get_naf_w3_partial_solve_wit_4_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_get_naf_w3_partial_solve_wit_4_non_alias_pure : get_naf_w3_partial_solve_wit_4_non_alias_pure.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  unfold U64_MOD.
  lia.
Qed.

Lemma proof_of_get_naf_w3_partial_solve_wit_5_non_alias_pure_split_goal_1 : get_naf_w3_partial_solve_wit_5_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_get_naf_w3_partial_solve_wit_5_non_alias_pure : get_naf_w3_partial_solve_wit_5_non_alias_pure.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  replace 7 with (Z.ones 3) in PreH19 by reflexivity.
  rewrite Z.land_ones in PreH19 by lia.
  pose proof
    (Z.mod_pos_bound (signed_last_nbits x0 8) (2 ^ 3) ltac:(lia)).
  lia.
Qed.

