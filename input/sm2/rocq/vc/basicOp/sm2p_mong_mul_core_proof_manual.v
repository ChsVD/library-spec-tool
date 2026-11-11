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
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import sm2p_mong_mul_core_goal.
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import sm2p_mong_mul_core_proof_auto.
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
Local Open Scope sac.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_3 : sm2p_mong_mul_core_entail_wit_3.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_3.
  left; intros.
  rename xs_2 into ys.
  rename PreH3 into Hlen.
  rename PreH2 into Hbounded.
  rename PreH1 into Hvalue.
  assert (Hlen9 : Zlength (ys ++ (0%Z :: nil)) = 9).
  { rewrite Zlength_app_cons; lia. }
  assert (Hbounded9 : u64_list_bounded (ys ++ (0%Z :: nil))).
  {
    unfold u64_list_bounded.
    intros j Hj.
    rewrite Zlength_app_cons in Hj.
    destruct (Z_lt_ge_dec j (Zlength ys)) as [Hlt | Hge].
    - rewrite app_Znth1 by lia. apply Hbounded. lia.
    - assert (Hjlen : j = Zlength ys) by lia.
      subst j. rewrite app_Znth2 by lia.
      replace (Zlength ys - Zlength ys) with 0 by lia.
      cbn. unfold U64_MOD. lia.
  }
  assert (Hzero : zero_prefix 0 (ys ++ (0%Z :: nil))).
  { unfold zero_prefix; intros j Hj; lia. }
  assert (Hvalue9 : u64_list_value (ys ++ (0%Z :: nil)) = T).
  {
    change (limb_list_value U64_MOD ys = T) in Hvalue.
    change (limb_list_value U64_MOD (ys ++ (0%Z :: nil)) = T).
    rewrite limb_list_value_app.
    rewrite limb_list_value_cons, limb_list_value_nil.
    change (limb_list_value U64_MOD ys + 0 = T).
    lia.
  }
  assert (Hnonneg : 0 <= u64_list_value (ys ++ (0%Z :: nil))) by lia.
  assert (Hlt576 : u64_list_value (ys ++ (0%Z :: nil)) < U576_MOD).
  {
    rewrite Hvalue9.
    eapply Z.lt_trans; [exact PreH5 |].
    vm_compute. reflexivity.
  }
  Exists (ys ++ (0%Z :: nil)) 0.
  unfold store_sm2_p.
  entailer!.
  - assert (Hone :
      (interim_pre + 8 * sizeof (UINT64)) # UInt64 |-> 0 |--
      UInt64Array.full
        (interim_pre + 8 * sizeof (UINT64)) 1 (0%Z :: nil)).
    {
      unfold UInt64Array.full, store_array.
      cbn [store_array_rec]. entailer!.
      replace (interim_pre + 8 * sizeof (UINT64) +
               0 * sizeof (UINT64))
        with (interim_pre + 8 * sizeof (UINT64)) by lia.
      reflexivity.
    }
    sep_apply Hone.
    sep_apply
      (UInt64Array.full_merge_to_full
        interim_pre 8 9 ys (0%Z :: nil) ltac:(lia)).
    entailer!.
    unfold store_u256_limbs.
    Exists SM2_P_LIMB_0 SM2_P_LIMB_1 SM2_P_LIMB_2 SM2_P_LIMB_3.
    pose proof sm2_p_limbs as HP.
    unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_5_split_goal_1 : sm2p_mong_mul_core_entail_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_5_split_goal_2 : sm2p_mong_mul_core_entail_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_5_split_goal_3 : sm2p_mong_mul_core_entail_wit_5_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_5_split_goal_4 : sm2p_mong_mul_core_entail_wit_5_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_5_split_goal_5 : sm2p_mong_mul_core_entail_wit_5_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_5_split_goal_6 : sm2p_mong_mul_core_entail_wit_5_split_goal_6.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_5 : sm2p_mong_mul_core_entail_wit_5.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_5.
  right.
  intros.
  replace (i + 0) with i in * by lia.
  repeat rewrite replace_Znth_Znth in *.
  set (x1 := replace_Znth i out xs) in *.
  set (x2 := replace_Znth (i + 1) out_2 x1) in *.
  set (x3 := replace_Znth (i + 2) out_3 x2) in *.
  set (ys := replace_Znth (i + 3) out_4 x3) in *.
  change (Znth i xs 0 + SM2_P_LIMB_0 + 0 =
          out + retval_2 * U64_MOD) in PreH46.
  change (Znth (i + 1) x1 0 + SM2_P_LIMB_1 + retval_2 =
          out_2 + retval_3 * U64_MOD) in PreH33.
  change (Znth (i + 2) x2 0 + SM2_P_LIMB_2 + retval_3 =
          out_3 + retval_4 * U64_MOD) in PreH20.
  change (Znth (i + 3) x3 0 + SM2_P_LIMB_3 + retval_4 =
          out_4 + retval * U64_MOD) in PreH7.
  assert (Hlimb0 : SM2_P_LIMB_0 = U64_MOD - 1) by reflexivity.
  assert (Hout : out = 0 /\ retval_2 = 1).
  {
    rewrite PreH55, Hlimb0 in PreH46.
    assert (Hret : retval_2 = 0 \/ retval_2 = 1).
    {
      clear - PreH44 PreH45.
      lia.
    }
    destruct Hret as [Hret | Hret].
    - subst retval_2.
      cbn in PreH46.
      assert (HoutU : out = U64_MOD).
      {
        symmetry.
        rewrite Z.add_0_r in PreH46.
        change (18446744073709551616 = out).
        exact PreH46.
      }
      subst out.
      exfalso.
      exact (Z.lt_irrefl U64_MOD PreH43).
    - subst retval_2.
      cbn in PreH46.
      split.
      + apply (proj1 (Z.add_cancel_r out 0 18446744073709551616)).
        cbn. symmetry. exact PreH46.
      + reflexivity.
  }
  destruct Hout as [Hout Hcarry].
  assert (Hzero1 : zero_prefix (i + 1) x1).
  {
    unfold x1. rewrite Hout.
    apply zero_prefix_replace_Znth_extend.
    - exact PreH69.
    - rewrite PreH67. lia.
  }
  assert (Hys_zero : zero_prefix (i + 1) ys).
  {
    unfold ys.
    apply zero_prefix_replace_Znth_after.
    - unfold x3.
      apply zero_prefix_replace_Znth_after.
      + unfold x2.
        apply zero_prefix_replace_Znth_after.
        * exact Hzero1.
        * lia.
        * rewrite PreH37. lia.
      + lia.
      + rewrite PreH24. lia.
    - lia.
    - rewrite PreH11. lia.
  }
  assert (E0 : Znth i xs 0 + SM2_P_LIMB_0 =
               out + retval_2 * U64_MOD).
  { rewrite <- PreH46. ring. }
  assert (E1 : Znth (i + 1) x1 0 + (SM2_P_LIMB_1 + retval_2) =
               out_2 + retval_3 * U64_MOD).
  { rewrite <- PreH33. ring. }
  assert (E2 : Znth (i + 2) x2 0 + (SM2_P_LIMB_2 + retval_3) =
               out_3 + retval_4 * U64_MOD).
  { rewrite <- PreH20. ring. }
  assert (E3 : Znth (i + 3) x3 0 + (SM2_P_LIMB_3 + retval_4) =
               out_4 + retval * U64_MOD).
  { rewrite <- PreH7. ring. }
  pose proof
    (limb_list_value_carry_step U64_MOD xs i SM2_P_LIMB_0 out retval_2
      ltac:(rewrite PreH67; lia) E0) as V0.
  pose proof
    (limb_list_value_carry_step U64_MOD x1 (i + 1)
      (SM2_P_LIMB_1 + retval_2) out_2 retval_3
      ltac:(rewrite PreH37; lia) E1) as V1.
  pose proof
    (limb_list_value_carry_step U64_MOD x2 (i + 2)
      (SM2_P_LIMB_2 + retval_3) out_3 retval_4
      ltac:(rewrite PreH24; lia) E2) as V2.
  pose proof
    (limb_list_value_carry_step U64_MOD x3 (i + 3)
      (SM2_P_LIMB_3 + retval_4) out_4 retval
      ltac:(rewrite PreH11; lia) E3) as V3.
  fold x1 in V0.
  fold x1 in V1.
  fold x2 in V1.
  fold x2 in V2.
  fold x3 in V2.
  fold x3 in V3.
  fold ys in V3.
  replace (i + 1 + 1) with (i + 2) in V1 by lia.
  replace (i + 2 + 1) with (i + 3) in V2 by lia.
  replace (i + 3 + 1) with (i + 4) in V3 by lia.
  unfold limb_radix in V0, V1, V2, V3.
  assert (V01 :
    u64_list_value x2 + retval_3 * U64_POW (i + 2) =
    u64_list_value xs + SM2_P_LIMB_0 * U64_POW i +
      SM2_P_LIMB_1 * U64_POW (i + 1)).
  {
    change
      (limb_list_value U64_MOD x2 + retval_3 * U64_MOD ^ (i + 2) =
       limb_list_value U64_MOD xs + SM2_P_LIMB_0 * U64_MOD ^ i +
         SM2_P_LIMB_1 * U64_MOD ^ (i + 1)).
    rewrite V1, <- V0. ring.
  }
  assert (V012 :
    u64_list_value x3 + retval_4 * U64_POW (i + 3) =
    u64_list_value xs + SM2_P_LIMB_0 * U64_POW i +
      SM2_P_LIMB_1 * U64_POW (i + 1) +
      SM2_P_LIMB_2 * U64_POW (i + 2)).
  {
    unfold u64_list_value, U64_POW in V01.
    change
      (limb_list_value U64_MOD x3 + retval_4 * U64_MOD ^ (i + 3) =
       limb_list_value U64_MOD xs + SM2_P_LIMB_0 * U64_MOD ^ i +
         SM2_P_LIMB_1 * U64_MOD ^ (i + 1) +
         SM2_P_LIMB_2 * U64_MOD ^ (i + 2)).
    rewrite V2, <- V01. ring.
  }
  assert (V0123 :
    u64_list_value ys + retval * U64_POW (i + 4) =
    u64_list_value xs +
      (SM2_P_LIMB_0 * U64_POW i +
       SM2_P_LIMB_1 * U64_POW (i + 1) +
       SM2_P_LIMB_2 * U64_POW (i + 2) +
       SM2_P_LIMB_3 * U64_POW (i + 3))).
  {
    unfold u64_list_value, U64_POW in V012.
    change
      (limb_list_value U64_MOD ys + retval * U64_MOD ^ (i + 4) =
       limb_list_value U64_MOD xs +
         (SM2_P_LIMB_0 * U64_MOD ^ i +
          SM2_P_LIMB_1 * U64_MOD ^ (i + 1) +
          SM2_P_LIMB_2 * U64_MOD ^ (i + 2) +
          SM2_P_LIMB_3 * U64_MOD ^ (i + 3))).
    transitivity
      (limb_list_value U64_MOD xs + SM2_P_LIMB_0 * U64_MOD ^ i +
       SM2_P_LIMB_1 * U64_MOD ^ (i + 1) +
       SM2_P_LIMB_2 * U64_MOD ^ (i + 2) +
       SM2_P_LIMB_3 * U64_MOD ^ (i + 3)).
    - rewrite V3, <- V012. ring.
    - ring.
  }
  pose proof (sm2_p_shifted_limbs 1 i PreH63) as HPshift.
  rewrite !Z.mul_1_l in HPshift.
  assert (Hrel :
    u64_list_value ys + retval * U64_POW (4 + i) =
    T + (K + U64_POW i) * SM2_P_Z).
  {
    replace (4 + i) with (i + 4) by lia.
    rewrite V0123, <- HPshift, PreH72.
    rewrite Z.mul_add_distr_r.
    rewrite (Z.mul_comm SM2_P_Z (U64_POW i)).
    rewrite Z.add_assoc.
    reflexivity.
  }
  assert (Hone : 0 <= 1 < U64_MOD) by (unfold U64_MOD; lia).
  pose proof
    (sm2p_montgomery_accumulator_bound T K 1 i
      (conj PreH61 PreH62) (conj PreH63 PreH59)
      (conj PreH65 PreH66) Hone) as Htotal.
  pose proof
    (limb_list_value_nonneg U64_MOD ys
      ltac:(unfold U64_MOD; lia) PreH1) as Hys_nonneg.
  pose proof (U64_POW_nonneg (4 + i)) as Hpow_nonneg.
  assert (Hys_lt : u64_list_value ys < U576_MOD).
  {
    clear - Hrel Htotal Hpow_nonneg PreH5.
    nia.
  }
  rewrite Z.mul_1_l in Htotal.
  assert (Hrestore : replace_Znth i 1 xs = xs).
  {
    rewrite <- PreH55.
    apply replace_Znth_Znth.
  }
  entailer!.
  all: rewrite Hrestore.
  all: fold x1; fold x2; fold x3; fold ys.
  all: assumption.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_6_split_goal_1 : sm2p_mong_mul_core_entail_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_6_split_goal_2 : sm2p_mong_mul_core_entail_wit_6_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_6_split_goal_3 : sm2p_mong_mul_core_entail_wit_6_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_6_split_goal_4 : sm2p_mong_mul_core_entail_wit_6_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_6_split_goal_5 : sm2p_mong_mul_core_entail_wit_6_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_6 : sm2p_mong_mul_core_entail_wit_6.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_6.
  right.
  intros.
  repeat rewrite replace_Znth_Znth in *.
  set (ys := replace_Znth pos out ys_2) in *.
  assert (Hposrange : 0 <= pos < Zlength ys_2).
  {
    rewrite PreH29.
    split.
    - eapply Z.le_trans with (m := 4 + i).
      + apply Z.add_nonneg_nonneg.
        * vm_compute. discriminate.
        * exact PreH19.
      + exact PreH24.
    - rewrite PreH16 in PreH14.
      exact PreH14.
  }
  assert (Hzero : zero_prefix (i + 1) ys).
  {
    unfold ys.
    apply zero_prefix_replace_Znth_after.
    - exact PreH31.
    - clear - PreH24. lia.
    - exact Hposrange.
  }
  assert (Hcarryeq :
    Znth pos ys_2 0 + carry = out + retval * U64_MOD).
  {
    rewrite <- PreH7.
    ring.
  }
  pose proof
    (limb_list_value_carry_step U64_MOD ys_2 pos carry out retval
      Hposrange Hcarryeq) as Hstep.
  fold ys in Hstep.
  change
    (u64_list_value ys + retval * U64_POW (pos + 1) =
     u64_list_value ys_2 + carry * U64_POW pos) in Hstep.
  assert (Hrel :
    u64_list_value ys + retval * U64_POW (pos + 1) =
    T + (K + U64_POW i) * SM2_P_Z).
  {
    rewrite Hstep.
    exact PreH36.
  }
  pose proof
    (limb_list_value_nonneg U64_MOD ys
      ltac:(unfold U64_MOD; lia) PreH1) as Hnonneg.
  pose proof (U64_POW_nonneg (pos + 1)) as Hpow_nonneg.
  assert (Hlt : u64_list_value ys < U576_MOD).
  {
    clear - Hrel PreH35 PreH5 Hpow_nonneg.
    nia.
  }
  destruct (Z_lt_ge_dec pos 8) as [Hpos | Hpos].
  - assert (Hbound : pos + 1 + retval <= 9).
    {
      assert (Hpos7 : pos <= 7).
      {
        apply (proj1 (Z.lt_succ_r pos 7)).
        change (pos < 8). exact Hpos.
      }
      pose proof
        (Z.add_le_mono pos 7 retval 1 Hpos7 PreH6) as Hsum.
      apply (proj1 (Z.add_le_mono_r (pos + retval) 8 1)) in Hsum.
      replace (pos + 1 + retval) with ((pos + retval) + 1) by ring.
      change ((pos + retval) + 1 <= 8 + 1).
      exact Hsum.
    }
    entailer!.
  - assert (Hpos_lt9 : pos < 9).
    {
      rewrite <- PreH16. exact PreH14.
    }
    assert (Hpos_le8 : pos <= 8).
    {
      apply (proj1 (Z.lt_succ_r pos 8)).
      change (pos < 9). exact Hpos_lt9.
    }
    assert (Hpos8 : pos = 8).
    {
      apply Z.le_antisymm.
      + exact Hpos_le8.
      + exact (Z.ge_le pos 8 Hpos).
    }
    subst pos.
    assert (Hretval0 : retval = 0).
    {
      destruct (Zle_lt_or_eq 0 retval PreH5)
        as [Hretpos | Hretzero].
      - assert (Hret1 : retval = 1).
        {
          apply Z.le_antisymm.
          + exact PreH6.
          + change (Z.succ 0 <= retval).
            apply Zlt_le_succ. exact Hretpos.
        }
        subst retval.
        replace (U64_POW (8 + 1)) with U576_MOD in Hrel by reflexivity.
        clear - Hrel PreH35 Hnonneg.
        change (0 <= u64_list_value ys) in Hnonneg.
        nia.
      - symmetry. exact Hretzero.
    }
    subst retval.
    entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_7_split_goal_1 : sm2p_mong_mul_core_entail_wit_7_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_7_split_goal_2 : sm2p_mong_mul_core_entail_wit_7_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_7_split_goal_3 : sm2p_mong_mul_core_entail_wit_7_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_7_split_goal_4 : sm2p_mong_mul_core_entail_wit_7_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_7_split_goal_5 : sm2p_mong_mul_core_entail_wit_7_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_7_split_goal_6 : sm2p_mong_mul_core_entail_wit_7_split_goal_6.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_7_split_goal_7 : sm2p_mong_mul_core_entail_wit_7_split_goal_7.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_7_split_goal_8 : sm2p_mong_mul_core_entail_wit_7_split_goal_8.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_7_split_goal_9 : sm2p_mong_mul_core_entail_wit_7_split_goal_9.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_7_split_goal_10 : sm2p_mong_mul_core_entail_wit_7_split_goal_10.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_7 : sm2p_mong_mul_core_entail_wit_7.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_7.
  right.
  intros.
  replace (i + 0) with i in * by lia.
  repeat rewrite replace_Znth_Znth in *.
  set (x1 := replace_Znth i out xs) in *.
  set (x2 := replace_Znth (i + 1) out_2 x1) in *.
  assert (HU64 : 0 < U64_MOD) by (unfold U64_MOD; lia).
  assert (Hnot :
    unsigned_last_nbits (Z.lnot (Znth i xs 0)) 64 =
    U64_MOD - Znth i xs 0 - 1).
  {
    change (Znth i xs 0 < 2 ^ 64) in PreH31.
    unfold unsigned_last_nbits, U64_MOD.
    rewrite Z.lnot_eq_pred_opp.
    symmetry.
    apply Z.mod_unique with (q := -1).
    - left. lia.
    - ring.
  }
  assert (Hlo :
    unsigned_last_nbits
      (unsigned_last_nbits (Z.lnot (Znth i xs 0)) 64 + 1) 64 =
    U64_MOD - Znth i xs 0).
  {
    rewrite Hnot.
    replace (U64_MOD - Znth i xs 0 - 1 + 1)
      with (U64_MOD - Znth i xs 0) by ring.
    apply unsigned_last_nbits_u64_small.
    clear - PreH29 PreH30 PreH31 PreH32.
    lia.
  }
  assert (Hhi :
    unsigned_last_nbits (Znth i xs 0 - 1) 64 =
    Znth i xs 0 - 1).
  {
    apply unsigned_last_nbits_u64_small.
    clear - PreH29 PreH30 PreH31 PreH32.
    lia.
  }
  rewrite Hlo in PreH20.
  assert (Hout : out = 0 /\ retval_2 = 1).
  {
    assert (Hret : retval_2 = 0 \/ retval_2 = 1).
    {
      clear - PreH18 PreH19.
      lia.
    }
    destruct Hret as [Hret | Hret].
    - subst retval_2.
      exfalso.
      clear - PreH20 PreH17.
      unfold U64_MOD in *.
      nia.
    - subst retval_2.
      split.
      + clear - PreH20. nia.
      + reflexivity.
  }
  destruct Hout as [Hout Hcarry].
  assert (Hx1_zero : zero_prefix (i + 1) x1).
  {
    unfold x1.
    rewrite Hout.
    apply zero_prefix_replace_Znth_extend.
    - exact PreH43.
    - rewrite PreH41. lia.
  }
  assert (Hx2_zero : zero_prefix (i + 1) x2).
  {
    unfold x2.
    apply zero_prefix_replace_Znth_after.
    - exact Hx1_zero.
    - lia.
    - rewrite PreH11. lia.
  }
  assert (E0 :
    Znth i xs 0 +
      unsigned_last_nbits
        (unsigned_last_nbits (Z.lnot (Znth i xs 0)) 64 + 1) 64 =
    out + retval_2 * U64_MOD).
  {
    rewrite Hlo.
    clear - PreH20.
    nia.
  }
  pose proof
    (limb_list_value_carry_step U64_MOD xs i
      (unsigned_last_nbits
        (unsigned_last_nbits (Z.lnot (Znth i xs 0)) 64 + 1) 64)
      out retval_2 ltac:(rewrite PreH41; lia) E0) as V0.
  assert (E1 :
    Znth (i + 1) x1 0 +
      (unsigned_last_nbits (Znth i xs 0 - 1) 64 + retval_2) =
    out_2 + retval * U64_MOD).
  {
    rewrite <- PreH7.
    ring.
  }
  pose proof
    (limb_list_value_carry_step U64_MOD x1 (i + 1)
      (unsigned_last_nbits (Znth i xs 0 - 1) 64 + retval_2)
      out_2 retval ltac:(rewrite PreH11; lia) E1) as V1.
  fold x1 in V0.
  fold x1 in V1.
  fold x2 in V1.
  replace (i + 1 + 1) with (i + 2) in V1 by lia.
  unfold limb_radix in V0, V1.
  assert (Hpow : U64_POW (i + 1) = U64_POW i * U64_MOD).
  {
    apply U64_POW_succ.
    exact PreH37.
  }
  assert (Hmul :
    unsigned_last_nbits
      (unsigned_last_nbits (Z.lnot (Znth i xs 0)) 64 + 1) 64 +
    unsigned_last_nbits (Znth i xs 0 - 1) 64 * U64_MOD =
    Znth i xs 0 * SM2_P_LIMB_0).
  {
    rewrite Hlo, Hhi.
    unfold SM2_P_LIMB_0.
    ring.
  }
  assert (Hrel :
    u64_list_value x2 + retval * U64_POW (i + 2) =
    T + K * SM2_P_Z + Znth i xs 0 * SM2_P_LIMB_0 * U64_POW i).
  {
    unfold u64_list_value, U64_POW in Hpow, PreH46 |- *.
    rewrite Hpow in V0, V1.
    clear - V0 V1 Hmul PreH46 Hcarry.
    nia.
  }
  pose proof
    (sm2p_montgomery_stage1_bound T K (Znth i xs 0) i
      (conj PreH35 PreH36) (conj PreH37 PreH33)
      (conj PreH39 PreH40) (conj PreH32 PreH31)) as Hstage.
  destruct Hstage as [Hstage_nonneg Hstage_lt].
  pose proof
    (limb_list_value_nonneg U64_MOD x2
      ltac:(unfold U64_MOD; lia) PreH1) as Hx2_nonneg.
  pose proof (U64_POW_nonneg (i + 2)) as Hpow_nonneg.
  assert (Hx2_lt : u64_list_value x2 < U576_MOD).
  {
    clear - Hrel Hstage_lt Hpow_nonneg PreH5.
    nia.
  }
  pose proof
    (unsigned_Lastnbits_range
      (unsigned_last_nbits (Z.lnot (Znth i xs 0)) 64 + 1) 64
      ltac:(lia)) as Hlo_range.
  pose proof
    (unsigned_Lastnbits_range (Znth i xs 0 - 1) 64
      ltac:(lia)) as Hhi_range.
  change
    (0 <= unsigned_last_nbits
      (unsigned_last_nbits (Z.lnot (Znth i xs 0)) 64 + 1) 64 <
      U64_MOD) in Hlo_range.
  change
    (0 <= unsigned_last_nbits (Znth i xs 0 - 1) 64 < U64_MOD)
    in Hhi_range.
  change (0 <= u64_list_value x2) in Hx2_nonneg.
  replace (2 + i) with (i + 2) by lia.
  entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_8_split_goal_1 : sm2p_mong_mul_core_entail_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_8_split_goal_2 : sm2p_mong_mul_core_entail_wit_8_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_8_split_goal_3 : sm2p_mong_mul_core_entail_wit_8_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_8_split_goal_4 : sm2p_mong_mul_core_entail_wit_8_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_8_split_goal_5 : sm2p_mong_mul_core_entail_wit_8_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_8 : sm2p_mong_mul_core_entail_wit_8.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_8.
  right.
  intros.
  repeat rewrite replace_Znth_Znth in *.
  set (ys := replace_Znth pos out ys_2) in *.
  assert (Hposrange : 0 <= pos < Zlength ys_2).
  {
    rewrite PreH36.
    split.
    - eapply Z.le_trans with (m := 2 + i).
      + apply Z.add_nonneg_nonneg.
        * vm_compute. discriminate.
        * exact PreH19.
      + exact PreH27.
    - rewrite PreH16 in PreH14.
      exact PreH14.
  }
  assert (Hzero : zero_prefix (i + 1) ys).
  {
    unfold ys.
    apply zero_prefix_replace_Znth_after.
    - exact PreH38.
    - clear - PreH27. lia.
    - exact Hposrange.
  }
  assert (Hcarryeq :
    Znth pos ys_2 0 + carry = out + retval * U64_MOD).
  {
    rewrite <- PreH7.
    ring.
  }
  pose proof
    (limb_list_value_carry_step U64_MOD ys_2 pos carry out retval
      Hposrange Hcarryeq) as Hstep.
  fold ys in Hstep.
  change
    (u64_list_value ys + retval * U64_POW (pos + 1) =
     u64_list_value ys_2 + carry * U64_POW pos) in Hstep.
  assert (Hrel :
    u64_list_value ys + retval * U64_POW (pos + 1) =
    T + K * SM2_P_Z + factor * SM2_P_LIMB_0 * U64_POW i).
  {
    rewrite Hstep.
    exact PreH43.
  }
  pose proof
    (limb_list_value_nonneg U64_MOD ys
      ltac:(unfold U64_MOD; lia) PreH1) as Hnonneg.
  pose proof (U64_POW_nonneg (pos + 1)) as Hpow_nonneg.
  assert (Hlt : u64_list_value ys < U576_MOD).
  {
    clear - Hrel PreH42 PreH5 Hpow_nonneg.
    nia.
  }
  destruct (Z_lt_ge_dec pos 8) as [Hpos | Hpos].
  - assert (Hbound : pos + 1 + retval <= 9).
    {
      assert (Hpos7 : pos <= 7).
      {
        apply (proj1 (Z.lt_succ_r pos 7)).
        change (pos < 8).
        exact Hpos.
      }
      pose proof
        (Z.add_le_mono pos 7 retval 1 Hpos7 PreH6) as Hsum.
      apply (proj1 (Z.add_le_mono_r (pos + retval) 8 1)) in Hsum.
      replace (pos + 1 + retval) with ((pos + retval) + 1) by ring.
      change ((pos + retval) + 1 <= 8 + 1).
      exact Hsum.
    }
    entailer!.
  - assert (Hpos_lt9 : pos < 9).
    {
      rewrite <- PreH16.
      exact PreH14.
    }
    assert (Hpos_le8 : pos <= 8).
    {
      apply (proj1 (Z.lt_succ_r pos 8)).
      change (pos < 9).
      exact Hpos_lt9.
    }
    assert (Hpos8 : pos = 8).
    {
      apply Z.le_antisymm.
      + exact Hpos_le8.
      + exact (Z.ge_le pos 8 Hpos).
    }
    subst pos.
    assert (Hretval0 : retval = 0).
    {
      destruct (Zle_lt_or_eq 0 retval PreH5)
        as [Hretpos | Hretzero].
      - assert (Hret1 : retval = 1).
        {
          apply Z.le_antisymm.
          + exact PreH6.
          + change (Z.succ 0 <= retval).
            apply Zlt_le_succ.
            exact Hretpos.
        }
        subst retval.
        replace (U64_POW (8 + 1)) with U576_MOD in Hrel by reflexivity.
        clear - Hrel PreH42 Hnonneg.
        change (0 <= u64_list_value ys) in Hnonneg.
        nia.
      - symmetry.
        exact Hretzero.
    }
    subst retval.
    entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_10_split_goal_1 : sm2p_mong_mul_core_entail_wit_10_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_10_split_goal_2 : sm2p_mong_mul_core_entail_wit_10_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_10_split_goal_3 : sm2p_mong_mul_core_entail_wit_10_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_10_split_goal_4 : sm2p_mong_mul_core_entail_wit_10_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_10_split_goal_5 : sm2p_mong_mul_core_entail_wit_10_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_10_split_goal_6 : sm2p_mong_mul_core_entail_wit_10_split_goal_6.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_10 : sm2p_mong_mul_core_entail_wit_10.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_10.
  right.
  intros.
  repeat rewrite replace_Znth_Znth in *.
  change (factor * SM2_P_LIMB_1 = retval + hi * U64_MOD) in PreH31.
  set (x1 := replace_Znth (i + 1) out ys_2) in *.
  set (ys := replace_Znth (i + 2) out_2 x1) in *.
  assert (Hys_zero : zero_prefix (i + 1) ys).
  {
    unfold ys.
    apply zero_prefix_replace_Znth_after.
    - unfold x1.
      apply zero_prefix_replace_Znth_after.
      + exact PreH55.
      + lia.
      + rewrite PreH53. lia.
    - lia.
    - unfold x1.
      rewrite Zlength_replace_Znth, PreH53.
      lia.
  }
  assert (E0 : Znth (i + 1) ys_2 0 + retval =
             out + retval_3 * U64_MOD).
  {
    rewrite <- PreH20.
    ring.
  }
  pose proof
    (limb_list_value_carry_step U64_MOD ys_2 (i + 1)
      retval out retval_3
      ltac:(rewrite PreH53; lia) E0) as V0.
  assert (E1 : Znth (i + 2) x1 0 + (hi + retval_3) =
             out_2 + retval_2 * U64_MOD).
  {
    rewrite <- PreH7.
    ring.
  }
  pose proof
    (limb_list_value_carry_step U64_MOD x1 (i + 2)
      (hi + retval_3) out_2 retval_2
      ltac:(unfold x1; rewrite Zlength_replace_Znth, PreH53; lia)
      E1) as V1.
  replace (i + 1 + 1) with (i + 2) in V0 by lia.
  replace (i + 2 + 1) with (3 + i) in V1 by lia.
  unfold limb_radix in V0, V1.
  assert (Hpow : U64_POW (i + 2) = U64_POW (i + 1) * U64_MOD).
  {
    replace (i + 2) with ((i + 1) + 1) by lia.
    apply U64_POW_succ.
    apply Z.add_nonneg_nonneg.
    - exact PreH36.
    - vm_compute. discriminate.
  }
  assert (Hcombine :
    u64_list_value ys + retval_2 * U64_POW (3 + i) =
    u64_list_value ys_2 + retval * U64_POW (i + 1) +
      hi * U64_POW (i + 2)).
  {
    change
      (limb_list_value U64_MOD ys + retval_2 * U64_MOD ^ (3 + i) =
       limb_list_value U64_MOD ys_2 + retval * U64_MOD ^ (i + 1) +
         hi * U64_MOD ^ (i + 2)).
    unfold ys.
    rewrite V1, Z.mul_add_distr_r.
    rewrite (Z.add_comm (hi * U64_MOD ^ (i + 2))
              (retval_3 * U64_MOD ^ (i + 2))).
    rewrite Z.add_assoc.
    unfold x1.
    rewrite V0.
    reflexivity.
  }
  assert (Hbase :
    u64_list_value ys_2 =
    T + K * SM2_P_Z + factor * SM2_P_LIMB_0 * U64_POW i).
  {
    rewrite PreH32 in PreH60.
    clear - PreH60.
    nia.
  }
  assert (Hadded :
    retval * U64_POW (i + 1) + hi * U64_POW (i + 2) =
    factor * SM2_P_LIMB_1 * U64_POW (i + 1)).
  {
    rewrite Hpow, PreH31.
    rewrite Z.mul_add_distr_r.
    f_equal.
    rewrite <- Z.mul_assoc.
    f_equal.
    apply Z.mul_comm.
  }
  assert (Hrel :
    u64_list_value ys + retval_2 * U64_POW (3 + i) =
    T + K * SM2_P_Z + factor * SM2_P_LIMB_0 * U64_POW i +
      factor * SM2_P_LIMB_1 * U64_POW (i + 1)).
  {
    rewrite Hcombine, Hbase.
    clear - Hadded.
    nia.
  }
  pose proof
    (sm2p_montgomery_stage2_bound T K factor i
      (conj PreH34 PreH35) (conj PreH36 PreH37)
      (conj PreH42 PreH43) (conj PreH38 PreH39)) as Htotal.
  destruct Htotal as [Htotal_nonneg Htotal_lt].
  pose proof
    (limb_list_value_nonneg U64_MOD ys
      ltac:(unfold U64_MOD; lia) PreH1) as Hys_nonneg.
  pose proof (U64_POW_nonneg (3 + i)) as Hpow_nonneg.
  assert (Hys_lt : u64_list_value ys < U576_MOD).
  {
    clear - Hrel Htotal_lt Hpow_nonneg PreH5.
    nia.
  }
  change (0 <= u64_list_value ys) in Hys_nonneg.
  entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_11_split_goal_1 : sm2p_mong_mul_core_entail_wit_11_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_11_split_goal_2 : sm2p_mong_mul_core_entail_wit_11_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_11_split_goal_3 : sm2p_mong_mul_core_entail_wit_11_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_11_split_goal_4 : sm2p_mong_mul_core_entail_wit_11_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_11_split_goal_5 : sm2p_mong_mul_core_entail_wit_11_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_11 : sm2p_mong_mul_core_entail_wit_11.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_11.
  LLM_pre_process ltac:(idtac).
  repeat rewrite replace_Znth_Znth in *.
  assert (Hpos : 0 <= pos < Zlength ys_2) by (rewrite PreH34; lia).
  assert (Hdigit : Znth pos ys_2 0 + carry =
                   out + retval * U64_MOD) by lia.
  pose proof
    (limb_list_value_carry_step U64_MOD ys_2 pos carry out retval Hpos Hdigit)
    as Hstep.
  set (ys := replace_Znth pos out ys_2) in *.
  assert (Hlen : Zlength ys = 9).
  {
    unfold ys.
    rewrite Zlength_replace_Znth.
    exact PreH34.
  }
  assert (Hbounded : u64_list_bounded ys).
  {
    unfold ys.
    apply limb_list_bounded_replace_Znth.
    - exact PreH35.
    - exact Hpos.
    - split; assumption.
  }
  assert (Hzero : zero_prefix (i + 1) ys).
  {
    unfold ys.
    apply zero_prefix_replace_Znth_after.
    - exact PreH36.
    - lia.
    - exact Hpos.
  }
  pose proof
    (limb_list_value_nonneg U64_MOD ys
      ltac:(unfold U64_MOD; lia) Hbounded) as Hnonneg.
  change (0 <= u64_list_value ys) in Hnonneg.
  pose proof (U64_POW_nonneg (pos + 1)) as Hpow_nonneg.
  assert (Hvalue :
    u64_list_value ys + retval * U64_POW (pos + 1) =
      T + K * SM2_P_Z + factor * SM2_P_LIMB_0 * U64_POW i +
      factor * SM2_P_LIMB_1 * U64_POW (i + 1)).
  {
    change
      (u64_list_value ys + retval * U64_POW (pos + 1) =
       u64_list_value ys_2 + carry * U64_POW pos) in Hstep.
    rewrite Hstep.
    exact PreH41.
  }
  assert (Hvalue_lt : u64_list_value ys < U576_MOD) by nia.
  assert (Hcarry1 : carry = 1) by lia.
  assert (Hpos_le8 : pos <= 8) by lia.
  assert (Hnext_bound : pos + 1 + retval <= 9).
  {
    destruct (Z_lt_ge_dec pos 8) as [Hpos8 | Hpos8].
    - lia.
    - assert (Hpos_eq8 : pos = 8) by lia.
      subst pos.
      assert (Hretval0 : retval = 0).
      {
        assert (Hret : retval = 0 \/ retval = 1) by lia.
        destruct Hret as [Hret | Hret]; [exact Hret |].
        subst retval.
        replace (U64_POW (8 + 1)) with U576_MOD in Hvalue by reflexivity.
        nia.
      }
      lia.
  }
  Exists ys.
  entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_12_split_goal_1 : sm2p_mong_mul_core_entail_wit_12_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_12_split_goal_2 : sm2p_mong_mul_core_entail_wit_12_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_12_split_goal_3 : sm2p_mong_mul_core_entail_wit_12_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_12_split_goal_4 : sm2p_mong_mul_core_entail_wit_12_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_12_split_goal_5 : sm2p_mong_mul_core_entail_wit_12_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_12_split_goal_6 : sm2p_mong_mul_core_entail_wit_12_split_goal_6.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_12_split_goal_7 : sm2p_mong_mul_core_entail_wit_12_split_goal_7.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_12_split_goal_8 : sm2p_mong_mul_core_entail_wit_12_split_goal_8.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_12 : sm2p_mong_mul_core_entail_wit_12.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_12.
  LLM_pre_process ltac:(idtac).
  repeat rewrite replace_Znth_Znth in *.
  set (negf :=
    unsigned_last_nbits
      (unsigned_last_nbits (Z.lnot factor) 64 + 1) 64) in *.
  set (predf := unsigned_last_nbits (factor - 1) 64) in *.
  set (x1 := replace_Znth (i + 2) out ys_2) in *.
  set (ys := replace_Znth (i + 3) out_2 x1) in *.
  Exists ys.
  split_pure_spatial.
  - entailer!.
  - assert (Hinner :
      unsigned_last_nbits (Z.lnot factor) 64 = U64_MOD - factor - 1).
    {
      unfold unsigned_last_nbits.
      change ((Z.lnot factor) mod U64_MOD = U64_MOD - factor - 1).
      rewrite Z.lnot_eq_pred_opp.
      symmetry.
      apply Z.mod_unique with (q := -1).
      - left. lia.
      - ring.
    }
    assert (Hneg : negf = U64_MOD - factor).
    {
      unfold negf.
      rewrite Hinner.
      replace (U64_MOD - factor - 1 + 1) with (U64_MOD - factor) by lia.
      apply unsigned_last_nbits_u64_small.
      split; lia.
    }
    assert (Hpred : predf = factor - 1).
    {
      unfold predf.
      apply unsigned_last_nbits_u64_small.
      split; lia.
    }
    assert (Hys_len : Zlength ys = 9).
    {
      unfold ys, x1.
      repeat rewrite Zlength_replace_Znth.
      exact PreH46.
    }
    assert (Hys_bounded : u64_list_bounded ys).
    {
      unfold ys.
      apply limb_list_bounded_replace_Znth.
      - unfold x1.
        apply limb_list_bounded_replace_Znth.
        + exact PreH47.
        + rewrite PreH46. lia.
        + split; assumption.
      - unfold x1.
        rewrite Zlength_replace_Znth, PreH46.
        lia.
      - split; assumption.
    }
    assert (Hys_zero : zero_prefix (i + 1) ys).
    {
      unfold ys.
      apply zero_prefix_replace_Znth_after.
      - unfold x1.
        apply zero_prefix_replace_Znth_after.
        + exact PreH48.
        + lia.
        + rewrite PreH46. lia.
      - lia.
      - unfold x1.
        rewrite Zlength_replace_Znth, PreH46.
        lia.
    }
    assert (E0 : Znth (i + 2) ys_2 0 + negf =
                   out + retval_2 * U64_MOD) by lia.
    pose proof
      (limb_list_value_carry_step U64_MOD ys_2 (i + 2) negf out retval_2
        ltac:(rewrite PreH46; lia) E0) as V0.
    assert (E1 : Znth (i + 3) x1 0 + (predf + retval_2) =
                   out_2 + retval * U64_MOD) by lia.
    pose proof
      (limb_list_value_carry_step U64_MOD x1 (i + 3) (predf + retval_2)
        out_2 retval
        ltac:(unfold x1; rewrite Zlength_replace_Znth, PreH46; lia) E1)
      as V1.
    fold x1 in V0.
    fold x1 in V1.
    fold ys in V1.
    replace (i + 2 + 1) with (i + 3) in V0 by lia.
    replace (i + 3 + 1) with (4 + i) in V1 by lia.
    change
      (u64_list_value x1 + retval_2 * U64_POW (i + 3) =
       u64_list_value ys_2 + negf * U64_POW (i + 2)) in V0.
    change
      (u64_list_value ys + retval * U64_POW (4 + i) =
       u64_list_value x1 + (predf + retval_2) * U64_POW (i + 3)) in V1.
    assert (Hpow : U64_POW (i + 3) = U64_POW (i + 2) * U64_MOD).
    {
      replace (i + 3) with ((i + 2) + 1) by lia.
      apply U64_POW_succ.
      lia.
    }
    assert (Hcombine :
      u64_list_value ys + retval * U64_POW (4 + i) =
      u64_list_value ys_2 + negf * U64_POW (i + 2) +
        predf * U64_POW (i + 3)).
    {
      rewrite V1, Z.mul_add_distr_r.
      rewrite (Z.add_comm (predf * U64_POW (i + 3))
        (retval_2 * U64_POW (i + 3))).
      rewrite Z.add_assoc.
      rewrite V0.
      reflexivity.
    }
    assert (Hbase :
      u64_list_value ys_2 =
      T + K * SM2_P_Z + factor * SM2_P_LIMB_0 * U64_POW i +
        factor * SM2_P_LIMB_1 * U64_POW (i + 1)).
    {
      rewrite PreH25 in PreH53.
      nia.
    }
    assert (Hlimb2 : SM2_P_LIMB_2 = U64_MOD - 1) by reflexivity.
    assert (Hadded :
      negf * U64_POW (i + 2) + predf * U64_POW (i + 3) =
      factor * SM2_P_LIMB_2 * U64_POW (i + 2)).
    {
      rewrite Hneg, Hpred, Hpow, Hlimb2.
      ring.
    }
    assert (Hrel :
      u64_list_value ys + retval * U64_POW (4 + i) =
      T + K * SM2_P_Z + factor * SM2_P_LIMB_0 * U64_POW i +
        factor * SM2_P_LIMB_1 * U64_POW (i + 1) +
        factor * SM2_P_LIMB_2 * U64_POW (i + 2)).
    {
      rewrite Hcombine, Hbase, <- Z.add_assoc.
      rewrite Hadded.
      reflexivity.
    }
    pose proof
      (sm2p_montgomery_stage3_bound T K factor i
        (conj PreH27 PreH28) (conj PreH29 PreH30)
        (conj PreH35 PreH36) (conj PreH31 PreH32)) as Htotal.
    pose proof
      (limb_list_value_nonneg U64_MOD ys
        ltac:(unfold U64_MOD; lia) Hys_bounded) as Hys_nonneg.
    change (0 <= u64_list_value ys) in Hys_nonneg.
    pose proof (U64_POW_nonneg (4 + i)) as Hpow_nonneg.
    assert (Htail : 0 <= retval * U64_POW (4 + i)) by nia.
    assert (Hys_lt : u64_list_value ys < U576_MOD) by lia.
    split_pure_and_solve.
    all: entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_13_split_goal_1 : sm2p_mong_mul_core_entail_wit_13_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_13_split_goal_2 : sm2p_mong_mul_core_entail_wit_13_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_13_split_goal_3 : sm2p_mong_mul_core_entail_wit_13_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_13_split_goal_4 : sm2p_mong_mul_core_entail_wit_13_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_13_split_goal_5 : sm2p_mong_mul_core_entail_wit_13_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_13 : sm2p_mong_mul_core_entail_wit_13.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_13.
  LLM_pre_process ltac:(idtac).
  repeat rewrite replace_Znth_Znth in *.
  assert (Hcarry : carry = 1) by lia.
  assert (Hpos : 0 <= pos < Zlength ys_2) by (rewrite PreH34; lia).
  assert (Hdigit : Znth pos ys_2 0 + carry =
                   out + retval * U64_MOD) by lia.
  pose proof
    (limb_list_value_carry_step U64_MOD ys_2 pos carry out retval Hpos Hdigit)
    as Hstep.
  set (ys := replace_Znth pos out ys_2) in *.
  assert (Hlen : Zlength ys = 9).
  {
    unfold ys.
    rewrite Zlength_replace_Znth.
    exact PreH34.
  }
  assert (Hbounded : u64_list_bounded ys).
  {
    unfold ys.
    apply limb_list_bounded_replace_Znth.
    - exact PreH35.
    - exact Hpos.
    - split; assumption.
  }
  assert (Hzero : zero_prefix (i + 1) ys).
  {
    unfold ys.
    apply zero_prefix_replace_Znth_after.
    - exact PreH36.
    - lia.
    - exact Hpos.
  }
  pose proof
    (limb_list_value_nonneg U64_MOD ys
      ltac:(unfold U64_MOD; lia) Hbounded) as Hnonneg.
  change (0 <= u64_list_value ys) in Hnonneg.
  pose proof (U64_POW_nonneg (pos + 1)) as Hpow_nonneg.
  assert (Hvalue :
    u64_list_value ys + retval * U64_POW (pos + 1) =
      T + K * SM2_P_Z + factor * SM2_P_LIMB_0 * U64_POW i +
      factor * SM2_P_LIMB_1 * U64_POW (i + 1) +
      factor * SM2_P_LIMB_2 * U64_POW (i + 2)).
  {
    change
      (u64_list_value ys + retval * U64_POW (pos + 1) =
       u64_list_value ys_2 + carry * U64_POW pos) in Hstep.
    rewrite Hstep.
    exact PreH41.
  }
  assert (Hvalue_lt : u64_list_value ys < U576_MOD) by nia.
  assert (Hnext_bound : pos + 1 + retval <= 9).
  {
    destruct (Z_lt_ge_dec (pos + 1) 9) as [Hlt | Hlast]; [lia |].
    assert (Hpos9 : pos + 1 = 9) by lia.
    assert (Hretval : retval = 0).
    {
      assert (retval = 0 \/ retval = 1) as [-> | ->] by lia;
        [reflexivity |].
      rewrite Hpos9 in Hvalue.
      replace (U64_POW 9) with U576_MOD in Hvalue by reflexivity.
      nia.
    }
    lia.
  }
  Exists ys.
  entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_15_split_goal_1 : sm2p_mong_mul_core_entail_wit_15_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_15_split_goal_2 : sm2p_mong_mul_core_entail_wit_15_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_15_split_goal_3 : sm2p_mong_mul_core_entail_wit_15_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_15_split_goal_4 : sm2p_mong_mul_core_entail_wit_15_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_15_split_goal_5 : sm2p_mong_mul_core_entail_wit_15_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_15_split_goal_6 : sm2p_mong_mul_core_entail_wit_15_split_goal_6.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_15 : sm2p_mong_mul_core_entail_wit_15.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_15.
  LLM_pre_process ltac:(idtac).
  repeat rewrite replace_Znth_Znth in *.
  change (factor * SM2_P_LIMB_3 = retval + hi * U64_MOD) in PreH29.
  set (x3 := replace_Znth (i + 3) out ys_2) in *.
  set (ys := replace_Znth (i + 4) out_2 x3) in *.
  Exists ys.
  split_pure_spatial.
  - unfold store_sm2_p, store_u256_limbs.
    Exists SM2_P_LIMB_0 SM2_P_LIMB_1 SM2_P_LIMB_2 SM2_P_LIMB_3.
    pose proof sm2_p_limbs as HP.
    unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    entailer!.
  - assert (Hx3_len : Zlength x3 = 9).
    {
      unfold x3.
      rewrite Zlength_replace_Znth.
      exact PreH51.
    }
    assert (Hys_len : Zlength ys = 9).
    {
      unfold ys.
      rewrite Zlength_replace_Znth.
      exact Hx3_len.
    }
    assert (Hx3_bounded : u64_list_bounded x3).
    {
      unfold x3.
      apply limb_list_bounded_replace_Znth.
      - exact PreH52.
      - rewrite PreH51. lia.
      - split; assumption.
    }
    assert (Hys_bounded : u64_list_bounded ys).
    {
      unfold ys.
      apply limb_list_bounded_replace_Znth.
      - exact Hx3_bounded.
      - rewrite Hx3_len. lia.
      - split; assumption.
    }
    assert (Hx3_zero : zero_prefix (i + 1) x3).
    {
      unfold x3.
      apply zero_prefix_replace_Znth_after.
      - exact PreH53.
      - lia.
      - rewrite PreH51. lia.
    }
    assert (Hys_zero : zero_prefix (i + 1) ys).
    {
      unfold ys.
      apply zero_prefix_replace_Znth_after.
      - exact Hx3_zero.
      - lia.
      - rewrite Hx3_len. lia.
    }
    assert (E3 : Znth (i + 3) ys_2 0 + retval =
                   out + retval_3 * U64_MOD) by lia.
    pose proof
      (limb_list_value_carry_step U64_MOD ys_2 (i + 3) retval out retval_3
        ltac:(rewrite PreH51; lia) E3) as V3.
    fold x3 in V3.
    assert (E4 : Znth (i + 4) x3 0 + (hi + retval_3) =
                   out_2 + retval_2 * U64_MOD) by lia.
    pose proof
      (limb_list_value_carry_step U64_MOD x3 (i + 4) (hi + retval_3)
        out_2 retval_2 ltac:(rewrite Hx3_len; lia) E4) as V4.
    fold ys in V4.
    replace (i + 3 + 1) with (i + 4) in V3 by lia.
    replace (i + 4 + 1) with (i + 5) in V4 by lia.
    change
      (u64_list_value x3 + retval_3 * U64_POW (i + 4) =
       u64_list_value ys_2 + retval * U64_POW (i + 3)) in V3.
    change
      (u64_list_value ys + retval_2 * U64_POW (i + 5) =
       u64_list_value x3 + (hi + retval_3) * U64_POW (i + 4)) in V4.
    assert (Hpow4 : U64_POW (i + 4) = U64_POW (i + 3) * U64_MOD).
    {
      replace (i + 4) with ((i + 3) + 1) by lia.
      apply U64_POW_succ.
      lia.
    }
    pose proof (sm2_p_shifted_limbs factor i PreH34) as HPshift.
    assert (Hbase :
      T + (K + factor * U64_POW i) * SM2_P_Z =
      T + K * SM2_P_Z +
        factor * SM2_P_LIMB_0 * U64_POW i +
        factor * SM2_P_LIMB_1 * U64_POW (i + 1) +
        factor * SM2_P_LIMB_2 * U64_POW (i + 2) +
        factor * SM2_P_LIMB_3 * U64_POW (i + 3)).
    {
      nia.
    }
    assert (Hrel :
      u64_list_value ys + retval_2 * U64_POW (i + 5) =
      T + (K + factor * U64_POW i) * SM2_P_Z).
    {
      rewrite Hbase.
      rewrite PreH30 in PreH58.
      rewrite Hpow4 in V3, V4.
      nia.
    }
    pose proof
      (sm2p_montgomery_accumulator_bound T K factor i
        (conj PreH32 PreH33) (conj PreH34 PreH35)
        (conj PreH40 PreH41) (conj PreH36 PreH37)) as Htotal.
    pose proof
      (limb_list_value_nonneg U64_MOD ys
        ltac:(unfold U64_MOD; lia) Hys_bounded) as Hys_nonneg.
    change (0 <= u64_list_value ys) in Hys_nonneg.
    pose proof (U64_POW_nonneg (i + 5)) as Hpow_nonneg.
    assert (Htail : 0 <= retval_2 * U64_POW (i + 5)) by nia.
    assert (Hys_lt : u64_list_value ys < U576_MOD) by lia.
    replace (i + 5) with (5 + i) in Hrel by lia.
    split_pure_and_solve.
    all: entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_16_split_goal_1 : sm2p_mong_mul_core_entail_wit_16_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_16_split_goal_2 : sm2p_mong_mul_core_entail_wit_16_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_16_split_goal_3 : sm2p_mong_mul_core_entail_wit_16_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_16_split_goal_4 : sm2p_mong_mul_core_entail_wit_16_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_16_split_goal_5 : sm2p_mong_mul_core_entail_wit_16_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_16 : sm2p_mong_mul_core_entail_wit_16.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_16.
  LLM_pre_process ltac:(idtac).
  repeat rewrite replace_Znth_Znth in *.
  assert (Hcarry : carry = 1) by lia.
  assert (Hpos : 0 <= pos < Zlength ys_2) by (rewrite PreH34; lia).
  assert (Hdigit : Znth pos ys_2 0 + carry =
                   out + retval * U64_MOD) by lia.
  pose proof
    (limb_list_value_carry_step U64_MOD ys_2 pos carry out retval Hpos Hdigit)
    as Hstep.
  set (ys := replace_Znth pos out ys_2) in *.
  assert (Hlen : Zlength ys = 9).
  {
    unfold ys.
    rewrite Zlength_replace_Znth.
    exact PreH34.
  }
  assert (Hbounded : u64_list_bounded ys).
  {
    unfold ys.
    apply limb_list_bounded_replace_Znth.
    - exact PreH35.
    - exact Hpos.
    - split; assumption.
  }
  assert (Hzero : zero_prefix (i + 1) ys).
  {
    unfold ys.
    apply zero_prefix_replace_Znth_after.
    - exact PreH36.
    - lia.
    - exact Hpos.
  }
  pose proof
    (limb_list_value_nonneg U64_MOD ys
      ltac:(unfold U64_MOD; lia) Hbounded) as Hnonneg.
  change (0 <= u64_list_value ys) in Hnonneg.
  pose proof (U64_POW_nonneg (pos + 1)) as Hpow_nonneg.
  assert (Hvalue :
    u64_list_value ys + retval * U64_POW (pos + 1) =
      T + (K + factor * U64_POW i) * SM2_P_Z).
  {
    change
      (u64_list_value ys + retval * U64_POW (pos + 1) =
       u64_list_value ys_2 + carry * U64_POW pos) in Hstep.
    rewrite Hstep.
    exact PreH41.
  }
  assert (Hvalue_lt : u64_list_value ys < U576_MOD) by nia.
  assert (Hnext_bound : pos + 1 + retval <= 9).
  {
    destruct (Z_lt_ge_dec (pos + 1) 9) as [Hlt | Hlast]; [lia |].
    assert (Hpos9 : pos + 1 = 9) by lia.
    assert (Hretval : retval = 0).
    {
      assert (retval = 0 \/ retval = 1) as [-> | ->] by lia;
        [reflexivity |].
      rewrite Hpos9 in Hvalue.
      replace (U64_POW 9) with U576_MOD in Hvalue by reflexivity.
      nia.
    }
    lia.
  }
  Exists ys.
  entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_17_1 : sm2p_mong_mul_core_entail_wit_17_1.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_17_1.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists ys (K_2 + factor * U64_POW i).
  entailer!.
  pose proof
    (u64_montgomery_coefficient_bound K_2 factor i PreH5
      (conj PreH11 PreH12) (conj PreH7 PreH8)) as HK.
  exact (proj2 HK).
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_17_2 : sm2p_mong_mul_core_entail_wit_17_2.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_17_2.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite replace_Znth_Znth.
  Exists xs_2 K_2.
  split_pure_spatial.
  - unfold store_sm2_p, store_u256_limbs.
    Exists SM2_P_LIMB_0 SM2_P_LIMB_1 SM2_P_LIMB_2 SM2_P_LIMB_3.
    pose proof sm2_p_limbs as HP.
    unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    entailer!.
  - entailer!.
  + assert (Hrange : 0 <= i < Zlength xs_2) by lia.
    pose proof
      (zero_prefix_replace_Znth_extend xs_2 i PreH14 Hrange) as Hz.
    rewrite <- PreH1 in Hz.
    rewrite replace_Znth_Znth in Hz.
    exact Hz.
  + rewrite U64_POW_succ.
    pose proof (U64_POW_nonneg i) as Hpow.
    unfold U64_MOD.
    nia.
    exact PreH8.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_17_3 : sm2p_mong_mul_core_entail_wit_17_3.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_17_3.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists ys (K_2 + U64_POW i).
  entailer!.
  pose proof
    (u64_montgomery_coefficient_bound K_2 1 i PreH5
      (conj PreH8 PreH9)) as HK.
  assert (Hone : 0 <= 1 < U64_MOD) by (unfold U64_MOD; lia).
  specialize (HK Hone).
  nia.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_19_1_split_goal_1 : sm2p_mong_mul_core_entail_wit_19_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_19_1_split_goal_2 : sm2p_mong_mul_core_entail_wit_19_1_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_19_1 : sm2p_mong_mul_core_entail_wit_19_1.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_19_1.
  right. intros.
  unfold SM2_RHOP_Z in PreH5.
  assert (HC : C = 1) by lia.
  assert (Hret : retval_2 = 0).
  { nia. }
  destruct sm2_p_montgomery_bounds as [HPbound Hhalf].
  entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_19_2_split_goal_1 : sm2p_mong_mul_core_entail_wit_19_2_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_19_2_split_goal_2 : sm2p_mong_mul_core_entail_wit_19_2_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_entail_wit_19_2 : sm2p_mong_mul_core_entail_wit_19_2.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_19_2.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_u256_limbs at 1.
  Intros x0 x1 x2 x3.
  destruct sm2_p_montgomery_bounds as [_ Hhalf].
  Exists X C X.
  entailer!.
  unfold store_u256_limbs at 1.
  Exists x0 x1 x2 x3.
  entailer!.
  unfold store_sm2_rhop, store_u256.
  rewrite <- (global_u32_v_addr_eq "SM2_rhoP").
  reflexivity.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_24_1 : sm2p_mong_mul_core_entail_wit_24_1.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_24_1.
  right; intros.
  pose proof sm2_rhop_limbs as [Hrho Hrbounds].
  assert (Hneg : SM2_P_Z + SM2_RHOP_Z = U256_MOD).
  { unfold SM2_RHOP_Z. lia. }
  assert (HPval :
    SM2_P_Z =
      u256_of_limbs
        SM2_P_LIMB_0 SM2_P_LIMB_1 SM2_P_LIMB_2 SM2_P_LIMB_3)
    by reflexivity.
  rewrite u64_list_value_four in PreH9.
  rewrite <- HPval in PreH9.
  assert (Hret3 : retval_3 = 1) by nia.
  assert (HS : S = Y - SM2_P_Z) by nia.
  Exists (K - Ckeep * U256_MOD - U256_MOD).
  rewrite u64_list_value_four.
  entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_entail_wit_24_2 : sm2p_mong_mul_core_entail_wit_24_2.
Proof.
  unfold sm2p_mong_mul_core_entail_wit_24_2.
  right; intros.
  Exists (K - Ckeep * U256_MOD).
  rewrite u64_list_value_four.
  entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_return_wit_1 : sm2p_mong_mul_core_return_wit_1.
Proof.
  unfold sm2p_mong_mul_core_return_wit_1.
  left. intros.
  Exists K2 Zout_2.
  unfold store_fp, store_mod.
  entailer!.
  unfold store_u256_limbs at 1.
  Intros x0 x1 x2 x3.
  assert (Htail :
    ((interim_pre + 4 * sizeof(UINT64)) # UInt64 |-> x0) **
    ((interim_pre + 5 * sizeof(UINT64)) # UInt64 |-> x1) **
    ((interim_pre + 6 * sizeof(UINT64)) # UInt64 |-> x2) **
    ((interim_pre + 7 * sizeof(UINT64)) # UInt64 |-> x3) **
    ((interim_pre + 8 * sizeof(UINT64)) # UInt64 |-> Ckeep)
    |-- UInt64Array.full_shape
          (interim_pre + 4 * sizeof(UINT64)) 5).
  {
    unfold UInt64Array.full_shape, store_undef_array.
    cbn [store_undef_array_rec Z.to_nat].
    cbv [Pos.to_nat Pos.iter_op Nat.add].
    cbn [store_undef_array_rec].
    Exists x0 x1 x2 x3 Ckeep.
    rewrite !sizeof_uint64.
    replace (interim_pre + 4 * 8 + (0 + 1 + 1 + 1 + 1) * 8)
      with (interim_pre + 8 * 8) by lia.
    replace (interim_pre + 4 * 8 + (0 + 1 + 1 + 1) * 8)
      with (interim_pre + 7 * 8) by lia.
    replace (interim_pre + 4 * 8 + (0 + 1 + 1) * 8)
      with (interim_pre + 6 * 8) by lia.
    replace (interim_pre + 4 * 8 + (0 + 1) * 8)
      with (interim_pre + 5 * 8) by lia.
    replace (interim_pre + 4 * 8 + 0 * 8)
      with (interim_pre + 4 * 8) by lia.
    entailer!.
  }
  replace (interim_pre + (4 + 3) * sizeof(UINT64))
    with (interim_pre + 7 * sizeof(UINT64)) by lia.
  replace (interim_pre + (4 + 2) * sizeof(UINT64))
    with (interim_pre + 6 * sizeof(UINT64)) by lia.
  replace (interim_pre + (4 + 1) * sizeof(UINT64))
    with (interim_pre + 5 * sizeof(UINT64)) by lia.
  replace (interim_pre + 4 * sizeof(UINT64) + 3 * sizeof(UINT64))
    with (interim_pre + 7 * sizeof(UINT64)) by lia.
  replace (interim_pre + 4 * sizeof(UINT64) + 2 * sizeof(UINT64))
    with (interim_pre + 6 * sizeof(UINT64)) by lia.
  replace (interim_pre + 4 * sizeof(UINT64) + 1 * sizeof(UINT64))
    with (interim_pre + 5 * sizeof(UINT64)) by lia.
  replace (interim_pre + 4 * sizeof(UINT64) + 0 * sizeof(UINT64))
    with (interim_pre + 4 * sizeof(UINT64)) by lia.
  sep_apply Htail.
  sep_apply
    (UInt64Array.full_shape_merge_to_full_shape
      interim_pre 4 9 ltac:(lia)).
  entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_4_pure_split_goal_1 : sm2p_mong_mul_core_partial_solve_wit_4_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_4_pure_split_goal_2 : sm2p_mong_mul_core_partial_solve_wit_4_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_4_pure : sm2p_mong_mul_core_partial_solve_wit_4_pure.
Proof.
  unfold sm2p_mong_mul_core_partial_solve_wit_4_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (i + 0) with i in * by lia.
  entailer!.
  exact (proj1 (proj1 sm2_p_limbs)).
Qed. 

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_7_pure_split_goal_1 : sm2p_mong_mul_core_partial_solve_wit_7_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_7_pure_split_goal_2 : sm2p_mong_mul_core_partial_solve_wit_7_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_7_pure : sm2p_mong_mul_core_partial_solve_wit_7_pure.
Proof.
  unfold sm2p_mong_mul_core_partial_solve_wit_7_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Znth_replace_Znth_Diff by lia.
  entailer!.
  pose proof sm2_p_limbs as [HL0 [HL1 [HL2 [HL3 HP]]]].
  - exact (proj1 HL1).
  - apply PreH33; lia.
  - apply PreH33; lia.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_10_pure_split_goal_1 : sm2p_mong_mul_core_partial_solve_wit_10_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_10_pure_split_goal_2 : sm2p_mong_mul_core_partial_solve_wit_10_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_10_pure : sm2p_mong_mul_core_partial_solve_wit_10_pure.
Proof.
  unfold sm2p_mong_mul_core_partial_solve_wit_10_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Znth_replace_Znth_Diff by lia.
  entailer!.
  pose proof sm2_p_limbs as [HL0 [HL1 [HL2 [HL3 HP]]]].
  destruct HL0 as [HL0lo HL0hi].
  destruct HL1 as [HL1lo HL1hi].
  destruct HL2 as [HL2lo HL2hi].
  destruct HL3 as [HL3lo HL3hi].
  all: try lia.
  all: try match goal with
       | H : u64_list_bounded ?values |- Znth ?index ?values 0 < U64_MOD =>
           apply H; lia
       | H : u64_list_bounded ?values |- 0 <= Znth ?index ?values 0 =>
           apply H; lia
       end.
  cbn; exact HL2lo.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_13_pure_split_goal_1 : sm2p_mong_mul_core_partial_solve_wit_13_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_13_pure_split_goal_2 : sm2p_mong_mul_core_partial_solve_wit_13_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_13_pure : sm2p_mong_mul_core_partial_solve_wit_13_pure.
Proof.
  unfold sm2p_mong_mul_core_partial_solve_wit_13_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Znth_replace_Znth_Diff by lia.
  entailer!.
  pose proof sm2_p_limbs as [HL0 [HL1 [HL2 [HL3 HP]]]].
  destruct HL0 as [HL0lo HL0hi].
  destruct HL1 as [HL1lo HL1hi].
  destruct HL2 as [HL2lo HL2hi].
  destruct HL3 as [HL3lo HL3hi].
  all: try lia.
  all: try match goal with
       | H : u64_list_bounded ?values |- Znth ?index ?values 0 < U64_MOD =>
           apply H; lia
       | H : u64_list_bounded ?values |- 0 <= Znth ?index ?values 0 =>
           apply H; lia
       end.
  cbn; exact HL3lo.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_17_pure_split_goal_1 : sm2p_mong_mul_core_partial_solve_wit_17_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_17_pure : sm2p_mong_mul_core_partial_solve_wit_17_pure.
Proof.
  unfold sm2p_mong_mul_core_partial_solve_wit_17_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Znth_replace_Znth_Diff by lia.
  entailer!.
  pose proof sm2_p_limbs as [HL0 [HL1 [HL2 [HL3 HP]]]].
  destruct HL0 as [HL0lo HL0hi].
  destruct HL1 as [HL1lo HL1hi].
  destruct HL2 as [HL2lo HL2hi].
  destruct HL3 as [HL3lo HL3hi].
  all: try lia.
  all: unfold unsigned_last_nbits.
  - change (0 <= (Z.lnot (Znth i xs 0) mod U64_MOD + 1) mod U64_MOD).
    exact (proj1 (Z.mod_pos_bound _ U64_MOD
      ltac:(unfold U64_MOD; lia))).
  - change ((Z.lnot (Znth i xs 0) mod U64_MOD + 1) mod U64_MOD < U64_MOD).
    exact (proj2 (Z.mod_pos_bound _ U64_MOD
      ltac:(unfold U64_MOD; lia))).
Qed. 

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_19_pure_split_goal_1 : sm2p_mong_mul_core_partial_solve_wit_19_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_19_pure : sm2p_mong_mul_core_partial_solve_wit_19_pure.
Proof.
  unfold sm2p_mong_mul_core_partial_solve_wit_19_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite Znth_replace_Znth_Diff by lia.
  entailer!.
  pose proof sm2_p_limbs as [HL0 [HL1 [HL2 [HL3 HP]]]].
  destruct HL0 as [HL0lo HL0hi].
  destruct HL1 as [HL1lo HL1hi].
  destruct HL2 as [HL2lo HL2hi].
  destruct HL3 as [HL3lo HL3hi].
  all: try lia.
  - unfold unsigned_last_nbits.
    change (0 <= (Znth i xs 0 - 1) mod U64_MOD).
    exact (proj1 (Z.mod_pos_bound _ U64_MOD
      ltac:(unfold U64_MOD; lia))).
  - unfold unsigned_last_nbits.
    change ((Znth i xs 0 - 1) mod U64_MOD < U64_MOD).
    exact (proj2 (Z.mod_pos_bound _ U64_MOD
      ltac:(unfold U64_MOD; lia))).
  - apply PreH31; lia.
  - apply PreH31; lia.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_23_pure_split_goal_1 : sm2p_mong_mul_core_partial_solve_wit_23_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_23_pure_split_goal_2 : sm2p_mong_mul_core_partial_solve_wit_23_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_23_pure : sm2p_mong_mul_core_partial_solve_wit_23_pure.
Proof.
  unfold sm2p_mong_mul_core_partial_solve_wit_23_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof sm2_p_limbs as [HL0 [HL1 [HL2 [HL3 HP]]]].
  destruct HL1 as [HL1lo HL1hi].
  entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_31_pure_split_goal_1 : sm2p_mong_mul_core_partial_solve_wit_31_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_31_pure : sm2p_mong_mul_core_partial_solve_wit_31_pure.
Proof.
  unfold sm2p_mong_mul_core_partial_solve_wit_31_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pures.
  all: dump_pre_spatial.
  all: try lia.
  all: try assumption.
  all: match goal with
  | |- context [unsigned_last_nbits ?x 64] =>
      pose proof (unsigned_Lastnbits_range x 64 ltac:(lia)) as [Hlo Hhi];
      first [exact Hlo |
        change (unsigned_last_nbits x 64 < 2 ^ 64); exact Hhi]
  end.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_37_pure_split_goal_1 : sm2p_mong_mul_core_partial_solve_wit_37_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_37_pure_split_goal_2 : sm2p_mong_mul_core_partial_solve_wit_37_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_37_pure : sm2p_mong_mul_core_partial_solve_wit_37_pure.
Proof.
  unfold sm2p_mong_mul_core_partial_solve_wit_37_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof sm2_p_limbs as [HL0 [HL1 [HL2 [HL3 HP]]]].
  entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_44_pure_split_goal_1 : sm2p_mong_mul_core_partial_solve_wit_44_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_44_pure_split_goal_2 : sm2p_mong_mul_core_partial_solve_wit_44_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2p_mong_mul_core_partial_solve_wit_44_pure : sm2p_mong_mul_core_partial_solve_wit_44_pure.
Proof.
  unfold sm2p_mong_mul_core_partial_solve_wit_44_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = 4) by lia.
  subst i.
  entailer!.
Qed. 

Lemma proof_of_sm2p_mong_mul_core_which_implies_wit_1 : sm2p_mong_mul_core_which_implies_wit_1.
Proof.
  unfold sm2p_mong_mul_core_which_implies_wit_1.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH6 4 ltac:(lia)) as H4.
  pose proof (PreH6 5 ltac:(lia)) as H5.
  pose proof (PreH6 6 ltac:(lia)) as H6.
  pose proof (PreH6 7 ltac:(lia)) as H7.
  pose proof (PreH6 8 ltac:(lia)) as H8.
  pose proof
    (u256_of_limbs_range
      (Znth 4 xs 0) (Znth 5 xs 0) (Znth 6 xs 0) (Znth 7 xs 0)
      H4 H5 H6 H7) as HX.
  assert (Hhead :
    sublist 0 4 xs =
      Znth 0 xs 0 :: Znth 1 xs 0 :: Znth 2 xs 0 ::
      Znth 3 xs 0 :: nil).
  {
    rewrite (sublist_split 0 4 1 xs) by lia.
    rewrite (sublist_split 1 4 2 xs) by lia.
    rewrite (sublist_split 2 4 3 xs) by lia.
    replace (sublist 0 1 xs) with (sublist 0 (0 + 1) xs)
      by (f_equal; lia).
    rewrite (sublist_single 0 0 xs) by lia.
    replace (sublist 1 2 xs) with (sublist 1 (1 + 1) xs)
      by (f_equal; lia).
    rewrite (sublist_single 0 1 xs) by lia.
    replace (sublist 2 3 xs) with (sublist 2 (2 + 1) xs)
      by (f_equal; lia).
    rewrite (sublist_single 0 2 xs) by lia.
    replace (sublist 3 4 xs) with (sublist 3 (3 + 1) xs)
      by (f_equal; lia).
    rewrite (sublist_single 0 3 xs) by lia.
    reflexivity.
  }
  assert (Htail :
    sublist 4 9 xs =
      Znth 4 xs 0 :: Znth 5 xs 0 :: Znth 6 xs 0 ::
      Znth 7 xs 0 :: Znth 8 xs 0 :: nil).
  {
    rewrite (sublist_split 4 9 5 xs) by lia.
    rewrite (sublist_split 5 9 6 xs) by lia.
    rewrite (sublist_split 6 9 7 xs) by lia.
    rewrite (sublist_split 7 9 8 xs) by lia.
    replace (sublist 4 5 xs) with (sublist 4 (4 + 1) xs)
      by (f_equal; lia).
    rewrite (sublist_single 0 4 xs) by lia.
    replace (sublist 5 6 xs) with (sublist 5 (5 + 1) xs)
      by (f_equal; lia).
    rewrite (sublist_single 0 5 xs) by lia.
    replace (sublist 6 7 xs) with (sublist 6 (6 + 1) xs)
      by (f_equal; lia).
    rewrite (sublist_single 0 6 xs) by lia.
    replace (sublist 7 8 xs) with (sublist 7 (7 + 1) xs)
      by (f_equal; lia).
    rewrite (sublist_single 0 7 xs) by lia.
    replace (sublist 8 9 xs) with (sublist 8 (8 + 1) xs)
      by (f_equal; lia).
    rewrite (sublist_single 0 8 xs) by lia.
    reflexivity.
  }
  assert (Hrepr :
    u64_list_value xs =
    (u256_of_limbs (Znth 4 xs 0) (Znth 5 xs 0)
       (Znth 6 xs 0) (Znth 7 xs 0) +
     Znth 8 xs 0 * U256_MOD) * U256_MOD).
  {
    unfold u64_list_value.
    pose proof
      (limb_list_value_split U64_MOD xs 4 ltac:(lia)) as Hsplit.
    rewrite PreH5 in Hsplit.
    rewrite Hhead, Htail in Hsplit.
    repeat rewrite limb_list_value_cons in Hsplit.
    rewrite limb_list_value_nil in Hsplit.
    pose proof (PreH7 0 ltac:(lia)) as H0.
    pose proof (PreH7 1 ltac:(lia)) as H1.
    pose proof (PreH7 2 ltac:(lia)) as H2.
    pose proof (PreH7 3 ltac:(lia)) as H3.
    unfold limb_radix, u256_of_limbs, U256_MOD, U64_MOD in *.
    nia.
  }
  destruct sm2_p_montgomery_bounds as [HP Hhalf].
  assert (HU256 : 0 < U256_MOD) by (cbv [U256_MOD]; lia).
  assert (Hsum :
    0 <= u256_of_limbs (Znth 4 xs 0) (Znth 5 xs 0)
           (Znth 6 xs 0) (Znth 7 xs 0) +
         Znth 8 xs 0 * U256_MOD <
    U256_MOD + SM2_P_Z).
  {
    unfold U512_MOD in PreH2.
    nia.
  }
  assert (HC : Znth 8 xs 0 <= 1) by nia.
  Exists (Znth 8 xs 0)
    (u256_of_limbs (Znth 4 xs 0) (Znth 5 xs 0)
       (Znth 6 xs 0) (Znth 7 xs 0)).
  entailer!.
  sep_apply
    (UInt64Array.full_split_to_full interim 4 9 xs ltac:(lia)).
  sep_apply
    (UInt64Array.full_to_full_shape
      interim 4 (sublist 0 4 xs)).
  rewrite Htail.
  cancel.
  unfold UInt64Array.full, store_array.
  cbn [store_array_rec].
  unfold store_u256_limbs.
  Exists (Znth 4 xs 0) (Znth 5 xs 0) (Znth 6 xs 0) (Znth 7 xs 0).
  entailer!.
  replace (0 + 1) with 1 by lia.
  replace (1 + 1) with 2 by lia.
  replace (2 + 1) with 3 by lia.
  replace (3 + 1) with 4 by lia.
  replace (interim + 4 * sizeof (UINT64) + 4 * sizeof (UINT64))
    with (interim + 8 * sizeof (UINT64)) by lia.
  entailer!.
Qed. 
