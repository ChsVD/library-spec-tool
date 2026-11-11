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
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import sm2n_mong_mul_core_goal.
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import sm2n_mong_mul_core_proof_auto.
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

Lemma proof_of_sm2n_mong_mul_core_entail_wit_4 : sm2n_mong_mul_core_entail_wit_4.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_4.
  left; intros.
  rename xs_2 into ys.
  rename PreH3 into Hlen.
  rename PreH2 into Hbounded.
  rename PreH1 into Hvalue.
  assert (Hlen9 : Zlength (ys ++ (0%Z :: nil)) = 9).
  {
    rewrite Zlength_app_cons.
    lia.
  }
  assert (Hbounded9 : u64_list_bounded (ys ++ (0%Z :: nil))).
  {
    unfold u64_list_bounded.
    intros j Hj.
    rewrite Zlength_app_cons in Hj.
    destruct (Z_lt_ge_dec j (Zlength ys)) as [Hlt | Hge].
    - rewrite app_Znth1 by lia.
      apply Hbounded.
      lia.
    - assert (Hjlen : j = Zlength ys) by lia.
      subst j.
      rewrite app_Znth2 by lia.
      replace (Zlength ys - Zlength ys) with 0 by lia.
      cbn.
      unfold U64_MOD.
      lia.
  }
  assert (Hzero : zero_prefix 0 (ys ++ (0%Z :: nil))).
  {
    unfold zero_prefix.
    intros j Hj.
    lia.
  }
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
    vm_compute.
    reflexivity.
  }
  Exists (ys ++ (0%Z :: nil)) 0.
  unfold store_sm2_n, store_sm2_neg_inv_n.
  entailer!.
  - assert (Hone :
      (interim_pre + 8 * sizeof (UINT64)) # UInt64 |-> 0 |--
      UInt64Array.full
        (interim_pre + 8 * sizeof (UINT64)) 1 (0%Z :: nil)).
    {
      unfold UInt64Array.full, store_array.
      cbn [store_array_rec].
      entailer!.
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
    Exists SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z.
    pose proof sm2_n_limbs as HN.
    unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    entailer!.
    sep_apply store_int_undef_store_int.
    entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_7_split_goal_1 : sm2n_mong_mul_core_entail_wit_7_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_7_split_goal_2 : sm2n_mong_mul_core_entail_wit_7_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_7_split_goal_3 : sm2n_mong_mul_core_entail_wit_7_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_7_split_goal_4 : sm2n_mong_mul_core_entail_wit_7_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_7_split_goal_5 : sm2n_mong_mul_core_entail_wit_7_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_7 : sm2n_mong_mul_core_entail_wit_7.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_7.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite replace_Znth_Znth in *.
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_1_split_goal_1 : sm2n_mong_mul_core_entail_wit_9_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_1_split_goal_2 : sm2n_mong_mul_core_entail_wit_9_1_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_1_split_goal_3 : sm2n_mong_mul_core_entail_wit_9_1_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_1_split_goal_4 : sm2n_mong_mul_core_entail_wit_9_1_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_1 : sm2n_mong_mul_core_entail_wit_9_1.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_9_1.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst j factor carry.
  replace (i + 0 + 0) with i in * by lia.
  repeat rewrite replace_Znth_Znth in *.
  change (Znth i ys 0 + SM2_N0_Z + 0 =
          out + retval * U64_MOD) in PreH7.
  set (zs := replace_Znth i out ys) in *.
  assert (Hout : out = 0).
  {
    eapply (sm2n_round_low_zero
      (Znth i ys 0) 1 h SM2_N0_Z 0 out retval).
    - exact PreH33.
    - ring.
    - lia.
    - lia.
  }
  assert (Hstep :
    u64_list_value zs + retval * U64_POW (i + 1) =
      u64_list_value ys + SM2_N0_Z * U64_POW i).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - rewrite PreH28. lia.
    - lia.
  }
  assert (Hzero : zero_prefix (i + 1) zs).
  {
    unfold zs.
    rewrite Hout.
    apply zero_prefix_replace_Znth_extend.
    - exact PreH34.
    - rewrite PreH28. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  split_pure_spatial.
  - unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    replace (0 + 1) with 1 by lia.
    replace (0 + 1 + 1) with 2 by lia.
    replace (0 + 1 + 1 + 1) with 3 by lia.
    entailer!.
    all: cbn; entailer!.
  - rewrite PreH35 in Hstep.
    replace (1 + i + 0) with (i + 1) by lia.
    entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_2_split_goal_1 : sm2n_mong_mul_core_entail_wit_9_2_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_2_split_goal_2 : sm2n_mong_mul_core_entail_wit_9_2_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_2_split_goal_3 : sm2n_mong_mul_core_entail_wit_9_2_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_2_split_goal_4 : sm2n_mong_mul_core_entail_wit_9_2_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_2 : sm2n_mong_mul_core_entail_wit_9_2.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_9_2.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst j factor carry.
  replace (i + 1 + 0) with (i + 1) in * by lia.
  repeat rewrite replace_Znth_Znth in *.
  change (Znth (i + 1) ys 0 + SM2_N1_Z + 0 =
          out + retval * U64_MOD) in PreH7.
  set (zs := replace_Znth (i + 1) out ys) in *.
  assert (Hstep :
    u64_list_value zs + retval * U64_POW (i + 1 + 1) =
      u64_list_value ys + SM2_N1_Z * U64_POW (i + 1)).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - rewrite PreH28. lia.
    - lia.
  }
  assert (Hzero : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact PreH33.
    - lia.
    - rewrite PreH28. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  split_pure_spatial.
  - unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    entailer!.
    all: cbn; entailer!.
  - rewrite PreH34 in Hstep.
    replace (1 + i + 1) with (i + 1 + 1) by lia.
    entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_3_split_goal_1 : sm2n_mong_mul_core_entail_wit_9_3_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_3_split_goal_2 : sm2n_mong_mul_core_entail_wit_9_3_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_3_split_goal_3 : sm2n_mong_mul_core_entail_wit_9_3_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_3_split_goal_4 : sm2n_mong_mul_core_entail_wit_9_3_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_3 : sm2n_mong_mul_core_entail_wit_9_3.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_9_3.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst j factor carry.
  replace (i + 2 + 0) with (i + 2) in * by lia.
  repeat rewrite replace_Znth_Znth in *.
  change (Znth (i + 2) ys 0 + SM2_N2_Z + 0 =
          out + retval * U64_MOD) in PreH7.
  set (zs := replace_Znth (i + 2) out ys) in *.
  assert (Hstep :
    u64_list_value zs + retval * U64_POW (i + 2 + 1) =
      u64_list_value ys + SM2_N2_Z * U64_POW (i + 2)).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - rewrite PreH28. lia.
    - lia.
  }
  assert (Hzero : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact PreH33.
    - lia.
    - rewrite PreH28. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  split_pure_spatial.
  - unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    entailer!.
    all: cbn; entailer!.
  - rewrite PreH34 in Hstep.
    replace (1 + i + 2) with (i + 2 + 1) by lia.
    entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_4_split_goal_1 : sm2n_mong_mul_core_entail_wit_9_4_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_4_split_goal_2 : sm2n_mong_mul_core_entail_wit_9_4_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_4_split_goal_3 : sm2n_mong_mul_core_entail_wit_9_4_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_4_split_goal_4 : sm2n_mong_mul_core_entail_wit_9_4_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_9_4 : sm2n_mong_mul_core_entail_wit_9_4.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_9_4.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst j factor carry.
  replace (i + 3 + 0) with (i + 3) in * by lia.
  repeat rewrite replace_Znth_Znth in *.
  change (Znth (i + 3) ys 0 + SM2_N3_Z + 0 =
          out + retval * U64_MOD) in PreH7.
  set (zs := replace_Znth (i + 3) out ys) in *.
  assert (Hstep :
    u64_list_value zs + retval * U64_POW (i + 3 + 1) =
      u64_list_value ys + SM2_N3_Z * U64_POW (i + 3)).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - rewrite PreH28. lia.
    - lia.
  }
  assert (Hzero : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact PreH33.
    - lia.
    - rewrite PreH28. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  assert (Hpow1 : U64_POW (i + 1) = U64_POW i * U64_MOD).
  {
    apply U64_POW_succ.
    lia.
  }
  assert (Hpow2 : U64_POW (i + 2) = U64_POW i * U64_MOD ^ 2).
  {
    replace (i + 2) with ((i + 1) + 1) by lia.
    rewrite U64_POW_succ by lia.
    rewrite Hpow1.
    ring.
  }
  assert (Hpow3 : U64_POW (i + 3) = U64_POW i * U64_MOD ^ 3).
  {
    replace (i + 3) with ((i + 2) + 1) by lia.
    rewrite U64_POW_succ by lia.
    rewrite Hpow2.
    ring.
  }
  assert (Hshift :
    SM2_N0_Z * U64_POW i +
      SM2_N1_Z * U64_POW (i + 1) +
      SM2_N2_Z * U64_POW (i + 2) +
      SM2_N3_Z * U64_POW (i + 3) =
    SM2_N_Z * U64_POW i).
  {
    rewrite Hpow1, Hpow2, Hpow3.
    unfold SM2_N_Z, u256_of_limbs.
    ring.
  }
  rewrite PreH34 in Hstep.
  assert (Hfinal :
    u64_list_value zs + retval * U64_POW (i + 3 + 1) =
      T + (K + U64_POW i) * SM2_N_Z).
  {
    nia.
  }
  split_pure_spatial.
  - unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    entailer!.
    all: cbn; entailer!.
  - replace (1 + i + 3) with (i + 3 + 1) by lia.
    entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_1_split_goal_1 : sm2n_mong_mul_core_entail_wit_10_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_1_split_goal_2 : sm2n_mong_mul_core_entail_wit_10_1_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_1_split_goal_3 : sm2n_mong_mul_core_entail_wit_10_1_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_1_split_goal_4 : sm2n_mong_mul_core_entail_wit_10_1_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_1_split_goal_5 : sm2n_mong_mul_core_entail_wit_10_1_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_1 : sm2n_mong_mul_core_entail_wit_10_1.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_10_1.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite replace_Znth_Znth in *.
  set (zs := replace_Znth pos out zs_2) in *.
  assert (Hstep :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      u64_list_value zs_2 + carry * U64_POW pos).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - rewrite PreH33. lia.
    - lia.
  }
  assert (Hzero : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact PreH35.
    - lia.
    - rewrite PreH33. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  assert (Hvalue :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      T + K * SM2_N_Z + SM2_N0_Z * U64_POW i) by lia.
  assert (Hrhs_lt :
    T + K * SM2_N_Z + SM2_N0_Z * U64_POW i < U576_MOD).
  {
    assert (Hi_cases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct Hi_cases as [-> | [-> | [-> | ->]]];
      cbv [U64_POW U64_MOD U576_MOD U256_MOD
           SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
           u256_of_limbs U32_MOD] in *;
      nia.
  }
  assert (Hnext : pos + 1 + retval <= 9).
  {
    destruct (Z.eq_dec pos 8) as [-> | Hpos].
    - replace (U64_POW (8 + 1)) with U576_MOD in Hvalue by reflexivity.
      nia.
    - lia.
  }
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_2_split_goal_1 : sm2n_mong_mul_core_entail_wit_10_2_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_2_split_goal_2 : sm2n_mong_mul_core_entail_wit_10_2_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_2_split_goal_3 : sm2n_mong_mul_core_entail_wit_10_2_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_2_split_goal_4 : sm2n_mong_mul_core_entail_wit_10_2_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_2_split_goal_5 : sm2n_mong_mul_core_entail_wit_10_2_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_2 : sm2n_mong_mul_core_entail_wit_10_2.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_10_2.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite replace_Znth_Znth in *.
  set (zs := replace_Znth pos out zs_2) in *.
  assert (Hstep :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      u64_list_value zs_2 + carry * U64_POW pos).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - rewrite PreH33. lia.
    - lia.
  }
  assert (Hzero : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact PreH35.
    - lia.
    - rewrite PreH33. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  assert (Hvalue :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      T + K * SM2_N_Z +
        SM2_N0_Z * U64_POW i +
        SM2_N1_Z * U64_POW (i + 1)) by lia.
  assert (Hrhs_lt :
    T + K * SM2_N_Z +
      SM2_N0_Z * U64_POW i +
      SM2_N1_Z * U64_POW (i + 1) < U576_MOD).
  {
    assert (Hi_cases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct Hi_cases as [-> | [-> | [-> | ->]]];
      cbv [U64_POW U64_MOD U576_MOD U256_MOD
           SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
           u256_of_limbs U32_MOD] in *;
      nia.
  }
  assert (Hnext : pos + 1 + retval <= 9).
  {
    destruct (Z.eq_dec pos 8) as [-> | Hpos].
    - replace (U64_POW (8 + 1)) with U576_MOD in Hvalue by reflexivity.
      nia.
    - lia.
  }
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_3_split_goal_1 : sm2n_mong_mul_core_entail_wit_10_3_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_3_split_goal_2 : sm2n_mong_mul_core_entail_wit_10_3_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_3_split_goal_3 : sm2n_mong_mul_core_entail_wit_10_3_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_3_split_goal_4 : sm2n_mong_mul_core_entail_wit_10_3_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_3_split_goal_5 : sm2n_mong_mul_core_entail_wit_10_3_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_3 : sm2n_mong_mul_core_entail_wit_10_3.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_10_3.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite replace_Znth_Znth in *.
  set (zs := replace_Znth pos out zs_2) in *.
  assert (Hstep :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      u64_list_value zs_2 + carry * U64_POW pos).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - rewrite PreH33. lia.
    - lia.
  }
  assert (Hzero : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact PreH35.
    - lia.
    - rewrite PreH33. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  assert (Hvalue :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      T + K * SM2_N_Z +
        SM2_N0_Z * U64_POW i +
        SM2_N1_Z * U64_POW (i + 1) +
        SM2_N2_Z * U64_POW (i + 2)) by lia.
  assert (Hrhs_lt :
    T + K * SM2_N_Z +
      SM2_N0_Z * U64_POW i +
      SM2_N1_Z * U64_POW (i + 1) +
      SM2_N2_Z * U64_POW (i + 2) < U576_MOD).
  {
    assert (Hi_cases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct Hi_cases as [-> | [-> | [-> | ->]]];
      cbv [U64_POW U64_MOD U576_MOD U256_MOD
           SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
           u256_of_limbs U32_MOD] in *;
      nia.
  }
  assert (Hnext : pos + 1 + retval <= 9).
  {
    destruct (Z.eq_dec pos 8) as [-> | Hpos].
    - replace (U64_POW (8 + 1)) with U576_MOD in Hvalue by reflexivity.
      nia.
    - lia.
  }
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_4_split_goal_1 : sm2n_mong_mul_core_entail_wit_10_4_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_4_split_goal_2 : sm2n_mong_mul_core_entail_wit_10_4_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_4_split_goal_3 : sm2n_mong_mul_core_entail_wit_10_4_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_4_split_goal_4 : sm2n_mong_mul_core_entail_wit_10_4_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_4_split_goal_5 : sm2n_mong_mul_core_entail_wit_10_4_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_10_4 : sm2n_mong_mul_core_entail_wit_10_4.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_10_4.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite replace_Znth_Znth in *.
  set (zs := replace_Znth pos out zs_2) in *.
  assert (Hstep :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      u64_list_value zs_2 + carry * U64_POW pos).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - rewrite PreH33. lia.
    - lia.
  }
  assert (Hzero : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact PreH35.
    - lia.
    - rewrite PreH33. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  assert (Hvalue :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      T + (K + U64_POW i) * SM2_N_Z) by lia.
  assert (Hrhs_lt :
    T + (K + U64_POW i) * SM2_N_Z < U576_MOD).
  {
    assert (Hi_cases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct Hi_cases as [-> | [-> | [-> | ->]]];
      cbv [U64_POW U64_MOD U576_MOD U256_MOD
           SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
           u256_of_limbs U32_MOD] in *;
      nia.
  }
  assert (Hnext : pos + 1 + retval <= 9).
  {
    destruct (Z.eq_dec pos 8) as [-> | Hpos].
    - replace (U64_POW (8 + 1)) with U576_MOD in Hvalue by reflexivity.
      nia.
    - lia.
  }
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_11_1_split_goal_1 : sm2n_mong_mul_core_entail_wit_11_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_11_1 : sm2n_mong_mul_core_entail_wit_11_1.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_11_1.
  right.
  intros.
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_11_2_split_goal_1 : sm2n_mong_mul_core_entail_wit_11_2_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_11_2 : sm2n_mong_mul_core_entail_wit_11_2.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_11_2.
  right.
  intros.
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_11_3_split_goal_1 : sm2n_mong_mul_core_entail_wit_11_3_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_11_3 : sm2n_mong_mul_core_entail_wit_11_3.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_11_3.
  right.
  intros.
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_11_4_split_goal_1 : sm2n_mong_mul_core_entail_wit_11_4_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_11_4 : sm2n_mong_mul_core_entail_wit_11_4.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_11_4.
  right.
  intros.
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_12_split_goal_1 : sm2n_mong_mul_core_entail_wit_12_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_12_split_goal_2 : sm2n_mong_mul_core_entail_wit_12_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_12_split_goal_3 : sm2n_mong_mul_core_entail_wit_12_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_12_split_goal_4 : sm2n_mong_mul_core_entail_wit_12_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_12_split_goal_5 : sm2n_mong_mul_core_entail_wit_12_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_12_split_goal_6 : sm2n_mong_mul_core_entail_wit_12_split_goal_6.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_12 : sm2n_mong_mul_core_entail_wit_12.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_12.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (i + 0) with i in * by lia.
  repeat rewrite replace_Znth_Znth in *.
  change (retval * SM2_N0_Z = retval_2 + hi * U64_MOD) in PreH31.
  set (ys := replace_Znth i out xs) in *.
  set (zs := replace_Znth (i + 1) out_2 ys) in *.
  assert (Hout : out = 0).
  {
    eapply (sm2n_round_low_zero
      (Znth i xs 0) retval hi_2 retval_2 hi out retval_4).
    - exact PreH38.
    - exact PreH31.
    - lia.
    - lia.
  }
  assert (Hstep0 :
    u64_list_value ys + retval_4 * U64_POW (i + 1) =
      u64_list_value xs + retval_2 * U64_POW i).
  {
    unfold u64_list_value, U64_POW, ys.
    eapply limb_list_value_carry_step.
    - rewrite PreH51. lia.
    - lia.
  }
  assert (Hstep1 :
    u64_list_value zs + retval_3 * U64_POW (i + 1 + 1) =
      u64_list_value ys + (hi + retval_4) * U64_POW (i + 1)).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - unfold ys. rewrite Zlength_replace_Znth, PreH51. lia.
    - lia.
  }
  replace (i + 1 + 1) with (i + 2) in Hstep1 by lia.
  assert (Hpow : U64_POW (i + 1) = U64_POW i * U64_MOD).
  {
    apply U64_POW_succ.
    lia.
  }
  assert (Hvalue :
    u64_list_value zs + retval_3 * U64_POW (i + 2) =
      T + K * SM2_N_Z + retval * SM2_N0_Z * U64_POW i).
  {
    rewrite Hstep1.
    replace
      (u64_list_value ys + (hi + retval_4) * U64_POW (i + 1))
      with
      ((u64_list_value ys + retval_4 * U64_POW (i + 1)) +
       hi * U64_POW (i + 1)) by ring.
    rewrite Hstep0, Hpow, PreH56.
    rewrite PreH31.
    ring.
  }
  assert (Hzero_y : zero_prefix (i + 1) ys).
  {
    unfold ys.
    rewrite Hout.
    apply zero_prefix_replace_Znth_extend.
    - exact PreH53.
    - rewrite PreH51. lia.
  }
  assert (Hzero_z : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact Hzero_y.
    - lia.
    - unfold ys. rewrite Zlength_replace_Znth, PreH51. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  assert (Htarget_nonneg :
    0 <= T + K * SM2_N_Z + retval * SM2_N0_Z * U64_POW i).
  {
    pose proof sm2_n_bounds.
    pose proof (U64_POW_nonneg i).
    cbv [SM2_N0_Z] in *.
    nia.
  }
  assert (Htarget_lt :
    T + K * SM2_N_Z + retval * SM2_N0_Z * U64_POW i < U576_MOD).
  {
    assert (Hi_cases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct Hi_cases as [-> | [-> | [-> | ->]]];
      cbv [U64_POW U64_MOD U576_MOD U256_MOD
           SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
           u256_of_limbs U32_MOD] in *;
      nia.
  }
  entailer!.
  all: try (replace (2 + i) with (i + 2) by lia; exact Hvalue).
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_13_split_goal_1 : sm2n_mong_mul_core_entail_wit_13_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_13_split_goal_2 : sm2n_mong_mul_core_entail_wit_13_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_13_split_goal_3 : sm2n_mong_mul_core_entail_wit_13_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_13_split_goal_4 : sm2n_mong_mul_core_entail_wit_13_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_13_split_goal_5 : sm2n_mong_mul_core_entail_wit_13_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_13 : sm2n_mong_mul_core_entail_wit_13.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_13.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite replace_Znth_Znth in *.
  set (zs := replace_Znth pos out ys_2) in *.
  assert (Hstep :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      u64_list_value ys_2 + carry * U64_POW pos).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - rewrite PreH36. lia.
    - lia.
  }
  assert (Hzero : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact PreH38.
    - lia.
    - rewrite PreH36. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  assert (Hvalue :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW i) by lia.
  assert (Hnext : pos + 1 + retval <= 9).
  {
    destruct (Z.eq_dec pos 8) as [-> | Hpos].
    - replace (U64_POW (8 + 1)) with U576_MOD in Hvalue by reflexivity.
      nia.
    - lia.
  }
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_14_split_goal_1 : sm2n_mong_mul_core_entail_wit_14_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_14_split_goal_2 : sm2n_mong_mul_core_entail_wit_14_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_14_split_goal_3 : sm2n_mong_mul_core_entail_wit_14_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_14_split_goal_4 : sm2n_mong_mul_core_entail_wit_14_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_14_split_goal_5 : sm2n_mong_mul_core_entail_wit_14_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_14_split_goal_6 : sm2n_mong_mul_core_entail_wit_14_split_goal_6.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_14_split_goal_7 : sm2n_mong_mul_core_entail_wit_14_split_goal_7.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_14_split_goal_8 : sm2n_mong_mul_core_entail_wit_14_split_goal_8.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_14 : sm2n_mong_mul_core_entail_wit_14.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_14.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst carry.
  repeat rewrite replace_Znth_Znth in *.
  set (ys := replace_Znth (i + 2) out ys_2) in *.
  set (zs := replace_Znth (i + 3) out_2 ys) in *.
  assert (Hu :
    unsigned_last_nbits
      (unsigned_last_nbits (Z.lnot factor) 64 + 1) 64 =
    U64_MOD - factor).
  {
    rewrite unsigned_lnot_u64 by lia.
    rewrite unsigned_last_nbits_eq.
    - lia.
    - unfold U64_MOD in *.
      lia.
  }
  assert (Hurange :
    0 <= unsigned_last_nbits
      (unsigned_last_nbits (Z.lnot factor) 64 + 1) 64 < U64_MOD)
    by (rewrite Hu; lia).
  assert (Hstep0 :
    u64_list_value ys + retval_2 * U64_POW (i + 2 + 1) =
      u64_list_value ys_2 +
        (U64_MOD - factor) * U64_POW (i + 2)).
  {
    unfold u64_list_value, U64_POW, ys.
    eapply limb_list_value_carry_step.
    - rewrite PreH48. lia.
    - rewrite Hu in PreH20.
      lia.
  }
  assert (Hstep1 :
    u64_list_value zs + retval * U64_POW (i + 3 + 1) =
      u64_list_value ys +
        (factor - 1 + retval_2) * U64_POW (i + 3)).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - unfold ys. rewrite Zlength_replace_Znth, PreH48. lia.
    - lia.
  }
  assert (Hpow : U64_POW (i + 3) = U64_POW (i + 2) * U64_MOD).
  {
    replace (i + 3) with ((i + 2) + 1) by lia.
    apply U64_POW_succ.
    lia.
  }
  assert (Hold :
    u64_list_value ys_2 =
      T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW i) by lia.
  assert (Hvalue :
    u64_list_value zs + retval * U64_POW (i + 4) =
      T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW i +
        factor * SM2_N2_Z * U64_POW (i + 2)).
  {
    replace (i + 4) with (i + 3 + 1) by lia.
    rewrite Hstep1.
    replace
      (u64_list_value ys +
       (factor - 1 + retval_2) * U64_POW (i + 3))
      with
      ((u64_list_value ys + retval_2 * U64_POW (i + 3)) +
       (factor - 1) * U64_POW (i + 3)) by ring.
    replace (i + 2 + 1) with (i + 3) in Hstep0 by lia.
    rewrite Hstep0, Hpow, Hold.
    unfold SM2_N2_Z.
    ring.
  }
  assert (Hzero_y : zero_prefix (i + 1) ys).
  {
    unfold ys.
    apply zero_prefix_replace_Znth_after.
    - exact PreH50.
    - lia.
    - rewrite PreH48. lia.
  }
  assert (Hzero_z : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact Hzero_y.
    - lia.
    - unfold ys. rewrite Zlength_replace_Znth, PreH48. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  assert (Htarget_nonneg :
    0 <= T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW i +
      factor * SM2_N2_Z * U64_POW (i + 2)).
  {
    destruct sm2_n_limbs as [HN0 [HN1 [HN2 HN3]]].
    pose proof sm2_n_bounds.
    pose proof (U64_POW_nonneg i).
    pose proof (U64_POW_nonneg (i + 2)).
    nia.
  }
  assert (Htarget_lt :
    T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW i +
      factor * SM2_N2_Z * U64_POW (i + 2) < U576_MOD).
  {
    assert (Hi_cases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct Hi_cases as [-> | [-> | [-> | ->]]];
      cbv [U64_POW U64_MOD U576_MOD U256_MOD
           SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
           u256_of_limbs U32_MOD] in *;
      nia.
  }
  entailer!.
  all: try (replace (4 + i) with (i + 4) by lia; exact Hvalue).
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_15_split_goal_1 : sm2n_mong_mul_core_entail_wit_15_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_15_split_goal_2 : sm2n_mong_mul_core_entail_wit_15_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_15_split_goal_3 : sm2n_mong_mul_core_entail_wit_15_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_15_split_goal_4 : sm2n_mong_mul_core_entail_wit_15_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_15_split_goal_5 : sm2n_mong_mul_core_entail_wit_15_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_15 : sm2n_mong_mul_core_entail_wit_15.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_15.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite replace_Znth_Znth in *.
  set (zs := replace_Znth pos out ys_2) in *.
  assert (Hstep :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      u64_list_value ys_2 + carry * U64_POW pos).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - rewrite PreH36. lia.
    - lia.
  }
  assert (Hzero : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact PreH38.
    - lia.
    - rewrite PreH36. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  assert (Hvalue :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW i +
        factor * SM2_N2_Z * U64_POW (i + 2)) by lia.
  assert (Hnext : pos + 1 + retval <= 9).
  {
    destruct (Z.eq_dec pos 8) as [-> | Hpos].
    - replace (U64_POW (8 + 1)) with U576_MOD in Hvalue by reflexivity.
      nia.
    - lia.
  }
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_17_split_goal_1 : sm2n_mong_mul_core_entail_wit_17_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_17_split_goal_2 : sm2n_mong_mul_core_entail_wit_17_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_17_split_goal_3 : sm2n_mong_mul_core_entail_wit_17_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_17_split_goal_4 : sm2n_mong_mul_core_entail_wit_17_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_17_split_goal_5 : sm2n_mong_mul_core_entail_wit_17_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_17_split_goal_6 : sm2n_mong_mul_core_entail_wit_17_split_goal_6.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_17 : sm2n_mong_mul_core_entail_wit_17.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_17.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst carry.
  repeat rewrite replace_Znth_Znth in *.
  change (factor * SM2_N1_Z = retval + hi * U64_MOD) in PreH31.
  set (ys := replace_Znth (i + 1) out ys_2) in *.
  set (zs := replace_Znth (i + 2) out_2 ys) in *.
  assert (Hstep0 :
    u64_list_value ys + retval_3 * U64_POW (i + 1 + 1) =
      u64_list_value ys_2 + retval * U64_POW (i + 1)).
  {
    unfold u64_list_value, U64_POW, ys.
    eapply limb_list_value_carry_step.
    - rewrite PreH53. lia.
    - lia.
  }
  assert (Hstep1 :
    u64_list_value zs + retval_2 * U64_POW (i + 2 + 1) =
      u64_list_value ys + (hi + retval_3) * U64_POW (i + 2)).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - unfold ys. rewrite Zlength_replace_Znth, PreH53. lia.
    - lia.
  }
  assert (Hpow : U64_POW (i + 2) = U64_POW (i + 1) * U64_MOD).
  {
    replace (i + 2) with ((i + 1) + 1) by lia.
    apply U64_POW_succ.
    lia.
  }
  assert (Hold :
    u64_list_value ys_2 =
      T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW i +
        factor * SM2_N2_Z * U64_POW (i + 2)) by lia.
  assert (Hvalue :
    u64_list_value zs + retval_2 * U64_POW (i + 3) =
      T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW i +
        factor * SM2_N2_Z * U64_POW (i + 2) +
        factor * SM2_N1_Z * U64_POW (i + 1)).
  {
    replace (i + 3) with (i + 2 + 1) by lia.
    rewrite Hstep1.
    replace
      (u64_list_value ys + (hi + retval_3) * U64_POW (i + 2))
      with
      ((u64_list_value ys + retval_3 * U64_POW (i + 2)) +
       hi * U64_POW (i + 2)) by ring.
    replace (i + 1 + 1) with (i + 2) in Hstep0 by lia.
    rewrite Hstep0, Hold, Hpow, PreH31.
    ring.
  }
  assert (Hzero_y : zero_prefix (i + 1) ys).
  {
    unfold ys.
    apply zero_prefix_replace_Znth_after.
    - exact PreH55.
    - lia.
    - rewrite PreH53. lia.
  }
  assert (Hzero_z : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact Hzero_y.
    - lia.
    - unfold ys. rewrite Zlength_replace_Znth, PreH53. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  assert (Htarget_nonneg :
    0 <= T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW i +
      factor * SM2_N2_Z * U64_POW (i + 2) +
      factor * SM2_N1_Z * U64_POW (i + 1)).
  {
    destruct sm2_n_limbs as [HN0 [HN1 [HN2 HN3]]].
    pose proof sm2_n_bounds.
    pose proof (U64_POW_nonneg i).
    pose proof (U64_POW_nonneg (i + 1)).
    pose proof (U64_POW_nonneg (i + 2)).
    nia.
  }
  assert (Htarget_lt :
    T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW i +
      factor * SM2_N2_Z * U64_POW (i + 2) +
      factor * SM2_N1_Z * U64_POW (i + 1) < U576_MOD).
  {
    assert (Hi_cases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct Hi_cases as [-> | [-> | [-> | ->]]];
      cbv [U64_POW U64_MOD U576_MOD U256_MOD
           SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
           u256_of_limbs U32_MOD] in *;
      nia.
  }
  entailer!.
  all: try (replace (3 + i) with (i + 3) by lia; exact Hvalue).
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_18_split_goal_1 : sm2n_mong_mul_core_entail_wit_18_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_18_split_goal_2 : sm2n_mong_mul_core_entail_wit_18_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_18_split_goal_3 : sm2n_mong_mul_core_entail_wit_18_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_18_split_goal_4 : sm2n_mong_mul_core_entail_wit_18_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_18_split_goal_5 : sm2n_mong_mul_core_entail_wit_18_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_18 : sm2n_mong_mul_core_entail_wit_18.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_18.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite replace_Znth_Znth in *.
  set (zs := replace_Znth pos out ys_2) in *.
  assert (Hstep :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      u64_list_value ys_2 + carry * U64_POW pos).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - rewrite PreH36. lia.
    - lia.
  }
  assert (Hzero : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact PreH38.
    - lia.
    - rewrite PreH36. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  assert (Hvalue :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW i +
        factor * SM2_N2_Z * U64_POW (i + 2) +
        factor * SM2_N1_Z * U64_POW (i + 1)) by lia.
  assert (Hnext : pos + 1 + retval <= 9).
  {
    destruct (Z.eq_dec pos 8) as [-> | Hpos].
    - replace (U64_POW (8 + 1)) with U576_MOD in Hvalue by reflexivity.
      nia.
    - lia.
  }
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_20_split_goal_1 : sm2n_mong_mul_core_entail_wit_20_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_20_split_goal_2 : sm2n_mong_mul_core_entail_wit_20_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_20_split_goal_3 : sm2n_mong_mul_core_entail_wit_20_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_20_split_goal_4 : sm2n_mong_mul_core_entail_wit_20_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_20_split_goal_5 : sm2n_mong_mul_core_entail_wit_20_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_20_split_goal_6 : sm2n_mong_mul_core_entail_wit_20_split_goal_6.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_20 : sm2n_mong_mul_core_entail_wit_20.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_20.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst carry.
  repeat rewrite replace_Znth_Znth in *.
  change (factor * SM2_N3_Z = retval + hi * U64_MOD) in PreH31.
  set (ys := replace_Znth (i + 3) out ys_2) in *.
  set (zs := replace_Znth (i + 4) out_2 ys) in *.
  assert (Hstep0 :
    u64_list_value ys + retval_3 * U64_POW (i + 3 + 1) =
      u64_list_value ys_2 + retval * U64_POW (i + 3)).
  {
    unfold u64_list_value, U64_POW, ys.
    eapply limb_list_value_carry_step.
    - rewrite PreH53. lia.
    - lia.
  }
  assert (Hstep1 :
    u64_list_value zs + retval_2 * U64_POW (i + 4 + 1) =
      u64_list_value ys + (hi + retval_3) * U64_POW (i + 4)).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - unfold ys. rewrite Zlength_replace_Znth, PreH53. lia.
    - lia.
  }
  assert (Hpow1 : U64_POW (i + 1) = U64_POW i * U64_MOD).
  {
    apply U64_POW_succ.
    lia.
  }
  assert (Hpow2 : U64_POW (i + 2) = U64_POW (i + 1) * U64_MOD).
  {
    replace (i + 2) with ((i + 1) + 1) by lia.
    apply U64_POW_succ.
    lia.
  }
  assert (Hpow3 : U64_POW (i + 3) = U64_POW (i + 2) * U64_MOD).
  {
    replace (i + 3) with ((i + 2) + 1) by lia.
    apply U64_POW_succ.
    lia.
  }
  assert (Hpow4 : U64_POW (i + 4) = U64_POW (i + 3) * U64_MOD).
  {
    replace (i + 4) with ((i + 3) + 1) by lia.
    apply U64_POW_succ.
    lia.
  }
  assert (Hold :
    u64_list_value ys_2 =
      T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW i +
        factor * SM2_N2_Z * U64_POW (i + 2) +
        factor * SM2_N1_Z * U64_POW (i + 1)) by lia.
  assert (Hstage :
    u64_list_value zs + retval_2 * U64_POW (i + 5) =
      T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW i +
        factor * SM2_N2_Z * U64_POW (i + 2) +
        factor * SM2_N1_Z * U64_POW (i + 1) +
        factor * SM2_N3_Z * U64_POW (i + 3)).
  {
    replace (i + 5) with (i + 4 + 1) by lia.
    rewrite Hstep1.
    replace
      (u64_list_value ys + (hi + retval_3) * U64_POW (i + 4))
      with
      ((u64_list_value ys + retval_3 * U64_POW (i + 4)) +
       hi * U64_POW (i + 4)) by ring.
    replace (i + 3 + 1) with (i + 4) in Hstep0 by lia.
    rewrite Hstep0, Hold, Hpow4, PreH31.
    ring.
  }
  assert (Hexpanded :
    T + (K + factor * U64_POW i) * SM2_N_Z =
      T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW i +
        factor * SM2_N2_Z * U64_POW (i + 2) +
        factor * SM2_N1_Z * U64_POW (i + 1) +
        factor * SM2_N3_Z * U64_POW (i + 3)).
  {
    rewrite Hpow3, Hpow2, Hpow1.
    unfold SM2_N_Z, u256_of_limbs.
    ring.
  }
  assert (Hvalue :
    u64_list_value zs + retval_2 * U64_POW (i + 5) =
      T + (K + factor * U64_POW i) * SM2_N_Z).
  {
    rewrite Hexpanded.
    exact Hstage.
  }
  assert (Hzero_y : zero_prefix (i + 1) ys).
  {
    unfold ys.
    apply zero_prefix_replace_Znth_after.
    - exact PreH55.
    - lia.
    - rewrite PreH53. lia.
  }
  assert (Hzero_z : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact Hzero_y.
    - lia.
    - unfold ys. rewrite Zlength_replace_Znth, PreH53. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  assert (Hq : 0 <= K + factor * U64_POW i < U256_MOD).
  {
    assert (Hsucc : U64_POW (i + 1) = U64_POW i * U64_MOD)
      by exact Hpow1.
    assert (Hpow_bound : U64_POW (i + 1) <= U256_MOD).
    {
      assert (Hi_cases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
      destruct Hi_cases as [-> | [-> | [-> | ->]]];
        cbv [U64_POW U64_MOD U256_MOD]; lia.
    }
    pose proof (U64_POW_nonneg i).
    nia.
  }
  assert (Htarget_nonneg :
    0 <= T + (K + factor * U64_POW i) * SM2_N_Z).
  {
    pose proof sm2_n_bounds.
    nia.
  }
  assert (Htarget_lt :
    T + (K + factor * U64_POW i) * SM2_N_Z < U576_MOD).
  {
    pose proof
      (sm2n_stage_value_bound_u4 T (K + factor * U64_POW i)
        (conj PreH34 PreH35) Hq) as Hb.
    change
      (T + (K + factor * U64_POW i) * SM2_N_Z < U576_MOD) in Hb.
    exact Hb.
  }
  entailer!.
  all: try (replace (5 + i) with (i + 5) by lia; exact Hvalue).
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_21_split_goal_1 : sm2n_mong_mul_core_entail_wit_21_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_21_split_goal_2 : sm2n_mong_mul_core_entail_wit_21_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_21_split_goal_3 : sm2n_mong_mul_core_entail_wit_21_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_21_split_goal_4 : sm2n_mong_mul_core_entail_wit_21_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_21_split_goal_5 : sm2n_mong_mul_core_entail_wit_21_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_21 : sm2n_mong_mul_core_entail_wit_21.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_21.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite replace_Znth_Znth in *.
  set (zs := replace_Znth pos out ys_2) in *.
  assert (Hstep :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      u64_list_value ys_2 + carry * U64_POW pos).
  {
    unfold u64_list_value, U64_POW, zs.
    eapply limb_list_value_carry_step.
    - rewrite PreH36. lia.
    - lia.
  }
  assert (Hzero : zero_prefix (i + 1) zs).
  {
    unfold zs.
    apply zero_prefix_replace_Znth_after.
    - exact PreH38.
    - lia.
    - rewrite PreH36. lia.
  }
  assert (Hrange : 0 <= u64_list_value zs < U576_MOD).
  {
    pose proof
      (limb_list_value_range U64_MOD zs ltac:(unfold U64_MOD; lia) PreH1)
      as Hr.
    change (0 <= u64_list_value zs < U576_MOD).
    change (0 <= limb_list_value U64_MOD zs < U576_MOD).
    rewrite PreH2 in Hr.
    exact Hr.
  }
  assert (Hvalue :
    u64_list_value zs + retval * U64_POW (pos + 1) =
      T + (K + factor * U64_POW i) * SM2_N_Z) by lia.
  assert (Hnext : pos + 1 + retval <= 9).
  {
    destruct (Z.eq_dec pos 8) as [-> | Hpos].
    - replace (U64_POW (8 + 1)) with U576_MOD in Hvalue by reflexivity.
      nia.
    - lia.
  }
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_22_1 : sm2n_mong_mul_core_entail_wit_22_1.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_22_1.
  LLM_pre_process ltac:(idtac).
  assert (Hpow : U64_POW (i + 1) = U64_POW i * U64_MOD).
  { apply U64_POW_succ. lia. }
  Exists ys (K_2 + factor * U64_POW i).
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_22_2 : sm2n_mong_mul_core_entail_wit_22_2.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_22_2.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hz : Znth i xs_2 0 = 0) by
    (unfold SM2_NEG_INV_N, U64_MOD in *; lia).
  repeat rewrite replace_Znth_Znth in *.
  assert (Hpow : U64_POW (i + 1) = U64_POW i * U64_MOD).
  { apply U64_POW_succ. lia. }
  Exists xs_2 K_2.
  entailer!.
  - unfold store_sm2_n, store_sm2_rhon, store_sm2_neg_inv_n,
      store_u256_limbs.
    Exists SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z.
    pose proof sm2_n_limbs as HN.
    unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    entailer!.
  - unfold zero_prefix in *.
    intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hne].
    + exact Hz.
    + apply PreH21.
      lia.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_22_3 : sm2n_mong_mul_core_entail_wit_22_3.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_22_3.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hpow : U64_POW (i + 1) = U64_POW i * U64_MOD).
  { apply U64_POW_succ. lia. }
  Exists ys (K_2 + U64_POW i).
  entailer!.
  - apply store_int_undef_store_int.
  - rewrite Hpow.
    unfold U64_MOD.
    nia.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_24_1_split_goal_1 : sm2n_mong_mul_core_entail_wit_24_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_24_1_split_goal_2 : sm2n_mong_mul_core_entail_wit_24_1_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_24_1 : sm2n_mong_mul_core_entail_wit_24_1.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_24_1.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof sm2_rhon_limbs as [Hrho Hrbounds].
  pose proof sm2_rhon_is_neg_n as Hneg.
  assert (HC : C = 1) by lia.
  assert (Hret : retval_2 = 0) by nia.
  Exists X C S.
  entailer!.
  - unfold store_sm2_rhon.
    rewrite (global_u32_v_addr_eq "SM2_rhoN").
    entailer!.
  - pose proof sm2_n_bounds as HNbound.
    assert (Hhalf : U256_MOD < 2 * SM2_N_Z).
    {
      cbv [SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
           u256_of_limbs U32_MOD U64_MOD U256_MOD].
      lia.
    }
    lia.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_24_2_split_goal_1 : sm2n_mong_mul_core_entail_wit_24_2_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_24_2_split_goal_2 : sm2n_mong_mul_core_entail_wit_24_2_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_entail_wit_24_2 : sm2n_mong_mul_core_entail_wit_24_2.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_24_2.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hhalf : U256_MOD < 2 * SM2_N_Z).
  {
    cbv [SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
         u256_of_limbs U32_MOD U64_MOD U256_MOD].
    lia.
  }
  Exists X C X.
  entailer!.
  unfold store_sm2_rhon.
  rewrite (global_u32_v_addr_eq "SM2_rhoN").
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_29_1 : sm2n_mong_mul_core_entail_wit_29_1.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_29_1.
  right; intros.
  pose proof sm2_rhon_limbs as [Hrho Hrbounds].
  pose proof sm2_rhon_is_neg_n as Hneg.
  assert (HNval :
    SM2_N_Z =
      u256_of_limbs SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z)
    by reflexivity.
  rewrite u64_list_value_four in PreH9.
  rewrite <- HNval in PreH9.
  assert (Hret3 : retval_3 = 1) by nia.
  assert (HS : S = Y - SM2_N_Z) by nia.
  Exists (K - Ckeep * U256_MOD - U256_MOD).
  rewrite u64_list_value_four.
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_entail_wit_29_2 : sm2n_mong_mul_core_entail_wit_29_2.
Proof.
  unfold sm2n_mong_mul_core_entail_wit_29_2.
  right; intros.
  Exists (K - Ckeep * U256_MOD).
  rewrite u64_list_value_four.
  entailer!.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_return_wit_1 : sm2n_mong_mul_core_return_wit_1.
Proof.
  unfold sm2n_mong_mul_core_return_wit_1.
  left. intros.
  Exists K2 Zout_2.
  unfold store_fn, store_mod.
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

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_2_pure_split_goal_1 : sm2n_mong_mul_core_partial_solve_wit_2_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_2_pure : sm2n_mong_mul_core_partial_solve_wit_2_pure.
Proof.
  unfold sm2n_mong_mul_core_partial_solve_wit_2_pure.
  right.
  intros.
  dump_pre_spatial.
  destruct sm2n_word_negative_inverse as [[Hlo Hhi] Hinv].
  exact Hhi.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_5_pure_split_goal_1 : sm2n_mong_mul_core_partial_solve_wit_5_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_5_pure_split_goal_2 : sm2n_mong_mul_core_partial_solve_wit_5_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_5_pure_split_goal_3 : sm2n_mong_mul_core_partial_solve_wit_5_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_5_pure_split_goal_4 : sm2n_mong_mul_core_partial_solve_wit_5_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_5_pure : sm2n_mong_mul_core_partial_solve_wit_5_pure.
Proof.
  unfold sm2n_mong_mul_core_partial_solve_wit_5_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  all: pose proof sm2_n_limbs as [HL0 [HL1 [HL2 HL3]]].
  - cbn. exact (proj1 HL0).
  - subst j. cbn. exact (proj2 HL0).
  - subst j. cbn. exact (proj1 HL0).
Qed. 

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_8_pure_split_goal_1 : sm2n_mong_mul_core_partial_solve_wit_8_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_8_pure_split_goal_2 : sm2n_mong_mul_core_partial_solve_wit_8_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_8_pure_split_goal_3 : sm2n_mong_mul_core_partial_solve_wit_8_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_8_pure_split_goal_4 : sm2n_mong_mul_core_partial_solve_wit_8_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_8_pure : sm2n_mong_mul_core_partial_solve_wit_8_pure.
Proof.
  unfold sm2n_mong_mul_core_partial_solve_wit_8_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  all: pose proof sm2_n_limbs as [HL0 [HL1 [HL2 HL3]]].
  - cbn. exact (proj1 HL1).
  - subst j. cbn. exact (proj2 HL1).
  - subst j. cbn. exact (proj1 HL1).
Qed. 

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_11_pure_split_goal_1 : sm2n_mong_mul_core_partial_solve_wit_11_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_11_pure_split_goal_2 : sm2n_mong_mul_core_partial_solve_wit_11_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_11_pure_split_goal_3 : sm2n_mong_mul_core_partial_solve_wit_11_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_11_pure_split_goal_4 : sm2n_mong_mul_core_partial_solve_wit_11_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_11_pure : sm2n_mong_mul_core_partial_solve_wit_11_pure.
Proof.
  unfold sm2n_mong_mul_core_partial_solve_wit_11_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  all: pose proof sm2_n_limbs as [HL0 [HL1 [HL2 HL3]]].
  - cbn. exact (proj1 HL2).
  - subst j. cbn. exact (proj2 HL2).
  - subst j. cbn. exact (proj1 HL2).
Qed. 

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_14_pure_split_goal_1 : sm2n_mong_mul_core_partial_solve_wit_14_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_14_pure_split_goal_2 : sm2n_mong_mul_core_partial_solve_wit_14_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_14_pure_split_goal_3 : sm2n_mong_mul_core_partial_solve_wit_14_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_14_pure_split_goal_4 : sm2n_mong_mul_core_partial_solve_wit_14_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_14_pure : sm2n_mong_mul_core_partial_solve_wit_14_pure.
Proof.
  unfold sm2n_mong_mul_core_partial_solve_wit_14_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  all: pose proof sm2_n_limbs as [HL0 [HL1 [HL2 HL3]]].
  - cbn. exact (proj1 HL3).
  - subst j. cbn. exact (proj2 HL3).
  - subst j. cbn. exact (proj1 HL3).
Qed. 

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_24_pure_split_goal_1 : sm2n_mong_mul_core_partial_solve_wit_24_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_24_pure_split_goal_2 : sm2n_mong_mul_core_partial_solve_wit_24_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_24_pure : sm2n_mong_mul_core_partial_solve_wit_24_pure.
Proof.
  unfold sm2n_mong_mul_core_partial_solve_wit_24_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  pose proof sm2_n_limbs as [HL0 [HL1 [HL2 HL3]]].
  cbn. exact (proj1 HL0).
Qed. 

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_32_pure_split_goal_1 : sm2n_mong_mul_core_partial_solve_wit_32_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_32_pure : sm2n_mong_mul_core_partial_solve_wit_32_pure.
Proof.
  unfold sm2n_mong_mul_core_partial_solve_wit_32_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  all: match goal with
  | |- context [unsigned_last_nbits ?x 64] =>
      pose proof (unsigned_Lastnbits_range x 64 ltac:(lia)) as Hrange
  end; fold U64_MOD in Hrange; lia.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_38_pure_split_goal_1 : sm2n_mong_mul_core_partial_solve_wit_38_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_38_pure_split_goal_2 : sm2n_mong_mul_core_partial_solve_wit_38_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_38_pure : sm2n_mong_mul_core_partial_solve_wit_38_pure.
Proof.
  unfold sm2n_mong_mul_core_partial_solve_wit_38_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  pose proof sm2_n_limbs as [HL0 [HL1 [HL2 HL3]]].
  cbn. exact (proj1 HL1).
Qed. 

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_46_pure_split_goal_1 : sm2n_mong_mul_core_partial_solve_wit_46_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_46_pure_split_goal_2 : sm2n_mong_mul_core_partial_solve_wit_46_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_46_pure : sm2n_mong_mul_core_partial_solve_wit_46_pure.
Proof.
  unfold sm2n_mong_mul_core_partial_solve_wit_46_pure.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  pose proof sm2_n_limbs as [HL0 [HL1 [HL2 HL3]]].
  cbn. exact (proj1 HL3).
Qed. 

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_53_pure_split_goal_1 : sm2n_mong_mul_core_partial_solve_wit_53_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_53_pure_split_goal_2 : sm2n_mong_mul_core_partial_solve_wit_53_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2n_mong_mul_core_partial_solve_wit_53_pure : sm2n_mong_mul_core_partial_solve_wit_53_pure.
Proof.
  unfold sm2n_mong_mul_core_partial_solve_wit_53_pure.
  right; intros.
  assert (Hi : i = 4) by lia.
  subst i.
  split_pures.
  - dump_pre_spatial.
    rewrite <- sm2n_montgomery_radix.
    exact PreH12.
  - dump_pre_spatial.
    exact PreH15.
Qed. 

Lemma proof_of_sm2n_mong_mul_core_which_implies_wit_1 : sm2n_mong_mul_core_which_implies_wit_1.
Proof.
  unfold sm2n_mong_mul_core_which_implies_wit_1.
  left; intros.
  unfold u64_list_bounded, limb_list_bounded in PreH6.
  pose proof (PreH6 4 ltac:(lia)) as H4.
  pose proof (PreH6 5 ltac:(lia)) as H5.
  pose proof (PreH6 6 ltac:(lia)) as H6.
  pose proof (PreH6 7 ltac:(lia)) as H7.
  pose proof (PreH6 8 ltac:(lia)) as H8.
  pose proof
    (u256_of_limbs_range
      (Znth 4 xs 0) (Znth 5 xs 0) (Znth 6 xs 0) (Znth 7 xs 0)
      H4 H5 H6 H7) as HX.
  assert (Hrepr :
    u64_list_value xs =
    (u256_of_limbs (Znth 4 xs 0) (Znth 5 xs 0)
       (Znth 6 xs 0) (Znth 7 xs 0) +
     Znth 8 xs 0 * U256_MOD) * U256_MOD).
  {
    unfold u64_list_value, limb_list_value.
    rewrite PreH5.
    change
      (@Sum.sum Z (fun i : Z => 0 <= i < 9)
        (ZRange.finite_Z_range 0 9)
        (fun i : Z => Znth i xs 0 * U64_MOD ^ i) =
       (u256_of_limbs (Znth 4 xs 0) (Znth 5 xs 0)
          (Znth 6 xs 0) (Znth 7 xs 0) +
        Znth 8 xs 0 * U256_MOD) * U256_MOD).
    repeat rewrite ZRange.sum_Z_range_cons by lia.
    rewrite ZRange.sum_Z_range_empty by lia.
    rewrite (PreH7 0 ltac:(lia)).
    cbn.
    rewrite (PreH7 1 ltac:(lia)).
    rewrite (PreH7 2 ltac:(lia)).
    rewrite (PreH7 3 ltac:(lia)).
    unfold u256_of_limbs.
    cbv [U64_MOD].
    ring.
  }
  pose proof sm2_n_bounds as HN.
  assert (HU256 : 0 < U256_MOD) by (cbv [U256_MOD]; lia).
  assert (Hsum :
    0 <= u256_of_limbs (Znth 4 xs 0) (Znth 5 xs 0)
           (Znth 6 xs 0) (Znth 7 xs 0) +
         Znth 8 xs 0 * U256_MOD <
    U256_MOD + SM2_N_Z).
  {
    nia.
  }
  assert (HC : Znth 8 xs 0 <= 1) by nia.
  Exists (Znth 8 xs 0)
    (u256_of_limbs (Znth 4 xs 0) (Znth 5 xs 0)
       (Znth 6 xs 0) (Znth 7 xs 0)).
  entailer!.
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
