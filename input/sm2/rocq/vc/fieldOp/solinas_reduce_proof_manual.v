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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import solinas_reduce_def.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import solinas_reduce_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import solinas_reduce_proof_auto.
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

Lemma proof_of_solinas_reduce_entail_wit_3_non_alias : solinas_reduce_entail_wit_3_non_alias.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof
    (solinas_mixed_high_decomposition
      words16 limbs8 T_non_alias
      PreH64 PreH65 PreH66 PreH31 PreH32 PreH33) as HTsplit.
  set (h8 := Znth 8 words16 0) in *.
  set (h9 := Znth 9 words16 0) in *.
  set (h10 := Znth 10 words16 0) in *.
  set (h11 := Znth 11 words16 0) in *.
  set (h12 := Znth 12 words16 0) in *.
  set (h13 := Znth 13 words16 0) in *.
  set (h14 := Znth 14 words16 0) in *.
  set (h15 := Znth 15 words16 0) in *.
  pose proof (PreH65 8 ltac:(lia)) as Hh8.
  pose proof (PreH65 9 ltac:(lia)) as Hh9.
  pose proof (PreH65 10 ltac:(lia)) as Hh10.
  pose proof (PreH65 11 ltac:(lia)) as Hh11.
  pose proof (PreH65 12 ltac:(lia)) as Hh12.
  pose proof (PreH65 13 ltac:(lia)) as Hh13.
  pose proof (PreH65 14 ltac:(lia)) as Hh14.
  pose proof (PreH65 15 ltac:(lia)) as Hh15.
  change (0 <= h8 < U32_MOD) in Hh8.
  change (0 <= h9 < U32_MOD) in Hh9.
  change (0 <= h10 < U32_MOD) in Hh10.
  change (0 <= h11 < U32_MOD) in Hh11.
  change (0 <= h12 < U32_MOD) in Hh12.
  change (0 <= h13 < U32_MOD) in Hh13.
  change (0 <= h14 < U32_MOD) in Hh14.
  change (0 <= h15 < U32_MOD) in Hh15.
  repeat multimatch type of PreH38 with
  | context [unsigned_last_nbits ?x 64] =>
      let Hx := fresh "Hsmall" in
      assert (Hx : 0 <= x < U64_MOD)
        by (unfold U32_MOD, U64_MOD in *; lia);
      rewrite (unsigned_last_nbits_u64_small x Hx) in PreH38;
      clear Hx
  end.
  repeat multimatch type of PreH43 with
  | context [unsigned_last_nbits ?x 64] =>
      let Hx := fresh "Hsmall" in
      assert (Hx : 0 <= x < U64_MOD)
        by (unfold U32_MOD, U64_MOD in *; lia);
      rewrite (unsigned_last_nbits_u64_small x Hx) in PreH43;
      clear Hx
  end.
  repeat multimatch type of PreH48 with
  | context [unsigned_last_nbits ?x 64] =>
      let Hx := fresh "Hsmall" in
      assert (Hx : 0 <= x < U64_MOD)
        by (unfold U32_MOD, U64_MOD in *; lia);
      rewrite (unsigned_last_nbits_u64_small x Hx) in PreH48;
      clear Hx
  end.
  repeat multimatch type of PreH53 with
  | context [unsigned_last_nbits ?x 64] =>
      let Hx := fresh "Hsmall" in
      assert (Hx : 0 <= x < U64_MOD)
        by (unfold U32_MOD, U64_MOD in *; lia);
      rewrite (unsigned_last_nbits_u64_small x Hx) in PreH53;
      clear Hx
  end.
  repeat multimatch type of PreH58 with
  | context [unsigned_last_nbits ?x 64] =>
      let Hx := fresh "Hsmall" in
      assert (Hx : 0 <= x < U64_MOD)
        by (unfold U32_MOD, U64_MOD in *; lia);
      rewrite (unsigned_last_nbits_u64_small x Hx) in PreH58;
      clear Hx
  end.
  repeat multimatch type of PreH63 with
  | context [unsigned_last_nbits ?x 64] =>
      let Hx := fresh "Hsmall" in
      assert (Hx : 0 <= x < U64_MOD)
        by (unfold U32_MOD, U64_MOD in *; lia);
      rewrite (unsigned_last_nbits_u64_small x Hx) in PreH63;
      clear Hx
  end.
  set (b0 :=
    h8 + h9 + h10 + h11 + h12 + 2 * h13 + 2 * h14 + 2 * h15).
  set (b1 :=
    h9 + h10 + h11 + h12 + h13 + 2 * h14 + 2 * h15).
  set (b3 := h8 + h11 + h12 + 2 * h13 + h14 + h15).
  set (b5 := h10 + h13 + h14 + 2 * h15).
  set (b7 :=
    h8 + h9 + h10 + h11 + 2 * h12 + 2 * h13 +
      2 * h14 + 3 * h15).
  assert (Hb1 : 0 <= b1 < U64_MOD)
    by (unfold b1, U32_MOD, U64_MOD in *; lia).
  assert (Hb3 : 0 <= b3 < U64_MOD)
    by (unfold b3, U32_MOD, U64_MOD in *; lia).
  assert (Hb5 : 0 <= b5 < U64_MOD)
    by (unfold b5, U32_MOD, U64_MOD in *; lia).
  assert (Hb7 : 0 <= b7 < U64_MOD)
    by (unfold b7, U32_MOD, U64_MOD in *; lia).
  replace
    (h14 + h15 + h13 + h12 + h11 + h8 + h13)
    with b3 in PreH63 by (unfold b3; lia).
  replace
    (h14 + h15 + h13 + h10 + h15)
    with b5 in PreH63 by (unfold b5; lia).
  replace
    (h14 + h15 + h13 + h10 + h15)
    with b5 in PreH58 by (unfold b5; lia).
  replace
    (h14 + h15 + h13 +
      (h14 + h15 + h13 + h12 + h11 + (h9 + h10) + h8))
    with b0 in PreH53 by (unfold b0; lia).
  replace
    (h14 + h15 +
      (h14 + h15 + h13 + h12 + h11 + (h9 + h10)))
    with b1 in PreH53 by (unfold b1; lia).
  replace
    (h14 + h15 +
      (h14 + h15 + h13 + h12 + h11 + (h9 + h10)))
    with b1 in PreH48 by (unfold b1; lia).
  replace
    (h14 + h15 + h13 + h12 + h11 + h8 + h13)
    with b3 in PreH48 by (unfold b3; lia).
  replace
    (h14 + h15 + h13 + h12 + h15 +
      (h14 + h15 + h13 + h12 + h11 + (h9 + h10) + h8))
    with b7 in PreH43 by (unfold b7; lia).
  replace
    (h14 + h15 + h13 + h12 + h15 +
      (h14 + h15 + h13 + h12 + h11 + (h9 + h10) + h8))
    with b7 in PreH38 by (unfold b7; lia).
  pose proof
    (u64_rshift_lor_add__u256_shift b3 b5 32 Hb3 ltac:(lia))
    as Hlor.
  replace (64 - 32) with 32 in Hlor by lia.
  rewrite Hlor in PreH63.
  pose proof
    (unsigned_last_nbits_shiftl_high__u256_shift
      b5 32 Hb5 ltac:(lia)) as Hsh5.
  replace (64 - 32) with 32 in Hsh5 by lia.
  rewrite Hsh5 in PreH63.
  pose proof
    (unsigned_last_nbits_shiftl_high__u256_shift
      b1 32 Hb1 ltac:(lia)) as Hsh1.
  replace (64 - 32) with 32 in Hsh1 by lia.
  rewrite Hsh1 in PreH53.
  pose proof
    (unsigned_last_nbits_shiftl_high__u256_shift
      b3 32 Hb3 ltac:(lia)) as Hsh3.
  replace (64 - 32) with 32 in Hsh3 by lia.
  rewrite Hsh3 in PreH48.
  pose proof
    (unsigned_last_nbits_shiftl_high__u256_shift
      b7 32 Hb7 ltac:(lia)) as Hsh7.
  replace (64 - 32) with 32 in Hsh7 by lia.
  rewrite Hsh7 in PreH43.
  assert (E2 :
    h9 + h12 + h13 + 2 * h14 + h15 +
      (mulx32_hi b3 + mulx32_lo b5 * U32_MOD) =
    out + retval_2 * U64_MOD).
  {
    unfold mulx32_hi, mulx32_lo, unsigned_last_nbits, U32_MOD.
    lia.
  }
  assert (E3 :
    h11 + h14 + h15 + mulx32_hi b5 + retval_2 =
    out_2 + retval_3 * U64_MOD).
  { unfold mulx32_hi. lia. }
  assert (E0 :
    b0 + mulx32_lo b1 * U32_MOD =
    out_3 + retval_4 * U64_MOD).
  {
    unfold mulx32_lo, unsigned_last_nbits, U32_MOD.
    lia.
  }
  assert (E1 :
    mulx32_hi b1 + mulx32_lo b3 * U32_MOD + retval_4 =
    out_4 + retval_5 * U64_MOD).
  {
    unfold mulx32_hi, mulx32_lo, unsigned_last_nbits, U32_MOD.
    lia.
  }
  assert (E3low :
    out_2 + mulx32_lo b7 * U32_MOD =
    out_5 + retval_6 * U64_MOD).
  {
    unfold mulx32_lo, unsigned_last_nbits, U32_MOD.
    lia.
  }
  assert (Eacc :
    mulx32_hi b7 + retval_6 =
    out_6 + retval_7 * U64_MOD).
  { unfold mulx32_hi. lia. }
  subst b0 b1 b3 b5 b7.
  pose proof
    (solinas_high_stage_from_carries
      h8 h9 h10 h11 h12 h13 h14 h15
      out_3 out_4 out out_2 out_5 out_6
      retval_2 retval_3 retval_4 retval_5 retval_6 retval_7
      Hh8 Hh9 Hh10 Hh11 Hh12 Hh13 Hh14 Hh15
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia)
      E2 E3 E0 E1 E3low Eacc) as Hstage.
  destruct Hstage as [Khigh [HSD [Hacc [Hminus Hhigh]]]].
  pose proof PreH11 as Hout_eq.
  unfold U64_MOD in Hout_eq.
  assert (Hretval9 : retval_9 = 0) by lia.
  assert (Hout7 : out_7 = out_6 + retval_8) by lia.
  assert (Hout7range : 0 <= out_7 <= 13) by lia.
  pose proof
    (solinas_payload_encoding out_7 Hout7range)
    as [Hpayload_range Hpayload_value].
  set (Pval :=
    u256_of_limbs
      out_7
      (unsigned_last_nbits
        (unsigned_last_nbits (Z.shiftl out_7 32) 64 - out_7) 64)
      0
      (unsigned_last_nbits (Z.shiftl out_7 32) 64)) in *.
  assert (HPval : Pval = out_7 * SM2_RHOP_Z).
  { symmetry. exact Hpayload_value. }
  pose proof
    (solinas_minus_expr_value
      h8 h9 h13 h14 Hh8 Hh9 Hh13 Hh14)
    as [Hminus_value Hminus_bound].
  set (M :=
    unsigned_last_nbits
      (unsigned_last_nbits
        (unsigned_last_nbits (h8 + h9) 64 + h13) 64 + h14) 64)
    in Hminus_value, Hminus_bound |- *.
  assert (HhighM :
    u256_of_limbs
      (h8 + h9 * U32_MOD)
      (h10 + h11 * U32_MOD)
      (h12 + h13 * U32_MOD)
      (h14 + h15 * U32_MOD) * U256_MOD =
    u256_of_limbs out_3 out_4 out out_5 +
      out_6 * U256_MOD - M * U64_MOD + Khigh * SM2_P_Z).
  {
    rewrite Hminus_value.
    rewrite <- Hhigh.
    unfold u256_of_limbs.
    ring.
  }
  repeat rewrite replace_Znth_Znth in PreH16.
  simpl in PreH16.
  assert (Hlowadd :
    u256_of_limbs
      (Znth 0 limbs8 0) (Znth 1 limbs8 0)
      (Znth 2 limbs8 0) (Znth 3 limbs8 0) +
    u256_of_limbs out_3 out_4 out out_5 =
    S + retval_8 * U256_MOD).
  {
    rewrite <- PreH16.
    unfold u64_list_value, u256_of_limbs.
    repeat rewrite limb_list_value_cons.
    rewrite limb_list_value_nil.
    ring.
  }
  change
    (u64_list_value
      (out_7 ::
       unsigned_last_nbits
         (unsigned_last_nbits (Z.shiftl out_7 32) 64 - out_7) 64 ::
       0 :: unsigned_last_nbits (Z.shiftl out_7 32) 64 :: nil) +
     S = S_2 + retval * U256_MOD) in PreH5.
  assert (Hpayload_list :
    u64_list_value
      (out_7 ::
       unsigned_last_nbits
         (unsigned_last_nbits (Z.shiftl out_7 32) 64 - out_7) 64 ::
       0 :: unsigned_last_nbits (Z.shiftl out_7 32) 64 :: nil) =
    Pval).
  {
    subst Pval.
    unfold u64_list_value, u256_of_limbs.
    repeat rewrite limb_list_value_cons.
    rewrite limb_list_value_nil.
    ring.
  }
  rewrite Hpayload_list in PreH5.
  pose proof
    (solinas_carry_normalized
      out_7 Pval S S_2 retval
      Hout7range ltac:(lia) ltac:(lia) ltac:(lia)
      HPval PreH5) as Hnormalized.
  pose proof
    (solinas_finish_normalized
      T_non_alias
      (u256_of_limbs
        (Znth 0 limbs8 0) (Znth 1 limbs8 0)
        (Znth 2 limbs8 0) (Znth 3 limbs8 0))
      (u256_of_limbs
        (h8 + h9 * U32_MOD)
        (h10 + h11 * U32_MOD)
        (h12 + h13 * U32_MOD)
        (h14 + h15 * U32_MOD))
      (u256_of_limbs out_3 out_4 out out_5)
      out_6 retval_8 M Khigh S out_7 Pval S_2
      HTsplit HhighM Hlowadd Hout7 HPval retval PreH5) as Hinvariant.
  Exists Pval (u256_of_limbs out_3 out_4 out out_5)
    (Khigh + out_7 + retval) S_2.
  clear - PreH1 PreH2 PreH3 PreH4 PreH31 PreH32 PreH33
    PreH70 PreH71 Hpayload_range Hminus_bound Hinvariant Hnormalized
    Hpayload_list.
  entailer!.
  assert (Hpayload_store :
    u64_list_value
      ((make_record_u32
        (out_7 ::
         unsigned_last_nbits
           (unsigned_last_nbits (Z.shiftl out_7 32) 64 - out_7) 64 ::
         0 :: unsigned_last_nbits (Z.shiftl out_7 32) 64 :: nil)).(u32_v)) =
      Pval).
  {
    change
      (u64_list_value
        (out_7 ::
         unsigned_last_nbits
           (unsigned_last_nbits (Z.shiftl out_7 32) 64 - out_7) 64 ::
         0 :: unsigned_last_nbits (Z.shiftl out_7 32) 64 :: nil) = Pval).
    exact Hpayload_list.
  }
  rewrite Hpayload_store.
  unfold store_u64_limbs.
  Exists limbs8.
  entailer!.
  repeat sep_apply store_uint64_undef_store_uint64.
  sep_apply store_ptr_undef_store_ptr.
  cancel.
Qed. 

Lemma proof_of_solinas_reduce_entail_wit_6_1_non_alias : solinas_reduce_entail_wit_6_1_non_alias.
Proof.
  LLM_pre_process ltac:(lia).
  assert (HC : C = 1) by lia.
  assert (Hretval : retval = 0).
  {
    clear - PreH1 PreH3 PreH4 PreH5 PreH7 PreH25 PreH49 PreH50 HC.
    rewrite HC in PreH49, PreH50.
    unfold U256_MOD in *.
    lia.
  }
  Exists Pred_2 SDred_2 Kred_2 S.
  unfold store_sm2_rhop.
  entailer!.
  rewrite <- PreH7.
  unfold store_u256, store_u256_limbs.
  Intros r0 r1 r2 r3.
  Exists x0_3 x1_3 x2_3 x3_3 x0 x1 x2 x3 r0 r1 r2 r3.
  entailer!.
  repeat rewrite <- global_u32_v_addr_eq.
  cancel.
  sep_apply store_uchar_undef_store_uchar.
  cancel.
Qed. 

Lemma proof_of_solinas_reduce_entail_wit_6_2_non_alias : solinas_reduce_entail_wit_6_2_non_alias.
Proof.
  LLM_pre_process ltac:(lia).
  Exists Pred_2 SDred_2 Kred_2 Sraw.
  entailer!.
  sep_apply store_uchar_undef_store_uchar.
  cancel.
Qed. 

Lemma proof_of_solinas_reduce_return_wit_1 : solinas_reduce_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hminus : 0 <= minus < U64_MOD).
  {
    clear - PreH71 PreH72.
    unfold SOLINAS_MINUS_MAX, U32_MOD, U64_MOD in *.
    lia.
  }
  pose proof
    (solinas_inverse_add_value
      x0_2 x1_2 x2_2 x3_2 minus out out_2 out_3
      retval retval_2 retval_3 Sred
      Hminus PreH49 PreH39 PreH34 PreH29) as Hraw.
  pose proof
    (solinas_minus_product_bound minus PreH71 PreH72) as HminusP.
  pose proof sm2_p_limbs as [_ [_ [_ [_ Hp]]]].
  pose proof sm2_rhop_limbs as [_ [_ [_ [_ Hrho]]]].
  assert (Hborrow : borrow = 0).
  {
    clear - Hraw PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
      HminusP PreH69 PreH70.
    subst retval_3.
    unfold SM2_RHOP_Z in PreH16.
    cbv [U256_MOD] in *.
    lia.
  }
  assert (HS : S = Sred - minus * U64_MOD + SM2_P_Z).
  {
    clear - Hraw PreH14 PreH15 PreH16 Hborrow.
    subst borrow retval_3.
    unfold SM2_RHOP_Z in PreH16.
    cbv [U256_MOD] in *.
    lia.
  }
  destruct sm2_p_montgomery_bounds as [[HPpos HPbound] HPhalf].
  assert (Hcarry : retval_5 = 1).
  {
    clear - PreH1 PreH2 PreH3 PreH4 PreH5 PreH9 PreH11
      PreH16 Hp HPhalf.
    rewrite u64_list_value_four in PreH9.
    rewrite <- Hp in PreH9.
    unfold SM2_RHOP_Z in PreH16.
    cbv [U256_MOD] in *.
    lia.
  }
  assert (Hresult : S_2 = Sred - minus * U64_MOD).
  {
    clear - HS PreH5 PreH16 Hcarry.
    subst retval_5.
    unfold SM2_RHOP_Z in PreH16.
    cbv [U256_MOD] in *.
    lia.
  }
  assert (Hcanonical : 0 <= S_2 < SM2_P_Z).
  {
    clear - PreH1 PreH11 HS Hresult HPhalf.
    cbv [U256_MOD] in *.
    lia.
  }
  Exists Kred S_2.
  unfold store_fp, store_mod, store_sm2_p, store_sm2_rhop.
  rewrite u64_list_value_four in *.
  assert (HT : T_non_alias = S_2 + Kred * SM2_P_Z)
    by (clear - PreH73 Hresult; lia).
  clear - Hcanonical HT Hp PreH16.
  unfold store_u256.
  entailer!.
  rewrite (global_u32_v_addr_eq "SM2_P").
  rewrite (global_u32_v_addr_eq "SM2_rhoP").
  rewrite Hp.
  rewrite PreH16.
  cancel.
Qed. 

Lemma proof_of_solinas_reduce_return_wit_2 : solinas_reduce_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hminus : 0 <= minus < U64_MOD).
  {
    clear - PreH66 PreH67.
    unfold SOLINAS_MINUS_MAX, U32_MOD, U64_MOD in *.
    lia.
  }
  pose proof
    (solinas_inverse_add_value
      x0_2 x1_2 x2_2 x3_2 minus out out_2 out_3
      retval retval_2 retval_3 Sred
      Hminus PreH44 PreH34 PreH29 PreH24) as Hraw.
  assert (Hretval3 : retval_3 = 1)
    by (clear - PreH10 PreH22 PreH23; lia).
  pose proof sm2_p_limbs as [_ [_ [_ [_ Hp]]]].
  destruct sm2_p_montgomery_bounds as [[HPpos HPbound] HPhalf].
  assert (Hcarry : retval_5 = 1).
  {
    clear - PreH1 PreH2 PreH3 PreH4 PreH5 PreH9 PreH11
      PreH64 PreH65 PreH66 Hraw Hretval3 Hp HPpos HPbound.
    rewrite u64_list_value_four in PreH9.
    rewrite <- Hp in PreH9.
    subst retval_3.
    unfold SM2_RHOP_Z in PreH11.
    cbv [U256_MOD] in *.
    lia.
  }
  assert (Hresult : S = Sred - minus * U64_MOD - SM2_P_Z).
  {
    clear - PreH5 PreH11 Hraw Hretval3 Hcarry.
    subst retval_3 retval_5.
    unfold SM2_RHOP_Z in PreH11.
    cbv [U256_MOD] in *.
    lia.
  }
  assert (Hcanonical : 0 <= S < SM2_P_Z).
  {
    clear - PreH1 PreH64 PreH65 PreH66 Hresult HPhalf.
    cbv [U256_MOD] in *.
    unfold U64_MOD in *.
    lia.
  }
  Exists (Kred + 1) S.
  unfold store_fp, store_mod, store_sm2_p, store_sm2_rhop.
  rewrite u64_list_value_four in *.
  assert (HT : T_non_alias = S + (Kred + 1) * SM2_P_Z)
    by (clear - PreH68 Hresult; lia).
  clear - Hcanonical HT Hp PreH11.
  unfold store_u256.
  entailer!.
  rewrite (global_u32_v_addr_eq "SM2_P").
  rewrite (global_u32_v_addr_eq "SM2_rhoP").
  rewrite Hp.
  rewrite PreH11.
  cancel.
Qed. 

Lemma proof_of_solinas_reduce_return_wit_3 : solinas_reduce_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hminus : 0 <= minus < U64_MOD).
  {
    clear - PreH66 PreH67.
    unfold SOLINAS_MINUS_MAX, U32_MOD, U64_MOD in *.
    lia.
  }
  pose proof
    (solinas_inverse_add_value
      x0_2 x1_2 x2_2 x3_2 minus out out_2 out_3
      retval retval_2 retval_3 Sred
      Hminus PreH44 PreH34 PreH29 PreH24) as Hraw.
  pose proof
    (solinas_minus_product_bound minus PreH66 PreH67) as HminusP.
  pose proof sm2_p_limbs as [_ [_ [_ [_ Hp]]]].
  assert (Hborrow : borrow = 0).
  {
    clear - Hraw PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      HminusP PreH64 PreH65.
    subst retval_3.
    unfold SM2_RHOP_Z in PreH11.
    cbv [U256_MOD] in *.
    lia.
  }
  assert (HS : S = Sred - minus * U64_MOD + SM2_P_Z).
  {
    clear - Hraw PreH9 PreH10 PreH11 Hborrow.
    subst borrow retval_3.
    unfold SM2_RHOP_Z in PreH11.
    cbv [U256_MOD] in *.
    lia.
  }
  assert (Hcanonical : 0 <= S < SM2_P_Z).
  {
    clear - PreH4 PreH5 Hp.
    rewrite u64_list_value_four in PreH4.
    rewrite <- Hp in PreH4.
    lia.
  }
  Exists (Kred - 1) S.
  unfold store_fp, store_mod, store_sm2_p, store_sm2_rhop.
  rewrite u64_list_value_four in *.
  assert (HT : T_non_alias = S + (Kred - 1) * SM2_P_Z)
    by (clear - PreH68 HS; lia).
  clear - Hcanonical HT Hp PreH11.
  unfold store_u256.
  entailer!.
  rewrite (global_u32_v_addr_eq "SM2_P").
  rewrite (global_u32_v_addr_eq "SM2_rhoP").
  rewrite Hp.
  rewrite PreH11.
  cancel.
Qed. 

Lemma proof_of_solinas_reduce_return_wit_4 : solinas_reduce_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hminus : 0 <= minus < U64_MOD).
  {
    clear - PreH61 PreH62.
    unfold SOLINAS_MINUS_MAX, U32_MOD, U64_MOD in *.
    lia.
  }
  pose proof
    (solinas_inverse_add_value
      x0_2 x1_2 x2_2 x3_2 minus out out_2 out_3
      retval retval_2 retval_3 Sred
      Hminus PreH39 PreH29 PreH24 PreH19) as Hraw.
  assert (Hretval3 : retval_3 = 1)
    by (clear - PreH5 PreH17 PreH18; lia).
  pose proof
    (u256_of_limbs_range x0_2 out out_2 out_3
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hrange.
  assert (Hresult :
    u256_of_limbs x0_2 out out_2 out_3 =
      Sred - minus * U64_MOD).
  {
    clear - Hraw Hretval3.
    subst retval_3.
    lia.
  }
  pose proof sm2_p_limbs as [_ [_ [_ [_ Hp]]]].
  assert (Hcanonical :
    0 <= u256_of_limbs x0_2 out out_2 out_3 < SM2_P_Z).
  {
    clear - Hrange PreH4 Hp.
    rewrite u64_list_value_four in PreH4.
    rewrite <- Hp in PreH4.
    lia.
  }
  Exists Kred (u256_of_limbs x0_2 out out_2 out_3).
  unfold store_fp, store_mod, store_sm2_p, store_sm2_rhop.
  rewrite u64_list_value_four in *.
  assert (HT :
    T_non_alias =
      u256_of_limbs x0_2 out out_2 out_3 + Kred * SM2_P_Z)
    by (clear - PreH63 Hresult; lia).
  unfold store_u256.
  clear - Hcanonical HT Hp PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    PreH12 PreH13 PreH14.
  entailer!.
  rewrite (global_u32_v_addr_eq "SM2_P").
  rewrite Hp.
  cancel.
  unfold store_u256_limbs.
  Exists x0_4 x1_4 x2_4 x3_4.
  entailer!.
Qed. 

Lemma proof_of_solinas_reduce_partial_solve_wit_21_non_alias_pure_split_goal_1 : solinas_reduce_partial_solve_wit_21_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_21_non_alias_pure_split_goal_2 : solinas_reduce_partial_solve_wit_21_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_21_non_alias_pure_split_goal_3 : solinas_reduce_partial_solve_wit_21_non_alias_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_21_non_alias_pure : solinas_reduce_partial_solve_wit_21_non_alias_pure.
Proof.
  aggressive_pre_process.
  all: solve_u64_bit_range.
Qed. 

Lemma proof_of_solinas_reduce_partial_solve_wit_22_non_alias_pure_split_goal_1 : solinas_reduce_partial_solve_wit_22_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_22_non_alias_pure_split_goal_2 : solinas_reduce_partial_solve_wit_22_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_22_non_alias_pure_split_goal_3 : solinas_reduce_partial_solve_wit_22_non_alias_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_22_non_alias_pure : solinas_reduce_partial_solve_wit_22_non_alias_pure.
Proof.
  aggressive_pre_process.
  all: solve_u64_bit_range.
Qed. 

Lemma proof_of_solinas_reduce_partial_solve_wit_26_non_alias_pure_split_goal_1 : solinas_reduce_partial_solve_wit_26_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_26_non_alias_pure_split_goal_2 : solinas_reduce_partial_solve_wit_26_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_26_non_alias_pure_split_goal_3 : solinas_reduce_partial_solve_wit_26_non_alias_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_26_non_alias_pure : solinas_reduce_partial_solve_wit_26_non_alias_pure.
Proof.
  aggressive_pre_process.
  all: solve_u64_bit_range.
Qed. 

Lemma proof_of_solinas_reduce_partial_solve_wit_27_non_alias_pure_split_goal_1 : solinas_reduce_partial_solve_wit_27_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_27_non_alias_pure_split_goal_2 : solinas_reduce_partial_solve_wit_27_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_27_non_alias_pure_split_goal_3 : solinas_reduce_partial_solve_wit_27_non_alias_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_27_non_alias_pure_split_goal_4 : solinas_reduce_partial_solve_wit_27_non_alias_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_27_non_alias_pure : solinas_reduce_partial_solve_wit_27_non_alias_pure.
Proof.
  aggressive_pre_process.
  all: solve_u64_bit_range.
Qed. 

Lemma proof_of_solinas_reduce_partial_solve_wit_28_non_alias_pure_split_goal_1 : solinas_reduce_partial_solve_wit_28_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_28_non_alias_pure_split_goal_2 : solinas_reduce_partial_solve_wit_28_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_28_non_alias_pure : solinas_reduce_partial_solve_wit_28_non_alias_pure.
Proof.
  aggressive_pre_process.
  all: solve_u64_bit_range.
Qed. 

Lemma proof_of_solinas_reduce_partial_solve_wit_29_non_alias_pure_split_goal_1 : solinas_reduce_partial_solve_wit_29_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_29_non_alias_pure_split_goal_2 : solinas_reduce_partial_solve_wit_29_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_29_non_alias_pure : solinas_reduce_partial_solve_wit_29_non_alias_pure.
Proof.
  aggressive_pre_process.
  all: solve_u64_bit_range.
Qed. 

Lemma proof_of_solinas_reduce_partial_solve_wit_40_pure_split_goal_1 : solinas_reduce_partial_solve_wit_40_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_40_pure_split_goal_2 : solinas_reduce_partial_solve_wit_40_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_40_pure : solinas_reduce_partial_solve_wit_40_pure.
Proof.
  aggressive_pre_process.
  all: pose proof
         (unsigned_Lastnbits_range (Z.lnot minus) 64 ltac:(lia)) as Hrange;
       change
         (0 <= unsigned_last_nbits (Z.lnot minus) 64 < U64_MOD)
         in Hrange;
       entailer!.
Qed. 

Lemma proof_of_solinas_reduce_partial_solve_wit_41_pure_split_goal_1 : solinas_reduce_partial_solve_wit_41_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_41_pure : solinas_reduce_partial_solve_wit_41_pure.
Proof.
  aggressive_pre_process.
  unfold U64_MOD.
  entailer!.
Qed. 

Lemma proof_of_solinas_reduce_partial_solve_wit_42_pure_split_goal_1 : solinas_reduce_partial_solve_wit_42_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_solinas_reduce_partial_solve_wit_42_pure : solinas_reduce_partial_solve_wit_42_pure.
Proof.
  aggressive_pre_process.
  clear - PreH1.
  unfold U64_MOD.
  entailer!.
Qed. 

Lemma proof_of_solinas_reduce_which_implies_wit_1 : solinas_reduce_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename T_non_alias into T.
  unfold store_u64_limbs.
  Intros xs.
  destruct H as [Hlen [Hbounded Hvalue]].
  destruct xs as [|x0 xs]; [cbn in Hlen; lia|].
  destruct xs as [|x1 xs];
    [rewrite Zlength_cons, Zlength_nil in Hlen; lia|].
  destruct xs as [|x2 xs];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct xs as [|x3 xs];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct xs as [|x4 xs];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct xs as [|x5 xs];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct xs as [|x6 xs];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct xs as [|x7 xs];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct xs as [|x8 xs].
  - unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    unfold u64_list_bounded in Hbounded.
    pose proof (Hbounded 0 ltac:(cbn [Zlength]; lia)) as Hx0.
    pose proof (Hbounded 1 ltac:(cbn [Zlength]; lia)) as Hx1.
    pose proof (Hbounded 2 ltac:(cbn [Zlength]; lia)) as Hx2.
    pose proof (Hbounded 3 ltac:(cbn [Zlength]; lia)) as Hx3.
    pose proof (Hbounded 4 ltac:(cbn [Zlength]; lia)) as Hx4.
    pose proof (Hbounded 5 ltac:(cbn [Zlength]; lia)) as Hx5.
    pose proof (Hbounded 6 ltac:(cbn [Zlength]; lia)) as Hx6.
    pose proof (Hbounded 7 ltac:(cbn [Zlength]; lia)) as Hx7.
    change (0 <= x0 < U64_MOD) in Hx0.
    change (0 <= x1 < U64_MOD) in Hx1.
    change (0 <= x2 < U64_MOD) in Hx2.
    change (0 <= x3 < U64_MOD) in Hx3.
    change (0 <= x4 < U64_MOD) in Hx4.
    change (0 <= x5 < U64_MOD) in Hx5.
    change (0 <= x6 < U64_MOD) in Hx6.
    change (0 <= x7 < U64_MOD) in Hx7.
    Intros.
    sep_apply_l_atomic
      (store_uint64_store_uint
        (input + 0 * sizeof(UINT64)) x0);
      Intros w0 w1.
    sep_apply_l_atomic
      (store_uint64_store_uint
        (input + (0 + 1) * sizeof(UINT64)) x1);
      Intros w2 w3.
    sep_apply_l_atomic
      (store_uint64_store_uint
        (input + (0 + 1 + 1) * sizeof(UINT64)) x2);
      Intros w4 w5.
    sep_apply_l_atomic
      (store_uint64_store_uint
        (input + (0 + 1 + 1 + 1) * sizeof(UINT64)) x3);
      Intros w6 w7.
    sep_apply_l_atomic
      (store_uint64_store_uint
        (input + (0 + 1 + 1 + 1 + 1) * sizeof(UINT64)) x4);
      Intros w8 w9.
    sep_apply_l_atomic
      (store_uint64_store_uint
        (input + (0 + 1 + 1 + 1 + 1 + 1) * sizeof(UINT64)) x5);
      Intros w10 w11.
    sep_apply_l_atomic
      (store_uint64_store_uint
        (input + (0 + 1 + 1 + 1 + 1 + 1 + 1) *
          sizeof(UINT64)) x6);
      Intros w12 w13.
    sep_apply_l_atomic
      (store_uint64_store_uint
        (input + (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) *
          sizeof(UINT64)) x7);
      Intros w14 w15.
    prop_apply_p
      (store_uint_u32_range
        (input + 0 * sizeof(UINT64)) w0); Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + 0 * sizeof(UINT64) + 4) w1); Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + (0 + 1) * sizeof(UINT64)) w2); Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + (0 + 1) * sizeof(UINT64) + 4) w3); Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + (0 + 1 + 1) * sizeof(UINT64)) w4); Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + (0 + 1 + 1) * sizeof(UINT64) + 4) w5); Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + (0 + 1 + 1 + 1) * sizeof(UINT64)) w6); Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + (0 + 1 + 1 + 1) * sizeof(UINT64) + 4) w7); Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + (0 + 1 + 1 + 1 + 1) * sizeof(UINT64)) w8); Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + (0 + 1 + 1 + 1 + 1) * sizeof(UINT64) + 4) w9);
      Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + (0 + 1 + 1 + 1 + 1 + 1) * sizeof(UINT64)) w10);
      Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + (0 + 1 + 1 + 1 + 1 + 1) * sizeof(UINT64) + 4)
        w11);
      Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + (0 + 1 + 1 + 1 + 1 + 1 + 1) *
          sizeof(UINT64)) w12);
      Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + (0 + 1 + 1 + 1 + 1 + 1 + 1) *
          sizeof(UINT64) + 4) w13);
      Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) *
          sizeof(UINT64)) w14);
      Intros.
    prop_apply_p
      (store_uint_u32_range
        (input + (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) *
          sizeof(UINT64) + 4) w15);
      Intros.
    pose proof
      (merge_int64_by_ints_value w0 w1 x0 H9 H10 Hx0 (proj1 H1))
      as Ex0.
    pose proof
      (merge_int64_by_ints_value w2 w3 x1 H11 H12 Hx1 (proj1 H2))
      as Ex1.
    pose proof
      (merge_int64_by_ints_value w4 w5 x2 H13 H14 Hx2 (proj1 H3))
      as Ex2.
    pose proof
      (merge_int64_by_ints_value w6 w7 x3 H15 H16 Hx3 (proj1 H4))
      as Ex3.
    pose proof
      (merge_int64_by_ints_value w8 w9 x4 H17 H18 Hx4 (proj1 H5))
      as Ex4.
    pose proof
      (merge_int64_by_ints_value w10 w11 x5 H19 H20 Hx5 (proj1 H6))
      as Ex5.
    pose proof
      (merge_int64_by_ints_value w12 w13 x6 H21 H22 Hx6 (proj1 H7))
      as Ex6.
    pose proof
      (merge_int64_by_ints_value w14 w15 x7 H23 H24 Hx7 (proj1 H8))
      as Ex7.
    Exists
      (w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 ::
       w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: nil).
    split_pure_spatial.
    + unfold UIntArray.full, store_array.
      cbn [store_array_rec].
      cbv [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
      cbn.
      cancel.
      replace (input + 0 + 4) with (input + 4) by ring.
      replace (input + 8 + 4) with (input + 12) by ring.
      replace (input + 16 + 4) with (input + 20) by ring.
      replace (input + 24 + 4) with (input + 28) by ring.
      replace (input + 32 + 4) with (input + 36) by ring.
      replace (input + 40 + 4) with (input + 44) by ring.
      replace (input + 48 + 4) with (input + 52) by ring.
      replace (input + 56 + 4) with (input + 60) by ring.
      cancel.
      entailer!.
    + split_pures; dump_pre_spatial.
      * reflexivity.
      * unfold u32_list_bounded.
        intros j Hj.
        apply ZRange.Forall_Znth_Zlength.
        -- repeat constructor; lia.
        -- exact Hj.
      * rewrite <- Hvalue.
        unfold u32_list_value, u64_list_value.
        change
          (@Sum.sum Z (fun i : Z => 0 <= i < 16)
            (ZRange.finite_Z_range 0 16)
            (fun i : Z =>
              Znth i
                (w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 ::
                 w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 ::
                 w15 :: nil)
                0 * U32_MOD ^ i) =
           @Sum.sum Z (fun i : Z => 0 <= i < 8)
            (ZRange.finite_Z_range 0 8)
            (fun i : Z =>
              Znth i
                (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: nil)
                0 * U64_MOD ^ i)).
        repeat rewrite ZRange.sum_Z_range_cons by lia.
        rewrite ZRange.sum_Z_range_empty by lia.
        repeat rewrite ZRange.sum_Z_range_cons by lia.
        rewrite ZRange.sum_Z_range_empty by lia.
        repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia].
        cbn.
        rewrite Ex0, Ex1, Ex2, Ex3, Ex4, Ex5, Ex6, Ex7.
        cbv [U32_MOD U64_MOD].
        ring.
  - repeat rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg xs).
    lia.
Qed. 

Lemma proof_of_solinas_reduce_which_implies_wit_2 : solinas_reduce_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename T_non_alias into T.
  rename words16 into words.
  rename PreH1 into Hlen.
  rename PreH2 into Hbounded.
  rename PreH3 into Hvalue.
  destruct words as [|w0 words];
    [rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w1 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w2 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w3 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w4 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w5 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w6 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w7 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w8 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w9 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w10 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w11 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w12 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w13 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w14 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w15 words];
    [repeat rewrite Zlength_cons in Hlen;
     rewrite Zlength_nil in Hlen; lia|].
  destruct words as [|w16 words].
  - unfold u32_list_bounded in Hbounded.
    pose proof (Hbounded 0 ltac:(cbn [Zlength]; lia)) as Hw0.
    pose proof (Hbounded 1 ltac:(cbn [Zlength]; lia)) as Hw1.
    pose proof (Hbounded 2 ltac:(cbn [Zlength]; lia)) as Hw2.
    pose proof (Hbounded 3 ltac:(cbn [Zlength]; lia)) as Hw3.
    pose proof (Hbounded 4 ltac:(cbn [Zlength]; lia)) as Hw4.
    pose proof (Hbounded 5 ltac:(cbn [Zlength]; lia)) as Hw5.
    pose proof (Hbounded 6 ltac:(cbn [Zlength]; lia)) as Hw6.
    pose proof (Hbounded 7 ltac:(cbn [Zlength]; lia)) as Hw7.
    pose proof (Hbounded 8 ltac:(cbn [Zlength]; lia)) as Hw8.
    pose proof (Hbounded 9 ltac:(cbn [Zlength]; lia)) as Hw9.
    pose proof (Hbounded 10 ltac:(cbn [Zlength]; lia)) as Hw10.
    pose proof (Hbounded 11 ltac:(cbn [Zlength]; lia)) as Hw11.
    pose proof (Hbounded 12 ltac:(cbn [Zlength]; lia)) as Hw12.
    pose proof (Hbounded 13 ltac:(cbn [Zlength]; lia)) as Hw13.
    pose proof (Hbounded 14 ltac:(cbn [Zlength]; lia)) as Hw14.
    pose proof (Hbounded 15 ltac:(cbn [Zlength]; lia)) as Hw15.
    change (0 <= w0 < U32_MOD) in Hw0.
    change (0 <= w1 < U32_MOD) in Hw1.
    change (0 <= w2 < U32_MOD) in Hw2.
    change (0 <= w3 < U32_MOD) in Hw3.
    change (0 <= w4 < U32_MOD) in Hw4.
    change (0 <= w5 < U32_MOD) in Hw5.
    change (0 <= w6 < U32_MOD) in Hw6.
    change (0 <= w7 < U32_MOD) in Hw7.
    change (0 <= w8 < U32_MOD) in Hw8.
    change (0 <= w9 < U32_MOD) in Hw9.
    change (0 <= w10 < U32_MOD) in Hw10.
    change (0 <= w11 < U32_MOD) in Hw11.
    change (0 <= w12 < U32_MOD) in Hw12.
    change (0 <= w13 < U32_MOD) in Hw13.
    change (0 <= w14 < U32_MOD) in Hw14.
    change (0 <= w15 < U32_MOD) in Hw15.
    unfold UIntArray.full, store_array.
    cbn [store_array_rec].
    cbv [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
    cbn.
    Intros.
    replace (input + 0) with input by ring.
    sep_apply_l_atomic
      (store_uint_pair_to_uint64 input w0 w1 Hw0 Hw1).
    replace (input + 12) with (input + 8 + 4) by ring.
    sep_apply_l_atomic
      (store_uint_pair_to_uint64 (input + 8) w2 w3 Hw2 Hw3).
    replace (input + 20) with (input + 16 + 4) by ring.
    sep_apply_l_atomic
      (store_uint_pair_to_uint64 (input + 16) w4 w5 Hw4 Hw5).
    replace (input + 28) with (input + 24 + 4) by ring.
    sep_apply_l_atomic
      (store_uint_pair_to_uint64 (input + 24) w6 w7 Hw6 Hw7).
    replace (input + 36) with (input + 32 + 4) by ring.
    sep_apply_l_atomic
      (store_uint_pair_to_uint64 (input + 32) w8 w9 Hw8 Hw9).
    replace (input + 44) with (input + 40 + 4) by ring.
    sep_apply_l_atomic
      (store_uint_pair_to_uint64 (input + 40) w10 w11 Hw10 Hw11).
    replace (input + 52) with (input + 48 + 4) by ring.
    sep_apply_l_atomic
      (store_uint_pair_to_uint64 (input + 48) w12 w13 Hw12 Hw13).
    replace (input + 60) with (input + 56 + 4) by ring.
    sep_apply_l_atomic
      (store_uint_pair_to_uint64 (input + 56) w14 w15 Hw14 Hw15).
    pose proof (u32_pair_range w0 w1 Hw0 Hw1) as Hl0.
    pose proof (u32_pair_range w2 w3 Hw2 Hw3) as Hl1.
    pose proof (u32_pair_range w4 w5 Hw4 Hw5) as Hl2.
    pose proof (u32_pair_range w6 w7 Hw6 Hw7) as Hl3.
    pose proof (u32_pair_range w8 w9 Hw8 Hw9) as Hl4.
    pose proof (u32_pair_range w10 w11 Hw10 Hw11) as Hl5.
    pose proof (u32_pair_range w12 w13 Hw12 Hw13) as Hl6.
    pose proof (u32_pair_range w14 w15 Hw14 Hw15) as Hl7.
    Exists
      ((w0 + w1 * U32_MOD) :: (w2 + w3 * U32_MOD) ::
       (w4 + w5 * U32_MOD) :: (w6 + w7 * U32_MOD) ::
       (w8 + w9 * U32_MOD) :: (w10 + w11 * U32_MOD) ::
       (w12 + w13 * U32_MOD) :: (w14 + w15 * U32_MOD) :: nil).
    split_pure_spatial.
    + unfold UInt64Array.full, store_array.
      cbn [store_array_rec].
      cbv [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
      cbn.
      replace (input + 0) with input by ring.
      cancel.
      entailer!.
    + split_pures; dump_pre_spatial.
      * reflexivity.
      * unfold u64_list_bounded.
        intros j Hj.
        apply ZRange.Forall_Znth_Zlength.
        -- repeat constructor; lia.
        -- exact Hj.
      * rewrite <- Hvalue.
        unfold u32_list_value.
        change
          (@Sum.sum Z (fun i : Z => 0 <= i < 8)
            (ZRange.finite_Z_range 0 8)
            (fun i : Z =>
              Znth i
                ((w0 + w1 * U32_MOD) :: (w2 + w3 * U32_MOD) ::
                 (w4 + w5 * U32_MOD) :: (w6 + w7 * U32_MOD) ::
                 (w8 + w9 * U32_MOD) :: (w10 + w11 * U32_MOD) ::
                 (w12 + w13 * U32_MOD) ::
                 (w14 + w15 * U32_MOD) :: nil)
                0 * U64_MOD ^ i) =
           @Sum.sum Z (fun i : Z => 0 <= i < 16)
            (ZRange.finite_Z_range 0 16)
            (fun i : Z =>
              Znth i
                (w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 ::
                 w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 ::
                 w15 :: nil)
                0 * U32_MOD ^ i)).
        repeat rewrite ZRange.sum_Z_range_cons by lia.
        rewrite ZRange.sum_Z_range_empty by lia.
        repeat rewrite ZRange.sum_Z_range_cons by lia.
        rewrite ZRange.sum_Z_range_empty by lia.
        repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia].
        cbn.
        cbv [U32_MOD U64_MOD].
        ring.
  - repeat rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg words).
    lia.
Qed. 
