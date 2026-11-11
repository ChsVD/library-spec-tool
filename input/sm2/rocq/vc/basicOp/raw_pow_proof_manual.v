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
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import raw_pow_goal.
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import raw_pow_proof_auto.
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

Lemma proof_of_raw_pow_return_wit_1 : raw_pow_return_wit_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
  pose proof
    (u64_double_u128 retval_4 hi_2 ltac:(lia) ltac:(lia)) as Hdouble01_raw.
  assert (Hdouble01 :
    2 * (x0 * x1) =
      unsigned_last_nbits (Z.shiftl retval_4 1) 64 +
      Z.lor (unsigned_last_nbits (Z.shiftl hi_2 1) 64)
        (Z.shiftr retval_4 63) * U64_MOD +
      Z.shiftr hi_2 63 * U64_MOD * U64_MOD)
    by nia.
  pose proof
    (u64_double_u128 retval_10 hi_4 ltac:(lia) ltac:(lia)) as Hdouble02_raw.
  assert (Hdouble02 :
    2 * (x0 * x2) =
      unsigned_last_nbits (Z.shiftl retval_10 1) 64 +
      Z.lor (unsigned_last_nbits (Z.shiftl hi_4 1) 64)
        (Z.shiftr retval_10 63) * U64_MOD +
      Z.shiftr hi_4 63 * U64_MOD * U64_MOD)
    by nia.
  pose proof
    (u64_double_u128 retval_13 hi_5 ltac:(lia) ltac:(lia)) as Hdouble03_raw.
  assert (Hdouble03 :
    2 * (x0 * x3) =
      unsigned_last_nbits (Z.shiftl retval_13 1) 64 +
      Z.lor (unsigned_last_nbits (Z.shiftl hi_5 1) 64)
        (Z.shiftr retval_13 63) * U64_MOD +
      Z.shiftr hi_5 63 * U64_MOD * U64_MOD)
    by nia.
  pose proof
    (u64_double_u128 retval_16 hi_6 ltac:(lia) ltac:(lia)) as Hdouble12_raw.
  assert (Hdouble12 :
    2 * (x1 * x2) =
      unsigned_last_nbits (Z.shiftl retval_16 1) 64 +
      Z.lor (unsigned_last_nbits (Z.shiftl hi_6 1) 64)
        (Z.shiftr retval_16 63) * U64_MOD +
      Z.shiftr hi_6 63 * U64_MOD * U64_MOD)
    by nia.
  pose proof
    (u64_double_u128 retval_22 hi_8 ltac:(lia) ltac:(lia)) as Hdouble13_raw.
  assert (Hdouble13 :
    2 * (x1 * x3) =
      unsigned_last_nbits (Z.shiftl retval_22 1) 64 +
      Z.lor (unsigned_last_nbits (Z.shiftl hi_8 1) 64)
        (Z.shiftr retval_22 63) * U64_MOD +
      Z.shiftr hi_8 63 * U64_MOD * U64_MOD)
    by nia.
  pose proof
    (u64_double_u128 retval_25 hi_9 ltac:(lia) ltac:(lia)) as Hdouble23_raw.
  assert (Hdouble23 :
    2 * (x2 * x3) =
      unsigned_last_nbits (Z.shiftl retval_25 1) 64 +
      Z.lor (unsigned_last_nbits (Z.shiftl hi_9 1) 64)
        (Z.shiftr retval_25 63) * U64_MOD +
      Z.shiftr hi_9 63 * U64_MOD * U64_MOD)
    by nia.

  pose proof (u64_shiftr63_range hi_2 ltac:(lia)) as Hbit_hi2.
  pose proof (u64_shiftr63_range hi_4 ltac:(lia)) as Hbit_hi4.
  pose proof (u64_shiftr63_range hi_5 ltac:(lia)) as Hbit_hi5.
  pose proof (u64_shiftr63_range hi_6 ltac:(lia)) as Hbit_hi6.
  pose proof (u64_shiftr63_range hi_8 ltac:(lia)) as Hbit_hi8.
  pose proof (u64_shiftr63_range hi_9 ltac:(lia)) as Hbit_hi9.
  assert (Hcarry01 :
    unsigned_last_nbits
      (0 + retval_3 + retval_6 + Z.shiftr hi_2 63) 8 =
    retval_3 + retval_6 + Z.shiftr hi_2 63).
  {
    replace (0 + retval_3 + retval_6 + Z.shiftr hi_2 63)
      with (retval_3 + retval_6 + Z.shiftr hi_2 63) by ring.
    apply u8_last_nbits_bits3; lia.
  }
  assert (Hcarry02 :
    unsigned_last_nbits
      (0 + retval_9 + retval_12 + Z.shiftr hi_4 63) 8 =
    retval_9 + retval_12 + Z.shiftr hi_4 63).
  {
    replace (0 + retval_9 + retval_12 + Z.shiftr hi_4 63)
      with (retval_9 + retval_12 + Z.shiftr hi_4 63) by ring.
    apply u8_last_nbits_bits3; lia.
  }
  assert (Hcarry0312 :
    unsigned_last_nbits
      (unsigned_last_nbits
         (unsigned_last_nbits (0 + retval_15 + Z.shiftr hi_5 63) 8 +
          retval_18) 8 + Z.shiftr hi_6 63) 8 =
    retval_15 + Z.shiftr hi_5 63 + retval_18 + Z.shiftr hi_6 63).
  {
    change
      (unsigned_last_nbits
         (unsigned_last_nbits
            (unsigned_last_nbits (retval_15 + Z.shiftr hi_5 63) 8 +
             retval_18) 8 + Z.shiftr hi_6 63) 8 =
       retval_15 + Z.shiftr hi_5 63 + retval_18 + Z.shiftr hi_6 63).
    apply u8_last_nbits_nested4; lia.
  }
  assert (Hcarry13 :
    unsigned_last_nbits
      (0 + retval_21 + retval_24 + Z.shiftr hi_8 63) 8 =
    retval_21 + retval_24 + Z.shiftr hi_8 63).
  {
    replace (0 + retval_21 + retval_24 + Z.shiftr hi_8 63)
      with (retval_21 + retval_24 + Z.shiftr hi_8 63) by ring.
    apply u8_last_nbits_bits3; lia.
  }
  assert (Hcarry23 :
    unsigned_last_nbits (0 + retval_27 + Z.shiftr hi_9 63) 8 =
    retval_27 + Z.shiftr hi_9 63).
  {
    replace (0 + retval_27 + Z.shiftr hi_9 63)
      with (retval_27 + Z.shiftr hi_9 63) by ring.
    apply u8_last_nbits_bits2; lia.
  }

  assert (HA_range : 0 <= A < U256_MOD).
  {
    pose proof
      (u256_of_limbs_range x0 x1 x2 x3
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hrange.
    nia.
  }
  assert (Hsquare_range : 0 <= A * A < U512_MOD).
  {
    replace U512_MOD with (U256_MOD * U256_MOD)
      by (cbv [U512_MOD U256_MOD]; reflexivity).
    clear - HA_range.
    nia.
  }
  assert (Hsquare_decompose :
    A * A =
      x0 * x0 +
      2 * (x0 * x1) * U64_MOD +
      (x1 * x1 + 2 * (x0 * x2)) * U64_MOD ^ 2 +
      (2 * (x0 * x3) + 2 * (x1 * x2)) * U64_MOD ^ 3 +
      (x2 * x2 + 2 * (x1 * x3)) * U64_MOD ^ 4 +
      2 * (x2 * x3) * U64_MOD ^ 5 +
      x3 * x3 * U64_MOD ^ 6).
  {
    rewrite PreH151.
    unfold u256_of_limbs.
    ring.
  }
  assert (Hinitial_zero : retval_3 = 0).
  {
    clear - PreH158 PreH159 PreH141 PreH136 PreH138
      PreH150 PreH145 PreH140.
    apply
      (initial_square_top_carry_zero
         U64_MOD x0 retval hi out retval_2 out_2 retval_3);
      try lia.
    unfold U64_MOD.
    lia.
  }
  assert (Hstage0 :
    x0 * x0 =
      out + out_2 * U64_MOD + retval_3 * U64_MOD ^ 2)
    by (clear - PreH150 PreH145 PreH140; nia).
  assert (Hstage1 :
    x0 * x0 + 2 * (x0 * x1) * U64_MOD =
      out + out_3 * U64_MOD + out_4 * U64_MOD ^ 2 +
      (retval_3 + retval_6 + Z.shiftr hi_2 63) * U64_MOD ^ 3)
    by (clear - Hstage0 Hinitial_zero Hdouble01 PreH130 PreH125; nia).
  assert (Hstage2 :
    x0 * x0 + 2 * (x0 * x1) * U64_MOD +
      x1 * x1 * U64_MOD ^ 2 =
      out + out_3 * U64_MOD + out_5 * U64_MOD ^ 2 +
      out_6 * U64_MOD ^ 3 + retval_9 * U64_MOD ^ 4)
    by (clear - Hstage1 Hcarry01 PreH120 PreH115 PreH110; nia).
  assert (Hstage3 :
    x0 * x0 + 2 * (x0 * x1) * U64_MOD +
      (x1 * x1 + 2 * (x0 * x2)) * U64_MOD ^ 2 =
      out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
      out_8 * U64_MOD ^ 3 +
      (retval_9 + retval_12 + Z.shiftr hi_4 63) * U64_MOD ^ 4)
    by (clear - Hstage2 Hdouble02 PreH100 PreH95; nia).
  assert (Hstage4 :
    x0 * x0 + 2 * (x0 * x1) * U64_MOD +
      (x1 * x1 + 2 * (x0 * x2)) * U64_MOD ^ 2 +
      2 * (x0 * x3) * U64_MOD ^ 3 =
      out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
      out_9 * U64_MOD ^ 3 + out_10 * U64_MOD ^ 4 +
      (retval_15 + Z.shiftr hi_5 63) * U64_MOD ^ 5)
    by (clear - Hstage3 Hcarry02 Hdouble03 PreH85 PreH80; nia).
  assert (Hstage5 :
    x0 * x0 + 2 * (x0 * x1) * U64_MOD +
      (x1 * x1 + 2 * (x0 * x2)) * U64_MOD ^ 2 +
      (2 * (x0 * x3) + 2 * (x1 * x2)) * U64_MOD ^ 3 =
      out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
      out_11 * U64_MOD ^ 3 + out_12 * U64_MOD ^ 4 +
      (retval_15 + Z.shiftr hi_5 63 + retval_18 +
       Z.shiftr hi_6 63) * U64_MOD ^ 5)
    by (clear - Hstage4 Hdouble12 PreH70 PreH65; nia).
  assert (Hstage6 :
    x0 * x0 + 2 * (x0 * x1) * U64_MOD +
      (x1 * x1 + 2 * (x0 * x2)) * U64_MOD ^ 2 +
      (2 * (x0 * x3) + 2 * (x1 * x2)) * U64_MOD ^ 3 +
      x2 * x2 * U64_MOD ^ 4 =
      out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
      out_11 * U64_MOD ^ 3 + out_13 * U64_MOD ^ 4 +
      out_14 * U64_MOD ^ 5 + retval_21 * U64_MOD ^ 6)
    by (clear - Hstage5 Hcarry0312 PreH60 PreH55 PreH50; nia).
  assert (Hstage7 :
    x0 * x0 + 2 * (x0 * x1) * U64_MOD +
      (x1 * x1 + 2 * (x0 * x2)) * U64_MOD ^ 2 +
      (2 * (x0 * x3) + 2 * (x1 * x2)) * U64_MOD ^ 3 +
      (x2 * x2 + 2 * (x1 * x3)) * U64_MOD ^ 4 =
      out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
      out_11 * U64_MOD ^ 3 + out_15 * U64_MOD ^ 4 +
      out_16 * U64_MOD ^ 5 +
      (retval_21 + retval_24 + Z.shiftr hi_8 63) * U64_MOD ^ 6)
    by (clear - Hstage6 Hdouble13 PreH40 PreH35; nia).
  assert (Hcross23 :
    out_16 +
      (retval_21 + retval_24 + Z.shiftr hi_8 63) * U64_MOD +
      2 * (x2 * x3) =
    out_17 + out_18 * U64_MOD +
      (retval_27 + Z.shiftr hi_9 63) * U64_MOD ^ 2)
    by (clear - Hcarry13 Hdouble23 PreH25 PreH20; nia).
  assert (Hstage8 :
    x0 * x0 + 2 * (x0 * x1) * U64_MOD +
      (x1 * x1 + 2 * (x0 * x2)) * U64_MOD ^ 2 +
      (2 * (x0 * x3) + 2 * (x1 * x2)) * U64_MOD ^ 3 +
      (x2 * x2 + 2 * (x1 * x3)) * U64_MOD ^ 4 +
      2 * (x2 * x3) * U64_MOD ^ 5 =
      out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
      out_11 * U64_MOD ^ 3 + out_15 * U64_MOD ^ 4 +
      out_17 * U64_MOD ^ 5 + out_18 * U64_MOD ^ 6 +
      (retval_27 + Z.shiftr hi_9 63) * U64_MOD ^ 7).
  {
    clear - Hstage7 Hcross23.
    rewrite Hstage7.
    replace
      (out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
       out_11 * U64_MOD ^ 3 + out_15 * U64_MOD ^ 4 +
       out_16 * U64_MOD ^ 5 +
       (retval_21 + retval_24 + Z.shiftr hi_8 63) * U64_MOD ^ 6 +
       2 * (x2 * x3) * U64_MOD ^ 5)
      with
      (out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
       out_11 * U64_MOD ^ 3 + out_15 * U64_MOD ^ 4 +
       (out_16 +
        (retval_21 + retval_24 + Z.shiftr hi_8 63) * U64_MOD +
        2 * (x2 * x3)) * U64_MOD ^ 5)
      by ring.
    replace
      (out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
       out_11 * U64_MOD ^ 3 + out_15 * U64_MOD ^ 4 +
       out_17 * U64_MOD ^ 5 + out_18 * U64_MOD ^ 6 +
       (retval_27 + Z.shiftr hi_9 63) * U64_MOD ^ 7)
      with
      (out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
       out_11 * U64_MOD ^ 3 + out_15 * U64_MOD ^ 4 +
       (out_17 + out_18 * U64_MOD +
        (retval_27 + Z.shiftr hi_9 63) * U64_MOD ^ 2) * U64_MOD ^ 5)
      by ring.
    rewrite Hcross23.
    reflexivity.
  }
  assert (Hfinal_square :
    out_18 + (retval_27 + Z.shiftr hi_9 63) * U64_MOD + x3 * x3 =
    out_19 + out_20 * U64_MOD + retval_30 * U64_MOD ^ 2)
    by (clear - Hcarry23 PreH15 PreH10 PreH5; nia).
  assert (Hstage9 :
    x0 * x0 + 2 * (x0 * x1) * U64_MOD +
      (x1 * x1 + 2 * (x0 * x2)) * U64_MOD ^ 2 +
      (2 * (x0 * x3) + 2 * (x1 * x2)) * U64_MOD ^ 3 +
      (x2 * x2 + 2 * (x1 * x3)) * U64_MOD ^ 4 +
      2 * (x2 * x3) * U64_MOD ^ 5 + x3 * x3 * U64_MOD ^ 6 =
      out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
      out_11 * U64_MOD ^ 3 + out_15 * U64_MOD ^ 4 +
      out_17 * U64_MOD ^ 5 + out_19 * U64_MOD ^ 6 +
      out_20 * U64_MOD ^ 7 + retval_30 * U64_MOD ^ 8).
  {
    clear - Hstage8 Hfinal_square.
    rewrite Hstage8.
    replace
      (out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
       out_11 * U64_MOD ^ 3 + out_15 * U64_MOD ^ 4 +
       out_17 * U64_MOD ^ 5 + out_18 * U64_MOD ^ 6 +
       (retval_27 + Z.shiftr hi_9 63) * U64_MOD ^ 7 +
       x3 * x3 * U64_MOD ^ 6)
      with
      (out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
       out_11 * U64_MOD ^ 3 + out_15 * U64_MOD ^ 4 +
       out_17 * U64_MOD ^ 5 +
       (out_18 + (retval_27 + Z.shiftr hi_9 63) * U64_MOD +
        x3 * x3) * U64_MOD ^ 6)
      by ring.
    replace
      (out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
       out_11 * U64_MOD ^ 3 + out_15 * U64_MOD ^ 4 +
       out_17 * U64_MOD ^ 5 + out_19 * U64_MOD ^ 6 +
       out_20 * U64_MOD ^ 7 + retval_30 * U64_MOD ^ 8)
      with
      (out + out_3 * U64_MOD + out_7 * U64_MOD ^ 2 +
       out_11 * U64_MOD ^ 3 + out_15 * U64_MOD ^ 4 +
       out_17 * U64_MOD ^ 5 +
       (out_19 + out_20 * U64_MOD + retval_30 * U64_MOD ^ 2) *
       U64_MOD ^ 6)
      by ring.
    rewrite Hfinal_square.
    reflexivity.
  }
  assert (Hweighted :
    A * A =
      u512_of_limbs out out_3 out_7 out_11 out_15 out_17 out_19 out_20 +
      retval_30 * U64_MOD ^ 8).
  {
    unfold u512_of_limbs.
    rewrite Hsquare_decompose.
    exact Hstage9.
  }
  pose proof
    (u512_of_limbs_range out out_3 out_7 out_11
       out_15 out_17 out_19 out_20
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hout_range.
  assert (Hradix8 : U64_MOD ^ 8 = U512_MOD).
  {
    cbv [U64_MOD U512_MOD U256_MOD].
    reflexivity.
  }
  assert (Htop_zero : retval_30 = 0)
    by (clear - Hweighted Hsquare_range Hout_range PreH3 Hradix8; nia).
  assert (Hout_value :
    A * A =
      u256_of_limbs out out_3 out_7 out_11 +
      u256_of_limbs out_15 out_17 out_19 out_20 * U256_MOD).
  {
    rewrite <- u512_as_u256_pair.
    clear - Hweighted Htop_zero.
    nia.
  }
  split_pure_spatial.
  - clear - Hout_value PreH1 PreH2 PreH6 PreH7 PreH21 PreH22
      PreH36 PreH37 PreH66 PreH67 PreH96 PreH97 PreH126 PreH127
      PreH141 PreH142 PreH151 PreH152 PreH153 PreH154 PreH155
      PreH156 PreH157 PreH158 PreH159.
    unfold store_u256_limbs, store_u64_limbs.
    Exists x0 x1 x2 x3.
    Exists (out :: out_3 :: out_7 :: out_11 ::
            out_15 :: out_17 :: out_19 :: out_20 :: nil).
    unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    split_pure_spatial.
    + rewrite !sizeof_uint64.
      cbn.
      sepcon_assoc_change.
      cancel.
    + split_pures.
      * dump_pre_spatial.
        repeat split; try lia; assumption.
      * dump_pre_spatial.
        split.
        { reflexivity. }
        split.
        {
          unfold u64_list_bounded, limb_list_bounded.
          intros index Hindex.
          apply ZRange.Forall_Znth_Zlength.
          - repeat constructor; lia.
          - exact Hindex.
        }
        {
          unfold u64_list_value, limb_list_value.
          change
            (@Sum.sum Z (fun i : Z => 0 <= i < 8)
               (ZRange.finite_Z_range 0 8)
               (fun i : Z =>
                  Znth i
                    (out :: out_3 :: out_7 :: out_11 ::
                     out_15 :: out_17 :: out_19 :: out_20 :: nil)
                    0 * U64_MOD ^ i) = A * A).
          repeat rewrite ZRange.sum_Z_range_cons by lia.
          rewrite ZRange.sum_Z_range_empty by lia.
          repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia].
          cbn.
          rewrite Hout_value.
          cbv [u256_of_limbs U256_MOD U64_MOD].
          ring.
        }
      * dump_pre_spatial.
        reflexivity.
      * dump_pre_spatial.
        reflexivity.
  - split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_raw_pow_partial_solve_wit_11_pure_split_goal_1 : raw_pow_partial_solve_wit_11_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_11_pure_split_goal_2 : raw_pow_partial_solve_wit_11_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_11_pure : raw_pow_partial_solve_wit_11_pure.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (unsigned_Lastnbits_range (Z.shiftl retval 1) 64 ltac:(lia))
      as Hrange;
    fold U64_MOD in Hrange;
    lia).
Qed.

Lemma proof_of_raw_pow_partial_solve_wit_13_pure_split_goal_1 : raw_pow_partial_solve_wit_13_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_13_pure_split_goal_2 : raw_pow_partial_solve_wit_13_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_13_pure : raw_pow_partial_solve_wit_13_pure.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (u64_double_lor_range hi retval ltac:(lia) ltac:(lia)) as Hrange;
    lia).
Qed.

Lemma proof_of_raw_pow_partial_solve_wit_19_pure_split_goal_1 : raw_pow_partial_solve_wit_19_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_19_pure : raw_pow_partial_solve_wit_19_pure.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (unsigned_Lastnbits_range
         ((0 + retval) + retval_2 + Z.shiftr hi 63) 8 ltac:(lia))
      as Hrange;
    assert (H8_64 : 2 ^ 8 < U64_MOD) by (unfold U64_MOD; lia);
    lia).
Qed.

Lemma proof_of_raw_pow_partial_solve_wit_22_pure_split_goal_1 : raw_pow_partial_solve_wit_22_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_22_pure_split_goal_2 : raw_pow_partial_solve_wit_22_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_22_pure : raw_pow_partial_solve_wit_22_pure.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (unsigned_Lastnbits_range (Z.shiftl retval 1) 64 ltac:(lia))
      as Hrange;
    fold U64_MOD in Hrange;
    lia).
Qed.

Lemma proof_of_raw_pow_partial_solve_wit_24_pure_split_goal_1 : raw_pow_partial_solve_wit_24_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_24_pure_split_goal_2 : raw_pow_partial_solve_wit_24_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_24_pure : raw_pow_partial_solve_wit_24_pure.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (u64_double_lor_range hi retval ltac:(lia) ltac:(lia)) as Hrange;
    lia).
Qed.

Lemma proof_of_raw_pow_partial_solve_wit_28_pure_split_goal_1 : raw_pow_partial_solve_wit_28_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_28_pure_split_goal_2 : raw_pow_partial_solve_wit_28_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_28_pure : raw_pow_partial_solve_wit_28_pure.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (unsigned_Lastnbits_range (Z.shiftl retval 1) 64 ltac:(lia))
      as Hrange;
    fold U64_MOD in Hrange;
    lia).
Qed.

Lemma proof_of_raw_pow_partial_solve_wit_30_pure_split_goal_1 : raw_pow_partial_solve_wit_30_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_30_pure_split_goal_2 : raw_pow_partial_solve_wit_30_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_30_pure_split_goal_3 : raw_pow_partial_solve_wit_30_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_30_pure : raw_pow_partial_solve_wit_30_pure.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (unsigned_Lastnbits_range
         ((0 + retval) + retval_2 + Z.shiftr hi 63) 8 ltac:(lia))
      as Hrange;
    pose proof
      (u64_double_lor_range hi_2 retval_3 ltac:(lia) ltac:(lia))
      as Hlor;
    assert (H8_64 : 2 ^ 8 < U64_MOD) by (unfold U64_MOD; lia);
    lia).
Qed.

Lemma proof_of_raw_pow_partial_solve_wit_33_pure_split_goal_1 : raw_pow_partial_solve_wit_33_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_33_pure_split_goal_2 : raw_pow_partial_solve_wit_33_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_33_pure : raw_pow_partial_solve_wit_33_pure.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (unsigned_Lastnbits_range (Z.shiftl retval 1) 64 ltac:(lia))
      as Hrange;
    fold U64_MOD in Hrange;
    lia).
Qed.

Lemma proof_of_raw_pow_partial_solve_wit_35_pure_split_goal_1 : raw_pow_partial_solve_wit_35_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_35_pure_split_goal_2 : raw_pow_partial_solve_wit_35_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_35_pure : raw_pow_partial_solve_wit_35_pure.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (u64_double_lor_range hi retval ltac:(lia) ltac:(lia)) as Hrange;
    lia).
Qed.

Lemma proof_of_raw_pow_partial_solve_wit_41_pure_split_goal_1 : raw_pow_partial_solve_wit_41_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_41_pure : raw_pow_partial_solve_wit_41_pure.
Proof.
  LLM_pre_process ltac:(
    match goal with
    | |- context [unsigned_last_nbits ?x 8] =>
        pose proof (unsigned_Lastnbits_range x 8 ltac:(lia)) as Hrange
    end;
    assert (H8_64 : 2 ^ 8 < U64_MOD) by (unfold U64_MOD; lia);
    lia).
Qed.

Lemma proof_of_raw_pow_partial_solve_wit_44_pure_split_goal_1 : raw_pow_partial_solve_wit_44_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_44_pure_split_goal_2 : raw_pow_partial_solve_wit_44_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_44_pure : raw_pow_partial_solve_wit_44_pure.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (unsigned_Lastnbits_range (Z.shiftl retval 1) 64 ltac:(lia))
      as Hrange;
    fold U64_MOD in Hrange;
    lia).
Qed.

Lemma proof_of_raw_pow_partial_solve_wit_46_pure_split_goal_1 : raw_pow_partial_solve_wit_46_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_46_pure_split_goal_2 : raw_pow_partial_solve_wit_46_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_46_pure : raw_pow_partial_solve_wit_46_pure.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (u64_double_lor_range hi retval ltac:(lia) ltac:(lia)) as Hrange;
    lia).
Qed.

Lemma proof_of_raw_pow_partial_solve_wit_50_pure_split_goal_1 : raw_pow_partial_solve_wit_50_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_50_pure_split_goal_2 : raw_pow_partial_solve_wit_50_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_50_pure : raw_pow_partial_solve_wit_50_pure.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (unsigned_Lastnbits_range (Z.shiftl retval 1) 64 ltac:(lia))
      as Hrange;
    fold U64_MOD in Hrange;
    lia).
Qed.

Lemma proof_of_raw_pow_partial_solve_wit_52_pure_split_goal_1 : raw_pow_partial_solve_wit_52_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_52_pure_split_goal_2 : raw_pow_partial_solve_wit_52_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_52_pure_split_goal_3 : raw_pow_partial_solve_wit_52_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_52_pure : raw_pow_partial_solve_wit_52_pure.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (unsigned_Lastnbits_range
         ((0 + retval) + retval_2 + Z.shiftr hi 63) 8 ltac:(lia))
      as Hrange;
    pose proof
      (u64_double_lor_range hi_2 retval_3 ltac:(lia) ltac:(lia))
      as Hlor;
    assert (H8_64 : 2 ^ 8 < U64_MOD) by (unfold U64_MOD; lia);
    lia).
Qed.

Lemma proof_of_raw_pow_partial_solve_wit_58_pure_split_goal_1 : raw_pow_partial_solve_wit_58_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_pow_partial_solve_wit_58_pure : raw_pow_partial_solve_wit_58_pure.
Proof.
  LLM_pre_process ltac:(
    pose proof
      (unsigned_Lastnbits_range
         ((0 + retval) + Z.shiftr hi 63) 8 ltac:(lia)) as Hrange;
    assert (H8_64 : 2 ^ 8 < U64_MOD) by (unfold U64_MOD; lia);
    lia).
Qed.
