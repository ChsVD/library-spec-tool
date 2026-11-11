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
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import raw_mul_goal.
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import raw_mul_proof_auto.
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

Lemma proof_of_raw_mul_entail_wit_2_a_eq_b_split_goal_1 : raw_mul_entail_wit_2_a_eq_b_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hradixpos : 0 < U64_MOD) by (cbv [U64_MOD]; lia).
  assert (Hlow00 : 0 + retval = out + retval_2 * U64_MOD) by lia.
  pose proof
    (radix_add2_conservation U64_MOD
      0 0 retval hi out out_2 retval_2 retval_3
      Hlow00 PreH140) as Hs00.
  assert (Hstage0 :
    raw_mul_prefix_0 x0 x1 x2 x3 x0 x1 x2 x3 =
      out + out_2 * U64_MOD + retval_3 * U64_MOD ^ 2).
  {
    clear - Hs00 PreH150.
    unfold raw_mul_prefix_0.
    nia.
  }
  assert (Hmul00range : 0 <= x0 * x0 < U64_MOD ^ 2).
  { apply u64_mul_range; lia. }
  assert (Hcarry00 : retval_3 = 0).
  {
    unfold raw_mul_prefix_0 in Hstage0.
    clear - Hstage0 Hmul00range PreH138 PreH136 PreH141 Hradixpos.
    nia.
  }
  subst retval_3.
  assert (Hlow01 : out_2 + retval_4 = out_3 + retval_5 * U64_MOD)
    by lia.
  pose proof
    (radix_add2_conservation U64_MOD
      out_2 0 retval_4 hi_2 out_3 out_4 retval_5 retval_6
      Hlow01 PreH125) as Hs01.
  assert (Hlow10 : out_3 + retval_7 = out_5 + retval_8 * U64_MOD)
    by lia.
  pose proof
    (radix_add2_conservation U64_MOD
      out_3 out_4 retval_7 hi_3 out_5 out_6 retval_8 retval_9
      Hlow10 PreH110) as Hs10.
  assert (Hstage1 :
    raw_mul_prefix_1 x0 x1 x2 x3 x0 x1 x2 x3 =
      out + out_5 * U64_MOD + out_6 * U64_MOD ^ 2 +
      (retval_6 + retval_9) * U64_MOD ^ 3).
  {
    clear - Hstage0 Hs01 Hs10 PreH135 PreH120.
    unfold raw_mul_prefix_1.
    nia.
  }
  assert (Hlow02 : out_6 + retval_10 = out_7 + retval_11 * U64_MOD)
    by lia.
  assert (Hhigh02 :
    retval_6 + retval_9 + hi_4 + retval_11 =
      out_8 + retval_12 * U64_MOD).
  { clear - PreH95; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_6 (retval_6 + retval_9) retval_10 hi_4
      out_7 out_8 retval_11 retval_12 Hlow02 Hhigh02) as Hs02.
  assert (Hlow11 : out_7 + retval_13 = out_9 + retval_14 * U64_MOD).
  { clear - PreH85; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_7 out_8 retval_13 hi_5 out_9 out_10 retval_14 retval_15
      Hlow11 PreH80) as Hs11.
  assert (Hlow20 : out_9 + retval_16 = out_11 + retval_17 * U64_MOD).
  { clear - PreH70; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_9 out_10 retval_16 hi_6 out_11 out_12 retval_17 retval_18
      Hlow20 PreH65) as Hs20.
  assert (Hstage2 :
    raw_mul_prefix_2 x0 x1 x2 x3 x0 x1 x2 x3 =
      out + out_5 * U64_MOD + out_11 * U64_MOD ^ 2 +
      out_12 * U64_MOD ^ 3 +
      (retval_12 + retval_15 + retval_18) * U64_MOD ^ 4).
  {
    clear - Hstage1 Hs02 Hs11 Hs20 PreH105 PreH90 PreH75.
    unfold raw_mul_prefix_2.
    nia.
  }
  assert (Hlow03 : out_12 + retval_19 = out_13 + retval_20 * U64_MOD).
  { clear - PreH55; lia. }
  assert (Hhigh03 :
    retval_12 + retval_15 + retval_18 + hi_7 + retval_20 =
      out_14 + retval_21 * U64_MOD).
  { clear - PreH50; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_12 (retval_12 + retval_15 + retval_18) retval_19 hi_7
      out_13 out_14 retval_20 retval_21 Hlow03 Hhigh03) as Hs03.
  assert (Hlow12 : out_13 + retval_22 = out_15 + retval_23 * U64_MOD).
  { clear - PreH40; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_13 out_14 retval_22 hi_8 out_15 out_16 retval_23 retval_24
      Hlow12 PreH35) as Hs12.
  assert (Hlow21 : out_15 + retval_25 = out_17 + retval_26 * U64_MOD).
  { clear - PreH25; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_15 out_16 retval_25 hi_9 out_17 out_18 retval_26 retval_27
      Hlow21 PreH20) as Hs21.
  assert (Hlow30 : out_17 + retval_28 = out_19 + retval_29 * U64_MOD).
  { clear - PreH10; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_17 out_18 retval_28 hi_10 out_19 out_20 retval_29 retval_30
      Hlow30 PreH5) as Hs30.
  assert (Hstage3 :
    raw_mul_prefix_3 x0 x1 x2 x3 x0 x1 x2 x3 =
      out + out_5 * U64_MOD + out_11 * U64_MOD ^ 2 +
      out_19 * U64_MOD ^ 3 + out_20 * U64_MOD ^ 4 +
      (retval_21 + retval_24 + retval_27 + retval_30) * U64_MOD ^ 5).
  {
    clear - Hstage2 Hs03 Hs12 Hs21 Hs30
      PreH60 PreH45 PreH30 PreH15.
    unfold raw_mul_prefix_3.
    nia.
  }
  clear - Hstage3.
  nia.
Qed.

Lemma proof_of_raw_mul_entail_wit_2_a_eq_b_split_goal_2 : raw_mul_entail_wit_2_a_eq_b_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbv [U64_MOD] in *; lia).
Qed.

Lemma proof_of_raw_mul_entail_wit_2_a_eq_b : raw_mul_entail_wit_2_a_eq_b.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_raw_mul_entail_wit_2_a_eq_b_split_goal_1.
  - Goal_apply proof_of_raw_mul_entail_wit_2_a_eq_b_split_goal_2.
Qed.

Lemma proof_of_raw_mul_entail_wit_3_non_alias_split_goal_1 : raw_mul_entail_wit_3_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hradixpos : 0 < U64_MOD) by (cbv [U64_MOD]; lia).
  assert (Hlow00 : 0 + retval = out + retval_2 * U64_MOD).
  { clear - PreH145; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      0 0 retval hi out out_2 retval_2 retval_3
      Hlow00 PreH140) as Hs00.
  assert (Hstage0 :
    raw_mul_prefix_0 x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2 =
      out + out_2 * U64_MOD + retval_3 * U64_MOD ^ 2).
  {
    clear - Hs00 PreH150.
    unfold raw_mul_prefix_0.
    nia.
  }
  assert (Hmul00range : 0 <= x0 * x0_2 < U64_MOD ^ 2).
  { apply u64_mul_range; lia. }
  assert (Hcarry00 : retval_3 = 0).
  {
    unfold raw_mul_prefix_0 in Hstage0.
    clear - Hstage0 Hmul00range PreH138 PreH136 PreH141 Hradixpos.
    nia.
  }
  subst retval_3.
  assert (Hlow01 : out_2 + retval_4 = out_3 + retval_5 * U64_MOD).
  { clear - PreH130; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_2 0 retval_4 hi_2 out_3 out_4 retval_5 retval_6
      Hlow01 PreH125) as Hs01.
  assert (Hlow10 : out_3 + retval_7 = out_5 + retval_8 * U64_MOD).
  { clear - PreH115; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_3 out_4 retval_7 hi_3 out_5 out_6 retval_8 retval_9
      Hlow10 PreH110) as Hs10.
  assert (Hstage1 :
    raw_mul_prefix_1 x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2 =
      out + out_5 * U64_MOD + out_6 * U64_MOD ^ 2 +
      (retval_6 + retval_9) * U64_MOD ^ 3).
  {
    clear - Hstage0 Hs01 Hs10 PreH135 PreH120.
    unfold raw_mul_prefix_1.
    nia.
  }
  assert (Hlow02 : out_6 + retval_10 = out_7 + retval_11 * U64_MOD).
  { clear - PreH100; lia. }
  assert (Hhigh02 :
    retval_6 + retval_9 + hi_4 + retval_11 =
      out_8 + retval_12 * U64_MOD).
  { clear - PreH95; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_6 (retval_6 + retval_9) retval_10 hi_4
      out_7 out_8 retval_11 retval_12 Hlow02 Hhigh02) as Hs02.
  assert (Hlow11 : out_7 + retval_13 = out_9 + retval_14 * U64_MOD).
  { clear - PreH85; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_7 out_8 retval_13 hi_5 out_9 out_10 retval_14 retval_15
      Hlow11 PreH80) as Hs11.
  assert (Hlow20 : out_9 + retval_16 = out_11 + retval_17 * U64_MOD).
  { clear - PreH70; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_9 out_10 retval_16 hi_6 out_11 out_12 retval_17 retval_18
      Hlow20 PreH65) as Hs20.
  assert (Hstage2 :
    raw_mul_prefix_2 x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2 =
      out + out_5 * U64_MOD + out_11 * U64_MOD ^ 2 +
      out_12 * U64_MOD ^ 3 +
      (retval_12 + retval_15 + retval_18) * U64_MOD ^ 4).
  {
    clear - Hstage1 Hs02 Hs11 Hs20 PreH105 PreH90 PreH75.
    unfold raw_mul_prefix_2.
    nia.
  }
  assert (Hlow03 : out_12 + retval_19 = out_13 + retval_20 * U64_MOD).
  { clear - PreH55; lia. }
  assert (Hhigh03 :
    retval_12 + retval_15 + retval_18 + hi_7 + retval_20 =
      out_14 + retval_21 * U64_MOD).
  { clear - PreH50; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_12 (retval_12 + retval_15 + retval_18) retval_19 hi_7
      out_13 out_14 retval_20 retval_21 Hlow03 Hhigh03) as Hs03.
  assert (Hlow12 : out_13 + retval_22 = out_15 + retval_23 * U64_MOD).
  { clear - PreH40; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_13 out_14 retval_22 hi_8 out_15 out_16 retval_23 retval_24
      Hlow12 PreH35) as Hs12.
  assert (Hlow21 : out_15 + retval_25 = out_17 + retval_26 * U64_MOD).
  { clear - PreH25; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_15 out_16 retval_25 hi_9 out_17 out_18 retval_26 retval_27
      Hlow21 PreH20) as Hs21.
  assert (Hlow30 : out_17 + retval_28 = out_19 + retval_29 * U64_MOD).
  { clear - PreH10; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_17 out_18 retval_28 hi_10 out_19 out_20 retval_29 retval_30
      Hlow30 PreH5) as Hs30.
  assert (Hstage3 :
    raw_mul_prefix_3 x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2 =
      out + out_5 * U64_MOD + out_11 * U64_MOD ^ 2 +
      out_19 * U64_MOD ^ 3 + out_20 * U64_MOD ^ 4 +
      (retval_21 + retval_24 + retval_27 + retval_30) * U64_MOD ^ 5).
  {
    clear - Hstage2 Hs03 Hs12 Hs21 Hs30
      PreH60 PreH45 PreH30 PreH15.
    unfold raw_mul_prefix_3.
    rewrite PreH60, PreH45, PreH30, PreH15, Hstage2.
    nia.
  }
  clear - Hstage3.
  nia.
Qed.

Lemma proof_of_raw_mul_entail_wit_3_non_alias_split_goal_2 : raw_mul_entail_wit_3_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbv [U64_MOD] in *; lia).
Qed.

Lemma proof_of_raw_mul_entail_wit_3_non_alias : raw_mul_entail_wit_3_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_raw_mul_entail_wit_3_non_alias_split_goal_1.
  - Goal_apply proof_of_raw_mul_entail_wit_3_non_alias_split_goal_2.
Qed.

Lemma proof_of_raw_mul_return_wit_1_a_eq_b : raw_mul_return_wit_1_a_eq_b.
Proof.
  LLM_pre_process ltac:(lia).
  rename A_a_eq_b into A.
  assert (Hstage3 :
    raw_mul_prefix_3 aa0 aa1 aa2 aa3 aa0 aa1 aa2 aa3 =
      ar0 + ar1 * U64_MOD + ar2 * U64_MOD ^ 2 +
      ar3 * U64_MOD ^ 3 + ar4 * U64_MOD ^ 4 + ar5 * U64_MOD ^ 5).
  {
    clear - PreH113.
    cbv [Z.pow] in *.
    nia.
  }
  assert (Hlow13 : ar4 + retval = out + retval_2 * U64_MOD).
  { clear - PreH85; lia. }
  assert (Hhigh13 : ar5 + hi + retval_2 = out_2 + retval_3 * U64_MOD).
  { clear - PreH80; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      ar4 ar5 retval hi out out_2 retval_2 retval_3
      Hlow13 Hhigh13) as Hs13.
  assert (Hlow22 : out + retval_4 = out_3 + retval_5 * U64_MOD).
  { clear - PreH70; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out out_2 retval_4 hi_2 out_3 out_4 retval_5 retval_6
      Hlow22 PreH65) as Hs22.
  assert (Hlow31 : out_3 + retval_7 = out_5 + retval_8 * U64_MOD).
  { clear - PreH55; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_3 out_4 retval_7 hi_3 out_5 out_6 retval_8 retval_9
      Hlow31 PreH50) as Hs31.
  assert (Hacc13 :
    ar4 + ar5 * U64_MOD + aa1 * aa3 =
      out + out_2 * U64_MOD + retval_3 * U64_MOD ^ 2).
  { rewrite PreH90; ring_simplify in Hs13; ring_simplify; exact Hs13. }
  assert (Hacc22 :
    out + out_2 * U64_MOD + aa2 * aa2 =
      out_3 + out_4 * U64_MOD + retval_6 * U64_MOD ^ 2).
  { rewrite PreH75; ring_simplify in Hs22; ring_simplify; exact Hs22. }
  assert (Hacc31 :
    out_3 + out_4 * U64_MOD + aa3 * aa1 =
      out_5 + out_6 * U64_MOD + retval_9 * U64_MOD ^ 2).
  { rewrite PreH60; ring_simplify in Hs31; ring_simplify; exact Hs31. }
  assert (Hlow23 : out_6 + retval_10 = out_7 + retval_11 * U64_MOD).
  { clear - PreH40; lia. }
  assert (Hhigh23 :
    retval_3 + retval_6 + retval_9 + hi_4 + retval_11 =
      out_8 + retval_12 * U64_MOD).
  { clear - PreH35; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_6 (retval_3 + retval_6 + retval_9) retval_10 hi_4
      out_7 out_8 retval_11 retval_12 Hlow23 Hhigh23) as Hs23.
  assert (Hlow32 : out_7 + retval_13 = out_9 + retval_14 * U64_MOD).
  { clear - PreH25; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_7 out_8 retval_13 hi_5 out_9 out_10 retval_14 retval_15
      Hlow32 PreH20) as Hs32.
  assert (Hacc23 :
    out_6 + (retval_3 + retval_6 + retval_9) * U64_MOD + aa2 * aa3 =
      out_7 + out_8 * U64_MOD + retval_12 * U64_MOD ^ 2).
  { rewrite PreH45; ring_simplify in Hs23; ring_simplify; exact Hs23. }
  assert (Hacc32 :
    out_7 + out_8 * U64_MOD + aa3 * aa2 =
      out_9 + out_10 * U64_MOD + retval_15 * U64_MOD ^ 2).
  { rewrite PreH30; ring_simplify in Hs32; ring_simplify; exact Hs32. }
  assert (Hlow33 : out_10 + retval_16 = out_11 + retval_17 * U64_MOD).
  { clear - PreH10; lia. }
  assert (Hhigh33 :
    retval_12 + retval_15 + hi_6 + retval_17 =
      out_12 + retval_18 * U64_MOD).
  { clear - PreH5; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_10 (retval_12 + retval_15) retval_16 hi_6
      out_11 out_12 retval_17 retval_18 Hlow33 Hhigh33) as Hs33.
  assert (Hacc33 :
    out_10 + (retval_12 + retval_15) * U64_MOD + aa3 * aa3 =
      out_11 + out_12 * U64_MOD + retval_18 * U64_MOD ^ 2).
  { rewrite PreH15; ring_simplify in Hs33; ring_simplify; exact Hs33. }
  assert (Hstage6 :
    raw_mul_prefix_6 aa0 aa1 aa2 aa3 aa0 aa1 aa2 aa3 =
      u512_of_limbs ar0 ar1 ar2 ar3 out_5 out_9 out_11 out_12 +
      retval_18 * U64_MOD ^ 8).
  {
    eapply raw_mul_prefix_3_to_6_conservation;
      [exact Hstage3 | exact Hacc13 | exact Hacc22 | exact Hacc31 |
       exact Hacc23 | exact Hacc32 | exact Hacc33].
  }
  pose proof
    (raw_mul_prefix_6_bound aa0 aa1 aa2 aa3 aa0 aa1 aa2 aa3
      (conj PreH92 PreH93) (conj PreH94 PreH95)
      (conj PreH96 PreH97) (conj PreH98 PreH99)
      (conj PreH92 PreH93) (conj PreH94 PreH95)
      (conj PreH96 PreH97) (conj PreH98 PreH99))
    as Hprefix_range.
  pose proof
    (u512_of_limbs_range ar0 ar1 ar2 ar3 out_5 out_9 out_11 out_12
      (conj PreH101 PreH102) (conj PreH103 PreH104)
      (conj PreH105 PreH106) (conj PreH107 PreH108)
      (conj PreH51 PreH52) (conj PreH21 PreH22)
      (conj PreH6 PreH7) (conj PreH1 PreH2))
    as Houtput_range.
  assert (Hradix8 : U64_MOD ^ 8 = U512_MOD)
    by (cbv [U64_MOD U512_MOD]; reflexivity).
  assert (Hcarryfinal : retval_18 = 0).
  {
    clear - Hstage6 Hprefix_range Houtput_range PreH3 PreH4 Hradix8.
    rewrite Hradix8 in Hstage6.
    nia.
  }
  subst retval_18.
  simpl in Hstage6.
  assert (Hproduct :
    A * A = u512_of_limbs ar0 ar1 ar2 ar3 out_5 out_9 out_11 out_12).
  {
    clear - Hstage6 PreH100.
    rewrite PreH100.
    rewrite <- raw_mul_prefix_6_product.
    lia.
  }
  assert (Hproduct_range : 0 <= A * A < U512_MOD).
  { rewrite Hproduct; exact Houtput_range. }
  assert (Hresult_value :
    u256_of_limbs ar0 ar1 ar2 ar3 +
      u256_of_limbs out_5 out_9 out_11 out_12 * U256_MOD = A * A).
  {
    rewrite <- u512_as_u256_pair.
    symmetry.
    exact Hproduct.
  }
  clear - PreH1 PreH2 PreH6 PreH7 PreH21 PreH22 PreH51 PreH52
    PreH91 PreH92 PreH93 PreH94 PreH95 PreH96 PreH97 PreH98 PreH99
    PreH100 PreH101 PreH102 PreH103 PreH104 PreH105 PreH106 PreH107 PreH108
    Hproduct_range Hresult_value.
  split_pure_spatial.
  - rewrite <- Hresult_value.
    sep_apply_r_atomic
      (uint64_cells8_to_store_u64_limbs result_pre
        ar0 ar1 ar2 ar3 out_5 out_9 out_11 out_12
        (conj PreH101 PreH102) (conj PreH103 PreH104)
        (conj PreH105 PreH106) (conj PreH107 PreH108)
        (conj PreH51 PreH52) (conj PreH21 PreH22)
        (conj PreH6 PreH7) (conj PreH1 PreH2)).
    rewrite PreH91.
    unfold store_u256_limbs.
    Exists aa0 aa1 aa2 aa3.
    rewrite !sizeof_uint64.
    cbn.
    split_pure_spatial.
    + sepcon_assoc_change.
      cancel.
    + dump_pre_spatial.
      repeat split; try assumption; lia.
  - split_pures;
    dump_pre_spatial;
    try assumption;
    lia.
Qed.

Lemma proof_of_raw_mul_return_wit_2_non_alias : raw_mul_return_wit_2_non_alias.
Proof.
  LLM_pre_process ltac:(lia).
  rename A_non_alias into A.
  rename B_non_alias into B.
  assert (Hstage3 :
    raw_mul_prefix_3 na0 na1 na2 na3 nb0 nb1 nb2 nb3 =
      nr0 + nr1 * U64_MOD + nr2 * U64_MOD ^ 2 +
      nr3 * U64_MOD ^ 3 + nr4 * U64_MOD ^ 4 + nr5 * U64_MOD ^ 5).
  {
    clear - PreH121.
    cbv [Z.pow] in *.
    nia.
  }
  assert (Hlow13 : nr4 + retval = out + retval_2 * U64_MOD).
  { clear - PreH85; lia. }
  assert (Hhigh13 : nr5 + hi + retval_2 = out_2 + retval_3 * U64_MOD).
  { clear - PreH80; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      nr4 nr5 retval hi out out_2 retval_2 retval_3
      Hlow13 Hhigh13) as Hs13.
  assert (Hlow22 : out + retval_4 = out_3 + retval_5 * U64_MOD).
  { clear - PreH70; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out out_2 retval_4 hi_2 out_3 out_4 retval_5 retval_6
      Hlow22 PreH65) as Hs22.
  assert (Hlow31 : out_3 + retval_7 = out_5 + retval_8 * U64_MOD).
  { clear - PreH55; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_3 out_4 retval_7 hi_3 out_5 out_6 retval_8 retval_9
      Hlow31 PreH50) as Hs31.
  assert (Hacc13 :
    nr4 + nr5 * U64_MOD + na1 * nb3 =
      out + out_2 * U64_MOD + retval_3 * U64_MOD ^ 2).
  { rewrite PreH90; ring_simplify in Hs13; ring_simplify; exact Hs13. }
  assert (Hacc22 :
    out + out_2 * U64_MOD + na2 * nb2 =
      out_3 + out_4 * U64_MOD + retval_6 * U64_MOD ^ 2).
  { rewrite PreH75; ring_simplify in Hs22; ring_simplify; exact Hs22. }
  assert (Hacc31 :
    out_3 + out_4 * U64_MOD + na3 * nb1 =
      out_5 + out_6 * U64_MOD + retval_9 * U64_MOD ^ 2).
  { rewrite PreH60; ring_simplify in Hs31; ring_simplify; exact Hs31. }
  assert (Hlow23 : out_6 + retval_10 = out_7 + retval_11 * U64_MOD).
  { clear - PreH40; lia. }
  assert (Hhigh23 :
    retval_3 + retval_6 + retval_9 + hi_4 + retval_11 =
      out_8 + retval_12 * U64_MOD).
  { clear - PreH35; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_6 (retval_3 + retval_6 + retval_9) retval_10 hi_4
      out_7 out_8 retval_11 retval_12 Hlow23 Hhigh23) as Hs23.
  assert (Hlow32 : out_7 + retval_13 = out_9 + retval_14 * U64_MOD).
  { clear - PreH25; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_7 out_8 retval_13 hi_5 out_9 out_10 retval_14 retval_15
      Hlow32 PreH20) as Hs32.
  assert (Hacc23 :
    out_6 + (retval_3 + retval_6 + retval_9) * U64_MOD + na2 * nb3 =
      out_7 + out_8 * U64_MOD + retval_12 * U64_MOD ^ 2).
  { rewrite PreH45; ring_simplify in Hs23; ring_simplify; exact Hs23. }
  assert (Hacc32 :
    out_7 + out_8 * U64_MOD + na3 * nb2 =
      out_9 + out_10 * U64_MOD + retval_15 * U64_MOD ^ 2).
  { rewrite PreH30; ring_simplify in Hs32; ring_simplify; exact Hs32. }
  assert (Hlow33 : out_10 + retval_16 = out_11 + retval_17 * U64_MOD).
  { clear - PreH10; lia. }
  assert (Hhigh33 :
    retval_12 + retval_15 + hi_6 + retval_17 =
      out_12 + retval_18 * U64_MOD).
  { clear - PreH5; lia. }
  pose proof
    (radix_add2_conservation U64_MOD
      out_10 (retval_12 + retval_15) retval_16 hi_6
      out_11 out_12 retval_17 retval_18 Hlow33 Hhigh33) as Hs33.
  assert (Hacc33 :
    out_10 + (retval_12 + retval_15) * U64_MOD + na3 * nb3 =
      out_11 + out_12 * U64_MOD + retval_18 * U64_MOD ^ 2).
  { rewrite PreH15; ring_simplify in Hs33; ring_simplify; exact Hs33. }
  assert (Hstage6 :
    raw_mul_prefix_6 na0 na1 na2 na3 nb0 nb1 nb2 nb3 =
      u512_of_limbs nr0 nr1 nr2 nr3 out_5 out_9 out_11 out_12 +
      retval_18 * U64_MOD ^ 8).
  {
    eapply raw_mul_prefix_3_to_6_conservation;
      [exact Hstage3 | exact Hacc13 | exact Hacc22 | exact Hacc31 |
       exact Hacc23 | exact Hacc32 | exact Hacc33].
  }
  pose proof
    (raw_mul_prefix_6_bound na0 na1 na2 na3 nb0 nb1 nb2 nb3
      (conj PreH91 PreH92) (conj PreH93 PreH94)
      (conj PreH95 PreH96) (conj PreH97 PreH98)
      (conj PreH99 PreH100) (conj PreH101 PreH102)
      (conj PreH103 PreH104) (conj PreH105 PreH106))
    as Hprefix_range.
  pose proof
    (u512_of_limbs_range nr0 nr1 nr2 nr3 out_5 out_9 out_11 out_12
      (conj PreH109 PreH110) (conj PreH111 PreH112)
      (conj PreH113 PreH114) (conj PreH115 PreH116)
      (conj PreH51 PreH52) (conj PreH21 PreH22)
      (conj PreH6 PreH7) (conj PreH1 PreH2))
    as Houtput_range.
  assert (Hradix8 : U64_MOD ^ 8 = U512_MOD)
    by (cbv [U64_MOD U512_MOD]; reflexivity).
  assert (Hcarryfinal : retval_18 = 0).
  {
    clear - Hstage6 Hprefix_range Houtput_range PreH3 PreH4 Hradix8.
    rewrite Hradix8 in Hstage6.
    nia.
  }
  subst retval_18.
  simpl in Hstage6.
  assert (Hproduct :
    A * B = u512_of_limbs nr0 nr1 nr2 nr3 out_5 out_9 out_11 out_12).
  {
    clear - Hstage6 PreH107 PreH108.
    rewrite PreH107, PreH108.
    rewrite <- raw_mul_prefix_6_product.
    lia.
  }
  assert (Hproduct_range : 0 <= A * B < U512_MOD).
  { rewrite Hproduct; exact Houtput_range. }
  assert (Hresult_value :
    u256_of_limbs nr0 nr1 nr2 nr3 +
      u256_of_limbs out_5 out_9 out_11 out_12 * U256_MOD = A * B).
  {
    rewrite <- u512_as_u256_pair.
    symmetry.
    exact Hproduct.
  }
  clear - PreH1 PreH2 PreH6 PreH7 PreH21 PreH22 PreH51 PreH52
    PreH91 PreH92 PreH93 PreH94 PreH95 PreH96 PreH97 PreH98
    PreH99 PreH100 PreH101 PreH102 PreH103 PreH104 PreH105 PreH106
    PreH107 PreH108 PreH109 PreH110 PreH111 PreH112 PreH113 PreH114
    PreH115 PreH116 Hproduct_range Hresult_value.
  split_pure_spatial.
  - rewrite <- Hresult_value.
    sep_apply_r_atomic
      (uint64_cells8_to_store_u64_limbs result_pre
        nr0 nr1 nr2 nr3 out_5 out_9 out_11 out_12
        (conj PreH109 PreH110) (conj PreH111 PreH112)
        (conj PreH113 PreH114) (conj PreH115 PreH116)
        (conj PreH51 PreH52) (conj PreH21 PreH22)
        (conj PreH6 PreH7) (conj PreH1 PreH2)).
    unfold store_u256_limbs.
    Exists na0 na1 na2 na3 nb0 nb1 nb2 nb3.
    rewrite !sizeof_uint64.
    cbn.
    split_pure_spatial.
    + sepcon_assoc_change.
      cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: repeat split.
      all: try assumption.
      all: lia.
  - split_pures;
    dump_pre_spatial;
    lia.
Qed.

Lemma proof_of_raw_mul_partial_solve_wit_53_a_eq_b_pure_split_goal_1 : raw_mul_partial_solve_wit_53_a_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_mul_partial_solve_wit_53_a_eq_b_pure : raw_mul_partial_solve_wit_53_a_eq_b_pure.
Proof.
  LLM_pre_process ltac:(lia).
  split_pures.
  all: dump_pre_spatial.
  all: try lia.
  unfold U64_MOD; lia.
Qed.

Lemma proof_of_raw_mul_partial_solve_wit_55_non_alias_pure_split_goal_1 : raw_mul_partial_solve_wit_55_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_mul_partial_solve_wit_55_non_alias_pure : raw_mul_partial_solve_wit_55_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia).
  split_pures.
  all: dump_pre_spatial.
  all: try lia.
  unfold U64_MOD; lia.
Qed.

Lemma proof_of_raw_mul_partial_solve_wit_90_a_eq_b_pure_split_goal_1 : raw_mul_partial_solve_wit_90_a_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_mul_partial_solve_wit_90_a_eq_b_pure : raw_mul_partial_solve_wit_90_a_eq_b_pure.
Proof.
  LLM_pre_process ltac:(lia).
  split_pures.
  all: dump_pre_spatial.
  all: try lia.
  unfold U64_MOD; lia.
Qed.

Lemma proof_of_raw_mul_partial_solve_wit_92_non_alias_pure_split_goal_1 : raw_mul_partial_solve_wit_92_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_mul_partial_solve_wit_92_non_alias_pure : raw_mul_partial_solve_wit_92_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia).
  split_pures.
  all: dump_pre_spatial.
  all: try lia.
  unfold U64_MOD; lia.
Qed.

Lemma proof_of_raw_mul_partial_solve_wit_176_a_eq_b_pure_split_goal_1 : raw_mul_partial_solve_wit_176_a_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_mul_partial_solve_wit_176_a_eq_b_pure : raw_mul_partial_solve_wit_176_a_eq_b_pure.
Proof.
  LLM_pre_process ltac:(lia).
  split_pures.
  all: dump_pre_spatial.
  all: try lia.
  unfold U64_MOD; lia.
Qed.

Lemma proof_of_raw_mul_partial_solve_wit_178_non_alias_pure_split_goal_1 : raw_mul_partial_solve_wit_178_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_mul_partial_solve_wit_178_non_alias_pure : raw_mul_partial_solve_wit_178_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia).
  split_pures.
  all: dump_pre_spatial.
  all: try lia.
  unfold U64_MOD; lia.
Qed.

Lemma proof_of_raw_mul_partial_solve_wit_201_a_eq_b_pure_split_goal_1 : raw_mul_partial_solve_wit_201_a_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_mul_partial_solve_wit_201_a_eq_b_pure : raw_mul_partial_solve_wit_201_a_eq_b_pure.
Proof.
  LLM_pre_process ltac:(lia).
  split_pures.
  all: dump_pre_spatial.
  all: try lia.
  unfold U64_MOD; lia.
Qed.

Lemma proof_of_raw_mul_partial_solve_wit_203_non_alias_pure_split_goal_1 : raw_mul_partial_solve_wit_203_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_raw_mul_partial_solve_wit_203_non_alias_pure : raw_mul_partial_solve_wit_203_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia).
  split_pures.
  all: dump_pre_spatial.
  all: try lia.
  unfold U64_MOD; lia.
Qed.
