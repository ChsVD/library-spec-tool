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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import ML_mul_basepoint_def.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import ML_mul_basepoint_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import ML_mul_basepoint_proof_auto.
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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_ecc_const_table.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_basepoint_mul.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_basepoint_mul.
Local Open Scope sac.

Lemma proof_of_ML_mul_basepoint_entail_wit_3 : ML_mul_basepoint_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  csimpl.
  assert (Hzaddr :
    &( &( &( "Tr") ->ₛ "z") ->ₛ "v") =
    &( &( "Tr") ->ₛ "z" .ₛ "v")) by (csimpl; reflexivity).
  assert (Hyaddr :
    &( &( &( "Tr") ->ₛ "y") ->ₛ "v") =
    &( &( "Tr") ->ₛ "y" .ₛ "v")) by (csimpl; reflexivity).
  assert (Hxaddr :
    &( &( &( "Tr") ->ₛ "x") ->ₛ "v") =
    &( &( "Tr") ->ₛ "x" .ₛ "v")) by (csimpl; reflexivity).
  rewrite Hzaddr, Hyaddr, Hxaddr.
  sep_apply (uint64_full4_named_triplet_to_store_jpoint_fields
    "Tr" xs ys zs ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (HTzaddr :
    &( &( &( "T") ->ₛ "z") ->ₛ "v") =
    &( &( "T") ->ₛ "z" .ₛ "v")) by (csimpl; reflexivity).
  assert (HTyaddr :
    &( &( &( "T") ->ₛ "y") ->ₛ "v") =
    &( &( "T") ->ₛ "y" .ₛ "v")) by (csimpl; reflexivity).
  assert (HTxaddr :
    &( &( &( "T") ->ₛ "x") ->ₛ "v") =
    &( &( "T") ->ₛ "x" .ₛ "v")) by (csimpl; reflexivity).
  rewrite HTzaddr, HTyaddr, HTxaddr.
  sep_apply (uint64_full4_named_triplet_to_store_jpoint_fields
    "T" xs ys zs ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (H0zaddr :
    &( &( &( "JPoint_ZERO") ->ₛ "z") ->ₛ "v") =
    &( &( "JPoint_ZERO") ->ₛ "z" .ₛ "v")) by (csimpl; reflexivity).
  assert (H0yaddr :
    &( &( &( "JPoint_ZERO") ->ₛ "y") ->ₛ "v") =
    &( &( "JPoint_ZERO") ->ₛ "y" .ₛ "v")) by (csimpl; reflexivity).
  assert (H0xaddr :
    &( &( &( "JPoint_ZERO") ->ₛ "x") ->ₛ "v") =
    &( &( "JPoint_ZERO") ->ₛ "x" .ₛ "v")) by (csimpl; reflexivity).
  rewrite H0zaddr, H0yaddr, H0xaddr.
  sep_apply (uint64_full4_named_triplet_to_store_jpoint_fields
    "JPoint_ZERO" xs ys zs ltac:(lia) ltac:(lia) ltac:(lia)).
  Exists ECInfinity.
  rewrite PreH18, PreH13, PreH8.
  unfold store_jpoint_with_canonical_infinity, store_jpoint_zero.
  Exists 1 1 0.
  Exists 1 1 0.
  assert (Hprefix : sm2_scalar_prefix K_non_alias (8 * 0) = 0).
  {
    unfold sm2_scalar_prefix, SM2_BYTE_BASE.
    cbn.
    apply Z.mod_1_r.
  }
  rewrite Hprefix, sm2_point_mul_zero.
  pose proof ec_math_refinement.canonical_infinity_representation as Hinf.
  unfold jpoint_canonical_infinity_encoding in Hinf.
  rewrite (nested_jpoint_u32_v_addr_eq result_pre "x").
  rewrite (nested_jpoint_u32_v_addr_eq result_pre "y").
  rewrite (nested_jpoint_u32_v_addr_eq result_pre "z").
  entailer!.
  csimpl.
  cancel.
Qed.

Lemma proof_of_ML_mul_basepoint_entail_wit_5_split_goal_1 : ML_mul_basepoint_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cbn.
  rewrite sm2_scalar_chunk_zero, sm2_point_mul_zero.
  exact (proj1 ec_math_refinement.canonical_infinity_representation).
Qed.

Lemma proof_of_ML_mul_basepoint_entail_wit_5_split_goal_2 : ML_mul_basepoint_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cbn.
  rewrite sm2_scalar_chunk_zero, sm2_point_mul_zero.
  exact (proj2 ec_math_refinement.canonical_infinity_representation).
Qed.

Lemma proof_of_ML_mul_basepoint_entail_wit_5_split_goal_3 : ML_mul_basepoint_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  reflexivity.
Qed.

Lemma proof_of_ML_mul_basepoint_entail_wit_5_split_goal_4 : ML_mul_basepoint_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_ML_mul_basepoint_entail_wit_5_split_goal_5 : ML_mul_basepoint_entail_wit_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrep : replace_Znth 0 1 (0 :: 0 :: 0 :: 0 :: nil) =
    (1 :: 0 :: 0 :: 0 :: nil)) by reflexivity.
  rewrite Hrep.
  assert (Hone : u64_list_value (1 :: 0 :: 0 :: 0 :: nil) = 1)
    by reflexivity.
  rewrite Hone; lia.
Qed.

Lemma proof_of_ML_mul_basepoint_entail_wit_5_split_goal_6 : ML_mul_basepoint_entail_wit_5_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_ML_mul_basepoint_entail_wit_5_split_goal_7 : ML_mul_basepoint_entail_wit_5_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrep : replace_Znth 0 1 (0 :: 0 :: 0 :: 0 :: nil) =
    (1 :: 0 :: 0 :: 0 :: nil)) by reflexivity.
  rewrite Hrep.
  assert (Hone : u64_list_value (1 :: 0 :: 0 :: 0 :: nil) = 1)
    by reflexivity.
  rewrite Hone; lia.
Qed.

Lemma proof_of_ML_mul_basepoint_entail_wit_5_split_goal_8 : ML_mul_basepoint_entail_wit_5_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_ML_mul_basepoint_entail_wit_5 : ML_mul_basepoint_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrep : replace_Znth 0 1 (0 :: 0 :: 0 :: 0 :: nil) =
    (1 :: 0 :: 0 :: 0 :: nil)) by reflexivity.
  rewrite Hrep.
  repeat sep_apply uint64_full4_to_store_u256_limbs.
  assert (Hzero : u64_list_value (0 :: 0 :: 0 :: 0 :: nil) = 0)
    by reflexivity.
  assert (Hone : u64_list_value (1 :: 0 :: 0 :: 0 :: nil) = 1)
    by reflexivity.
  rewrite Hzero, Hone.
  pose proof (store_u256_limbs_named_zxy_to_store_jpoint_fields
    "T" 1 1 0
    ltac:(unfold SM2_P_Z; lia)
    ltac:(unfold SM2_P_Z; lia)
    ltac:(unfold SM2_P_Z; lia)) as Hfields.
  sep_apply_l_atomic Hfields.
  rewrite sm2_scalar_chunk_zero, sm2_point_mul_zero.
  pose proof ec_math_refinement.canonical_infinity_representation as Hinf.
  unfold jpoint_canonical_infinity_encoding in Hinf.
  sep_apply (store_jpoint_fields_to_store_jpoint_with_canonical_infinity
    &( "T") 1 1 0 ECInfinity (proj1 Hinf) (proj2 Hinf)).
  split_pure_spatial.
  - rewrite sizeof_uint64.
    replace (&( k_pre # "u32" ->ₛ "v") + 8 * i)
      with (&( k_pre # "u32" ->ₛ "v") + i * 8) by ring.
    replace (&( k_pre # "u32" ->ₛ "v") + 8 * i + 8)
      with (&( k_pre # "u32" ->ₛ "v") + (i + 1) * 8) by ring.
    cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_ML_mul_basepoint_entail_wit_6 : ML_mul_basepoint_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (sm2_inner_add_step_from_chunk K_non_alias byte_list i j
    PreH13 PreH14 PreH15 ltac:(lia) ltac:(lia)) as Hstep.
  rewrite Hstep.
  entailer!.
  apply store_uchar_undef_store_uchar.
Qed.

Lemma proof_of_ML_mul_basepoint_entail_wit_8 : ML_mul_basepoint_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj : j = 8) by lia.
  subst j.
  rewrite sm2_outer_prefix_step by lia.
  Exists (sm2_point_mul (sm2_scalar_chunk K_non_alias i 8) SM2_G_POINT).
  entailer!.
Qed.

Lemma proof_of_ML_mul_basepoint_return_wit_1 : ML_mul_basepoint_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = 4) by lia.
  subst i.
  replace (8 * 4) with 32 by lia.
  rewrite sm2_scalar_prefix_32 by lia.
  entailer!.
Qed.

Lemma proof_of_ML_mul_basepoint_which_implies_wit_1 : ML_mul_basepoint_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply (store_fn_to_u8_full32 k K_non_alias).
  Intros byte_list.
  Exists byte_list.
  entailer!.
Qed.

Lemma proof_of_ML_mul_basepoint_which_implies_wit_2_split_goal_1 : ML_mul_basepoint_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_sm2_base_point_table.
  entailer!.
Qed.

Lemma proof_of_ML_mul_basepoint_which_implies_wit_2_split_goal_spatial : ML_mul_basepoint_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_ML_mul_basepoint_which_implies_wit_2 : ML_mul_basepoint_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_sm2_base_point_table.
  entailer!.
Qed.

Lemma proof_of_ML_mul_basepoint_which_implies_wit_3_split_goal_spatial : ML_mul_basepoint_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_jpoint_fields, store_fp, store_mod, store_u256.
  Intros.
  unfold store_u256_limbs.
  Intros x0 x1 x2 x3.
  Intros y0 y1 y2 y3.
  Intros z0 z1 z2 z3.
  destruct H2 as [Hx0 [Hx1 [Hx2 [Hx3 Hx]]]].
  destruct H3 as [Hy0 [Hy1 [Hy2 [Hy3 Hy]]]].
  destruct H4 as [Hz0 [Hz1 [Hz2 [Hz3 Hz]]]].
  assert (HX : x0 = 0 /\ x1 = 0 /\ x2 = 0 /\ x3 = 0).
  {
    apply (proj1 (u256_of_limbs_eq_zero_iff__eq_zero
      x0 x1 x2 x3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    symmetry; exact Hx.
  }
  assert (HY : y0 = 0 /\ y1 = 0 /\ y2 = 0 /\ y3 = 0).
  {
    apply (proj1 (u256_of_limbs_eq_zero_iff__eq_zero
      y0 y1 y2 y3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    symmetry; exact Hy.
  }
  assert (HZ : z0 = 0 /\ z1 = 0 /\ z2 = 0 /\ z3 = 0).
  {
    apply (proj1 (u256_of_limbs_eq_zero_iff__eq_zero
      z0 z1 z2 z3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    symmetry; exact Hz.
  }
  destruct HX as [-> [-> [-> ->]]].
  destruct HY as [-> [-> [-> ->]]].
  destruct HZ as [-> [-> [-> ->]]].
  unfold UInt64Array.full, store_array.
  cbn [store_array_rec].
  rewrite !sizeof_uint64.
  rewrite (named_jpoint_u32_v_addr_eq "T" "x").
  rewrite (named_jpoint_u32_v_addr_eq "T" "y").
  rewrite (named_jpoint_u32_v_addr_eq "T" "z").
  entailer!.
  rewrite (nested_jpoint_u32_v_addr_eq &( "T") "x").
  rewrite (nested_jpoint_u32_v_addr_eq &( "T") "y").
  rewrite (nested_jpoint_u32_v_addr_eq &( "T") "z").
  entailer!.
  replace (0 + 1) with 1 by lia.
  replace (0 + 1 + 1) with 2 by lia.
  replace (0 + 1 + 1 + 1) with 3 by lia.
  cancel.
  replace (1 + 1) with 2 by lia.
  replace (1 + 1 + 1) with 3 by lia.
  cancel.
  replace (2 + 1) with 3 by lia.
  cancel.
Qed.

Lemma proof_of_ML_mul_basepoint_which_implies_wit_3 : ML_mul_basepoint_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_jpoint_fields, store_fp, store_mod, store_u256.
  Intros.
  unfold store_u256_limbs.
  Intros x0 x1 x2 x3.
  Intros y0 y1 y2 y3.
  Intros z0 z1 z2 z3.
  destruct H2 as [Hx0 [Hx1 [Hx2 [Hx3 Hx]]]].
  destruct H3 as [Hy0 [Hy1 [Hy2 [Hy3 Hy]]]].
  destruct H4 as [Hz0 [Hz1 [Hz2 [Hz3 Hz]]]].
  assert (HX : x0 = 0 /\ x1 = 0 /\ x2 = 0 /\ x3 = 0).
  {
    apply (proj1 (u256_of_limbs_eq_zero_iff__eq_zero
      x0 x1 x2 x3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    symmetry.
    exact Hx.
  }
  assert (HY : y0 = 0 /\ y1 = 0 /\ y2 = 0 /\ y3 = 0).
  {
    apply (proj1 (u256_of_limbs_eq_zero_iff__eq_zero
      y0 y1 y2 y3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    symmetry.
    exact Hy.
  }
  assert (HZ : z0 = 0 /\ z1 = 0 /\ z2 = 0 /\ z3 = 0).
  {
    apply (proj1 (u256_of_limbs_eq_zero_iff__eq_zero
      z0 z1 z2 z3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    symmetry.
    exact Hz.
  }
  destruct HX as [-> [-> [-> ->]]].
  destruct HY as [-> [-> [-> ->]]].
  destruct HZ as [-> [-> [-> ->]]].
  unfold UInt64Array.full, store_array.
  cbn [store_array_rec].
  rewrite !sizeof_uint64.
  rewrite (named_jpoint_u32_v_addr_eq "T" "x").
  rewrite (named_jpoint_u32_v_addr_eq "T" "y").
  rewrite (named_jpoint_u32_v_addr_eq "T" "z").
  entailer!.
  rewrite (nested_jpoint_u32_v_addr_eq &( "T") "x").
  rewrite (nested_jpoint_u32_v_addr_eq &( "T") "y").
  rewrite (nested_jpoint_u32_v_addr_eq &( "T") "z").
  entailer!.
  replace (0 + 1) with 1 by lia.
  replace (0 + 1 + 1) with 2 by lia.
  replace (0 + 1 + 1 + 1) with 3 by lia.
  cancel.
  replace (1 + 1) with 2 by lia.
  replace (1 + 1 + 1) with 3 by lia.
  cancel.
  replace (2 + 1) with 3 by lia.
  cancel.
Qed.

Lemma proof_of_ML_mul_basepoint_which_implies_wit_4_split_goal_1 : ML_mul_basepoint_which_implies_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byte.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (j + 8 * i)).
  assert (0 <= j + 8 * i < Zlength byte_list)
    by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2; lia.
Qed.

Lemma proof_of_ML_mul_basepoint_which_implies_wit_4_split_goal_2 : ML_mul_basepoint_which_implies_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byte.
  rewrite Znth_sublist by lia.
  unfold u8_list_bounded, limb_list_bounded in PreH2.
  specialize (PreH2 (j + 8 * i)).
  assert (0 <= j + 8 * i < Zlength byte_list)
    by (rewrite PreH1; lia).
  specialize (PreH2 H).
  unfold SM2_BYTE_BASE in PreH2; lia.
Qed.

Lemma proof_of_ML_mul_basepoint_which_implies_wit_4 : ML_mul_basepoint_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byte.
  entailer!.
  all: rewrite Znth_sublist by lia.
  all: unfold u8_list_bounded, limb_list_bounded in PreH2.
  all: specialize (PreH2 (j + 8 * i)).
  all: assert (0 <= j + 8 * i < Zlength byte_list)
    by (rewrite PreH1; lia).
  all: specialize (PreH2 H).
  all: unfold SM2_BYTE_BASE in PreH2; lia.
Qed.

Lemma proof_of_ML_mul_basepoint_which_implies_wit_5_split_goal_1 : ML_mul_basepoint_which_implies_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : _ /\ _ |- _ => destruct H as [Hchunk Hterm]
  end.
  subst byte.
  rewrite (sm2_table_term_from_chunk K_non_alias byte_list i j)
    by (try assumption; lia).
  rewrite <- sm2_point_mul_add.
  - apply (sm2_inner_sum_noninfinity K_non_alias i j).
    + lia.
    + lia.
    + lia.
    + left; exact Hchunk.
  - exact (proj1
      (sm2_scalar_chunk_bounds K_non_alias i j ltac:(lia) ltac:(lia))).
  - exact (proj1
      (sm2_scalar_term_bounds K_non_alias i j ltac:(lia) ltac:(lia))).
Qed.

Lemma proof_of_ML_mul_basepoint_which_implies_wit_5_split_goal_2 : ML_mul_basepoint_which_implies_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : _ /\ _ |- _ => destruct H as [Hchunk Hterm]
  end.
  subst byte.
  rewrite (sm2_table_term_from_chunk K_non_alias byte_list i j)
    by (try assumption; lia).
  rewrite (sm2_table_term_from_chunk K_non_alias byte_list i j) in Hterm
    by (try assumption; lia).
  apply (sm2_inner_points_distinct K_non_alias i j).
  - lia.
  - lia.
  - lia.
  - exact Hchunk.
  - exact Hterm.
Qed.

Lemma proof_of_ML_mul_basepoint_which_implies_wit_5 : ML_mul_basepoint_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst byte.
  rewrite (sm2_table_term_from_chunk K_non_alias byte_list i j)
    by (try assumption; lia).
  assert (Hdistinct :
    sm2_point_mul (sm2_scalar_chunk K_non_alias i j) SM2_G_POINT <>
      ECInfinity /\
    sm2_point_mul (sm2_scalar_term K_non_alias i j) SM2_G_POINT <>
      ECInfinity ->
    sm2_point_mul (sm2_scalar_chunk K_non_alias i j) SM2_G_POINT <>
    sm2_point_mul (sm2_scalar_term K_non_alias i j) SM2_G_POINT).
  {
    intros [Hchunk Hterm].
    apply (sm2_inner_points_distinct K_non_alias i j).
    - lia.
    - lia.
    - lia.
    - exact Hchunk.
    - exact Hterm.
  }
  assert (Hsafe :
    sm2_point_mul (sm2_scalar_chunk K_non_alias i j) SM2_G_POINT <>
      ECInfinity /\
    sm2_point_mul (sm2_scalar_term K_non_alias i j) SM2_G_POINT <>
      ECInfinity ->
    sm2_point_add
      (sm2_point_mul (sm2_scalar_chunk K_non_alias i j) SM2_G_POINT)
      (sm2_point_mul (sm2_scalar_term K_non_alias i j) SM2_G_POINT) <>
    ECInfinity).
  {
    intros [Hchunk Hterm].
    rewrite <- sm2_point_mul_add.
    - apply (sm2_inner_sum_noninfinity K_non_alias i j).
      + lia.
      + lia.
      + lia.
      + left; exact Hchunk.
    - exact (proj1
        (sm2_scalar_chunk_bounds K_non_alias i j ltac:(lia) ltac:(lia))).
    - exact (proj1
        (sm2_scalar_term_bounds K_non_alias i j ltac:(lia) ltac:(lia))).
  }
  entailer!.
Qed.

Lemma proof_of_ML_mul_basepoint_which_implies_wit_6_split_goal_spatial : ML_mul_basepoint_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_sm2_base_point_table.
  entailer!.
Qed.

Lemma proof_of_ML_mul_basepoint_which_implies_wit_6 : ML_mul_basepoint_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_sm2_base_point_table.
  entailer!.
Qed.

Lemma proof_of_add_JPoint_and_AFPoint_derive_canonical_finite_guard_r_eq_point1_by_canonical_r_eq_point1 : add_JPoint_and_AFPoint_derive_canonical_finite_guard_r_eq_point1_by_canonical_r_eq_point1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists P1_canonical_finite_guard_r_eq_point1
    P2_canonical_finite_guard_r_eq_point1.
  apply sepcon_cancel_end.
  - destruct (sm2_ec_point_dec
      P1_canonical_finite_guard_r_eq_point1 ECInfinity) as [HP1 | HP1].
    + Left. Left. entailer!.
    + destruct (sm2_ec_point_dec
        P2_canonical_finite_guard_r_eq_point1 ECInfinity) as [HP2 | HP2].
      * Left. Right. entailer!.
      * Right. entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    entailer!.
Qed.
