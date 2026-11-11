Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma ecc_montg_helper_views_strategy10_correctness : ecc_montg_helper_views_strategy10.
  pre_process_default.
  unfold store_u256.
  replace
    (&(p # "u32" ->ₛ "v") + 0 * sizeof(UINT64))
    with (&(p # "u32" ->ₛ "v")) by lia.
  entailer!.
Qed.

Lemma ecc_montg_helper_views_strategy11_correctness : ecc_montg_helper_views_strategy11.
  pre_process_default.
  unfold store_u256_limbs.
  Intros x0 x1 x2 x3.
  Exists x0 x1 x2 x3.
  simpl.
  pre_process_default.
Qed.

Lemma ecc_montg_helper_views_strategy20_correctness : ecc_montg_helper_views_strategy20.
  pre_process_default.
  unfold store_fp, store_mod, store_u256.
  rewrite u32_v_field_address_eq.
  unfold store_u256_limbs at 1.
  Intros x0 x1 x2 x3.
  apply split_pure_and_spatial_goals.
  - unfold store_u256_limbs.
    Exists x0 x1 x2 x3.
    entailer!.
  - destruct H0 as [? [? [? [? ->]]]].
    pose proof (u256_of_limbs_range x0 x1 x2 x3 H0 H1 H2 H3).
    entailer!; lia.
Qed.

Lemma ecc_montg_helper_views_strategy21_correctness : ecc_montg_helper_views_strategy21.
  pre_process_default.
  unfold store_fn, store_mod, store_u256.
  rewrite u32_v_field_address_eq.
  unfold store_u256_limbs at 1.
  Intros x0 x1 x2 x3.
  apply split_pure_and_spatial_goals.
  - unfold store_u256_limbs.
    Exists x0 x1 x2 x3.
    entailer!.
  - destruct H0 as [? [? [? [? ->]]]].
    pose proof (u256_of_limbs_range x0 x1 x2 x3 H0 H1 H2 H3).
    entailer!; lia.
Qed.

Lemma ecc_montg_helper_views_strategy30_correctness : ecc_montg_helper_views_strategy30.
  unfold ecc_montg_helper_views_strategy30.
  intros.
  unfold store_fp, store_mod, store_u256.
  rewrite u32_v_field_address_eq.
  entailer!.
  apply_sepcon_adjoint.
  entailer!.
Qed.

Lemma ecc_montg_helper_views_strategy31_correctness : ecc_montg_helper_views_strategy31.
  unfold ecc_montg_helper_views_strategy31.
  intros.
  unfold store_fn, store_mod, store_u256.
  rewrite u32_v_field_address_eq.
  entailer!.
  apply_sepcon_adjoint.
  entailer!.
Qed.

Lemma ecc_montg_helper_views_strategy32_correctness : ecc_montg_helper_views_strategy32.
  pre_process_default.
  unfold store_fp, store_mod, store_u256.
  rewrite u32_v_field_address_eq.
  entailer!.
Qed.

Lemma ecc_montg_helper_views_strategy40_correctness : ecc_montg_helper_views_strategy40.
  pre_process_default.
  unfold UndefStructPredu32.
  rewrite u32_v_field_address_eq.
  entailer!.
Qed.
