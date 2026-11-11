Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_ecc_const_table.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_protocol.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sm2_protocol_views_strategy1_correctness : sm2_protocol_views_strategy1.
Proof.
  pre_process_default.
  subst q. Intros; subst. entailer!.
Qed.

Lemma sm2_protocol_views_strategy2_correctness : sm2_protocol_views_strategy2.
Proof.
  pre_process_default.
  subst q.
  unfold store_sm2_private_key.
  entailer!.
  pre_process_default.
  Intros_p Hd; subst required_d; cancel.
Qed.

Lemma sm2_protocol_views_strategy4_correctness : sm2_protocol_views_strategy4.
Proof.
  pre_process_default.
  subst q. entailer!.
Qed.

Lemma sm2_protocol_views_strategy5_correctness : sm2_protocol_views_strategy5.
Proof.
  pre_process_default.
  subst q. unfold undef_sm2_private_key. entailer!.
Qed.

Lemma sm2_protocol_views_strategy7_correctness : sm2_protocol_views_strategy7.
Proof.
  pre_process_default.
  subst q.
  unfold undef_sm2_private_key, UndefStructPredu32.
  entailer!.
Qed.

Lemma sm2_protocol_views_strategy10_correctness : sm2_protocol_views_strategy10.
Proof.
  pre_process_default.
  subst q. Intros; subst. entailer!.
Qed.

Lemma sm2_protocol_views_strategy11_correctness : sm2_protocol_views_strategy11.
Proof.
  pre_process_default.
  subst q. unfold store_sm2_signature.
  entailer!.
  pre_process_default. Intros_p Hr; subst required_r; cancel.
Qed.

Lemma sm2_protocol_views_strategy12_correctness : sm2_protocol_views_strategy12.
Proof.
  pre_process_default.
  subst q. unfold store_sm2_signature.
  entailer!.
  pre_process_default. Intros_p Hs; subst required_s; cancel.
Qed.

Lemma sm2_protocol_views_strategy14_correctness : sm2_protocol_views_strategy14.
Proof.
  pre_process_default.
  subst q. entailer!.
Qed.

Lemma sm2_protocol_views_strategy20_correctness : sm2_protocol_views_strategy20.
Proof.
  pre_process_default.
  subst q. Intros; subst. entailer!.
Qed.

Lemma sm2_protocol_views_strategy21_correctness : sm2_protocol_views_strategy21.
Proof.
  pre_process_default.
  subst q. unfold store_sm2_public_key.
  entailer!.
  pre_process_default. Intros_p Hp; subst required_point; cancel.
Qed.

Lemma sm2_protocol_views_strategy30_correctness : sm2_protocol_views_strategy30.
Proof.
  pre_process_default.
  subst q. Intros; subst. entailer!.
Qed.

Lemma sm2_protocol_views_strategy31_correctness : sm2_protocol_views_strategy31.
Proof.
  pre_process_default.
  subst q. unfold store_sm2_za.
  entailer!.
  pre_process_default. Intros_p Hza; subst required_za; cancel.
Qed.

Lemma sm2_protocol_views_strategy40_correctness : sm2_protocol_views_strategy40.
Proof.
  pre_process_default.
Qed.

Lemma sm2_protocol_views_strategy50_correctness : sm2_protocol_views_strategy50.
Proof.
  pre_process_default.
Qed.

Lemma sm2_protocol_views_strategy60_correctness : sm2_protocol_views_strategy60.
Proof.
  pre_process_default.
Qed.

Lemma sm2_protocol_views_strategy63_correctness : sm2_protocol_views_strategy63.
Proof.
  pre_process_default.
Qed.

Lemma sm2_protocol_views_strategy70_correctness : sm2_protocol_views_strategy70.
Proof.
  pre_process_default.
Qed.

Lemma sm2_protocol_views_strategy80_correctness : sm2_protocol_views_strategy80.
Proof.
  pre_process_default.
Qed.

Lemma sm2_protocol_views_strategy90_correctness : sm2_protocol_views_strategy90.
Proof.
  pre_process_default.
Qed.

Lemma sm2_protocol_views_strategy100_correctness : sm2_protocol_views_strategy100.
Proof.
  pre_process_default.
Qed.

Lemma sm2_protocol_views_strategy15_correctness : sm2_protocol_views_strategy15.
Proof.
  pre_process_default; try (unfold undef_sm2_signature; entailer!).
Qed.

Lemma sm2_protocol_views_strategy41_correctness : sm2_protocol_views_strategy41.
Proof.
  pre_process_default;
    try (unfold store_sm2_get_public_key_globals; entailer!).
Qed.

Lemma sm2_protocol_views_strategy51_correctness : sm2_protocol_views_strategy51.
Proof.
  pre_process_default;
    try (unfold store_sm2_keypair_globals,
      store_sm2_get_public_key_globals; entailer!).
Qed.

Lemma sm2_protocol_views_strategy61_correctness : sm2_protocol_views_strategy61.
Proof.
  pre_process_default; try (unfold store_sm2_za_globals; entailer!).
Qed.

Lemma sm2_protocol_views_strategy64_correctness : sm2_protocol_views_strategy64.
Proof.
  pre_process_default; try (unfold store_sm2_g; entailer!).
Qed.

Lemma sm2_protocol_views_strategy71_correctness : sm2_protocol_views_strategy71.
Proof.
  pre_process_default;
    try (unfold store_sm2_sign_dgst_globals; entailer!).
Qed.

Lemma sm2_protocol_views_strategy81_correctness : sm2_protocol_views_strategy81.
Proof.
  pre_process_default;
    try (unfold store_sm2_sign_globals, store_sm2_za_globals,
      store_sm2_sign_dgst_globals; entailer!).
Qed.

Lemma sm2_protocol_views_strategy91_correctness : sm2_protocol_views_strategy91.
Proof.
  pre_process_default;
    try (unfold store_sm2_verify_dgst_globals; entailer!).
Qed.

Lemma sm2_protocol_views_strategy101_correctness : sm2_protocol_views_strategy101.
Proof.
  pre_process_default;
    try (unfold store_sm2_verify_globals,
      store_sm2_verify_dgst_globals; entailer!).
Qed.

Lemma sm2_protocol_views_strategy3_correctness : sm2_protocol_views_strategy3.
Proof.
  pre_process_default; try (unfold store_sm2_private_key; entailer!).
Qed.

Lemma sm2_protocol_views_strategy6_correctness : sm2_protocol_views_strategy6.
Proof.
  pre_process_default; try (unfold undef_sm2_private_key; entailer!).
Qed.

Lemma sm2_protocol_views_strategy13_correctness : sm2_protocol_views_strategy13.
Proof.
  pre_process_default.
  Intros_r required_s.
  apply_sepcon_adjoint.
  unfold store_sm2_signature.
  entailer!.
Qed.

Lemma sm2_protocol_views_strategy16_correctness : sm2_protocol_views_strategy16.
Proof.
  pre_process_default; try (unfold undef_sm2_signature; entailer!).
Qed.

Lemma sm2_protocol_views_strategy22_correctness : sm2_protocol_views_strategy22.
Proof.
  pre_process_default; try (unfold store_sm2_public_key; entailer!).
Qed.

Lemma sm2_protocol_views_strategy23_correctness : sm2_protocol_views_strategy23.
Proof.
  pre_process_default; try (unfold store_sm2_public_key; entailer!).
Qed.

Lemma sm2_protocol_views_strategy32_correctness : sm2_protocol_views_strategy32.
Proof.
  pre_process_default; try (unfold store_sm2_za; entailer!).
Qed.

Lemma sm2_protocol_views_strategy42_correctness : sm2_protocol_views_strategy42.
Proof.
  pre_process_default;
    try (unfold store_sm2_get_public_key_globals; entailer!).
Qed.

Lemma sm2_protocol_views_strategy52_correctness : sm2_protocol_views_strategy52.
Proof.
  pre_process_default;
    try (unfold store_sm2_keypair_globals,
      store_sm2_get_public_key_globals; entailer!).
Qed.

Lemma sm2_protocol_views_strategy62_correctness : sm2_protocol_views_strategy62.
Proof.
  pre_process_default; try (unfold store_sm2_za_globals; entailer!).
Qed.

Lemma sm2_protocol_views_strategy65_correctness : sm2_protocol_views_strategy65.
Proof.
  pre_process_default; try (unfold store_sm2_g; entailer!).
Qed.

Lemma sm2_protocol_views_strategy72_correctness : sm2_protocol_views_strategy72.
Proof.
  pre_process_default;
    try (unfold store_sm2_sign_dgst_globals; entailer!).
Qed.

Lemma sm2_protocol_views_strategy82_correctness : sm2_protocol_views_strategy82.
Proof.
  pre_process_default;
    try (unfold store_sm2_sign_globals, store_sm2_za_globals,
      store_sm2_sign_dgst_globals; entailer!).
Qed.

Lemma sm2_protocol_views_strategy92_correctness : sm2_protocol_views_strategy92.
Proof.
  pre_process_default;
    try (unfold store_sm2_verify_dgst_globals; entailer!).
Qed.

Lemma sm2_protocol_views_strategy102_correctness : sm2_protocol_views_strategy102.
Proof.
  pre_process_default;
    try (unfold store_sm2_verify_globals,
      store_sm2_verify_dgst_globals; entailer!).
Qed.

Lemma sm2_protocol_views_strategy24_correctness : sm2_protocol_views_strategy24.
Proof.
  pre_process_default.
  pose proof
    (afpoint_represents_sm2_point_coordinates x y point H)
    as [Hx Hy].
  entailer!.
Qed.
