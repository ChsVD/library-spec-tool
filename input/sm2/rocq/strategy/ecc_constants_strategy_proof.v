Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma ecc_constants_strategy10_correctness : ecc_constants_strategy10.
Proof.
  pre_process_default.
Qed.

Lemma ecc_constants_strategy13_correctness : ecc_constants_strategy13.
Proof.
  pre_process_default.
  cancel.
  Intros_p Hx.
  subst x.
  unfold store_sm2_a.
  cancel.
Qed.

Lemma ecc_constants_strategy20_correctness : ecc_constants_strategy20.
Proof.
  pre_process_default.
Qed.

Lemma ecc_constants_strategy23_correctness : ecc_constants_strategy23.
Proof.
  pre_process_default.
  cancel.
  Intros_p Hx.
  subst x.
  unfold store_sm2_b.
  cancel.
Qed.

Lemma ecc_constants_strategy30_correctness : ecc_constants_strategy30.
Proof.
  pre_process_default.
Qed.

Lemma ecc_constants_strategy33_correctness : ecc_constants_strategy33.
Proof.
  pre_process_default.
  cancel.
  Intros_p Hx.
  Intros_p Hy.
  Intros_p Hz.
  subst x; subst y; subst z.
  unfold store_jpoint_zero.
  cancel.
Qed.

Lemma ecc_constants_strategy40_correctness : ecc_constants_strategy40.
Proof.
  pre_process_default.
Qed.

Lemma ecc_constants_strategy43_correctness : ecc_constants_strategy43.
Proof.
  pre_process_default.
  cancel.
  Intros_p Hx.
  subst x.
  unfold store_sm2_inv2p.
  cancel.
Qed.

Lemma ecc_constants_strategy11_correctness : ecc_constants_strategy11.
Proof.
  pre_process_default.
Qed.

Lemma ecc_constants_strategy21_correctness : ecc_constants_strategy21.
Proof.
  pre_process_default.
Qed.

Lemma ecc_constants_strategy31_correctness : ecc_constants_strategy31.
Proof.
  pre_process_default.
Qed.

Lemma ecc_constants_strategy41_correctness : ecc_constants_strategy41.
Proof.
  pre_process_default.
Qed.
