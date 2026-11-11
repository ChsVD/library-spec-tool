Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import wnaf3_predicate_cancellation_strategy_goal.
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

Lemma wnaf3_predicate_cancellation_strategy1_correctness : wnaf3_predicate_cancellation_strategy1.
Proof.
  unfold wnaf3_predicate_cancellation_strategy1.
  intros.
  Intros_p Hpositive.
  Intros_p Hnegative.
  subst required_positive; subst required_negative.
  entailer!.
  apply_sepcon_adjoint.
  entailer!.
Qed.

Lemma wnaf3_predicate_cancellation_strategy2_correctness : wnaf3_predicate_cancellation_strategy2.
Proof.
  unfold wnaf3_predicate_cancellation_strategy2.
  intros.
  Intros_p Hpositive.
  Intros_p Hnegative.
  Intros_p Hpoint.
  subst required_positive; subst required_negative; subst required_point.
  entailer!.
  apply_sepcon_adjoint.
  entailer!.
Qed.

Lemma wnaf3_predicate_cancellation_strategy3_correctness : wnaf3_predicate_cancellation_strategy3.
Proof.
  unfold wnaf3_predicate_cancellation_strategy3.
  intros.
  Intros_p Hpositive.
  Intros_p Hnegative.
  subst required_positive; subst required_negative.
  entailer!.
  apply_sepcon_adjoint.
  entailer!.
Qed.

Lemma wnaf3_predicate_cancellation_strategy4_correctness : wnaf3_predicate_cancellation_strategy4.
Proof.
  unfold wnaf3_predicate_cancellation_strategy4.
  intros.
  Intros_p Haddress.
  Intros_p Hlength.
  subst required_address; subst required_length.
  entailer!.
  apply_sepcon_adjoint.
  entailer!.
Qed.

Lemma wnaf3_predicate_cancellation_strategy5_correctness : wnaf3_predicate_cancellation_strategy5.
Proof.
  unfold wnaf3_predicate_cancellation_strategy5.
  intros.
  Intros_p Haddress.
  Intros_p Hlength.
  Intros_p Hdigits.
  subst required_address; subst required_length; subst required_digits.
  entailer!.
  apply_sepcon_adjoint.
  entailer!.
Qed.

Lemma wnaf3_predicate_cancellation_strategy6_correctness : wnaf3_predicate_cancellation_strategy6.
Proof.
  unfold wnaf3_predicate_cancellation_strategy6.
  intros.
  Intros_p Haddress.
  Intros_p Hstart.
  Intros_p Hdigits.
  Intros_p Hbase_point.
  subst required_address; subst required_start; subst required_digits;
    subst required_base_point.
  entailer!.
  apply_sepcon_adjoint.
  entailer!.
Qed.

Lemma wnaf3_predicate_cancellation_strategy7_correctness : wnaf3_predicate_cancellation_strategy7.
Proof.
  unfold wnaf3_predicate_cancellation_strategy7.
  intros.
  Intros_p Haddress.
  Intros_p Hpoint.
  subst required_address; subst required_point.
  entailer!.
  apply_sepcon_adjoint.
  entailer!.
Qed.

Lemma wnaf3_predicate_cancellation_strategy8_correctness : wnaf3_predicate_cancellation_strategy8.
Proof.
  unfold wnaf3_predicate_cancellation_strategy8.
  intros.
  Intros_p Hpoint_value.
  Intros_p Haddress.
  Intros_p Hstart.
  Intros_p Hdigits.
  Intros_p Hbase_point.
  subst required_address; subst required_start; subst required_digits;
    subst required_base_point; subst point.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.
