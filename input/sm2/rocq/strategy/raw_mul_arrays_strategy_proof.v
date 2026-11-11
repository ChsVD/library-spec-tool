Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import raw_mul_arrays_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma raw_mul_arrays_strategy1_correctness : raw_mul_arrays_strategy1.
Proof.
  pre_process_default.
  match goal with
  | |- _ |-- ?Q =>
      change
        (UInt64Array.mixed_full p 8
          (Some x0 :: Some x1 :: Some x2 ::
           None :: None :: None :: None :: None :: nil)
         |-- Q)
  end.
  rewrite UInt64Array.mixed_full_unfold.
  rewrite UInt64Array.mixed_seg_unfold.
  rewrite UInt64Array.mixed_seg_unfold.
  simpl UInt64Array.mixedstoreA.
  sep_apply UInt64Array.mixed_seg_to_undef_seg.
  cancel.
  replace (1 + 1 + 1) with 3 by lia.
  cancel.
Qed.

Lemma raw_mul_arrays_strategy2_correctness : raw_mul_arrays_strategy2.
Proof.
  pre_process_default.
  subst j.
  Intros.
  subst w.
  cancel.
Qed.

Lemma raw_mul_arrays_strategy3_correctness : raw_mul_arrays_strategy3.
Proof.
  pre_process_default.
  Intros_p Hvw.
  subst q.
  subst j.
  subst w.
  cancel.
Qed.
