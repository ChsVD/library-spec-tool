Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_facts_strategy_goal.
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

Lemma ecc_point_facts_strategy1_correctness : ecc_point_facts_strategy1.
Proof.
  pre_process_default.
  assert (Hz : z <> 0).
  {
    intro Hz.
    subst z.
    apply H0.
    apply (proj1 (jpoint_represents_infinity_iff x y 0 point H)).
    reflexivity.
  }
  entailer!.
Qed.

Lemma ecc_point_facts_strategy2_correctness : ecc_point_facts_strategy2.
Proof.
  pre_process_default.
  assert (Hvalid : valid_afpoint x y).
  {
    apply (proj2 (valid_afpoint_iff x y)).
    exists point.
    exact H.
  }
  entailer!.
Qed.
