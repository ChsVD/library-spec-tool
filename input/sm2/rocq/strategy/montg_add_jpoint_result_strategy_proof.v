Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_result_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import SimpleC.EE.Applications_human.sm2.lib.add_JPoint_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.montg_add_jpoint_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma montg_add_jpoint_result_strategy1_correctness : montg_add_jpoint_result_strategy1.
Proof.
  pre_process_default.
  assert (HP : P1 = P2).
  {
    eapply montg_add_equal_points;
    eassumption.
  }
  entailer!.
Qed.

Lemma montg_add_jpoint_result_strategy2_correctness : montg_add_jpoint_result_strategy2.
Proof.
  pre_process_default.
  pose proof (montg_add_generic_formula_represents
    x1 y1 z1 x2 y2 z2 P1 P2 H H0 H1 H2 (or_introl H3)) as Hresult.
  entailer!.
Qed.

Lemma montg_add_jpoint_result_strategy3_correctness : montg_add_jpoint_result_strategy3.
Proof.
  pre_process_default.
  pose proof (montg_add_generic_formula_represents
    x1 y1 z1 x2 y2 z2 P1 P2 H H0 H1 H2
      (or_intror (conj H3 H4))) as Hresult.
  entailer!.
Qed.
