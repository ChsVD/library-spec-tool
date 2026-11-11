Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_result_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.montg_add_jpoint_and_apoint_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma montg_add_jpoint_and_apoint_result_strategy1_correctness : montg_add_jpoint_and_apoint_result_strategy1.
Proof.
  pre_process_default.
  assert (Hh : maja_h x1 x2 z1 = 0).
  {
    apply (proj1 (mont_p_eq_zero_iff
      (maja_h x1 x2 z1)
      ltac:(unfold maja_h; apply maja_mod_range))).
    exact H3.
  }
  assert (Hr : maja_r y1 y2 z1 = 0).
  {
    apply (proj1 (mont_p_eq_zero_iff
      (maja_r y1 y2 z1)
      ltac:(unfold maja_r; apply maja_mod_range))).
    exact H4.
  }
  pose proof (maja_equal_points
    x1 y1 z1 x2 y2 P1 P2 H1 H2 H H0 Hh Hr) as Hequal.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_result_strategy2_correctness : montg_add_jpoint_and_apoint_result_strategy2.
Proof.
  pre_process_default.
  assert (Hh : maja_h x1 x2 z1 = 0).
  {
    apply (proj1 (mont_p_eq_zero_iff
      (maja_h x1 x2 z1)
      ltac:(unfold maja_h; apply maja_mod_range))).
    exact H3.
  }
  assert (Hr : maja_r y1 y2 z1 <> 0).
  {
    intros Hr0.
    apply H4.
    apply (proj2 (mont_p_eq_zero_iff
      (maja_r y1 y2 z1)
      ltac:(unfold maja_r; apply maja_mod_range))).
    exact Hr0.
  }
  pose proof (maja_inverse_points_add_infinity
    x1 y1 z1 x2 y2 P1 P2 H1 H2 H H0 Hh Hr) as Hinfinity.
  entailer!.
Qed.

Lemma montg_add_jpoint_and_apoint_result_strategy3_correctness : montg_add_jpoint_and_apoint_result_strategy3.
Proof.
  pre_process_default.
  assert (Hh : maja_h x1 x2 z1 <> 0).
  {
    intros Hh0.
    apply H3.
    apply (proj2 (mont_p_eq_zero_iff
      (maja_h x1 x2 z1)
      ltac:(unfold maja_h; apply maja_mod_range))).
    exact Hh0.
  }
  pose proof (maja_generic_formula_represents
    x1 y1 z1 x2 y2 P1 P2 H1 H2 H H0 Hh) as Hresult.
  entailer!.
Qed.
