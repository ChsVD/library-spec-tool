Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
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

Definition montg_add_jpoint_and_apoint_y_strategy1 :=
  forall (p : Z) (x1 : Z) (z1 : Z) (x2 : Z) (y1 : Z) (y2 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( mont_p ( maja_u1h2 x1 x2 z1)) ( mont_p ( maja_rx x1 y1 z1 x2 y2))) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( maja_e_minus_rx x1 y1 z1 x2 y2))))
    ).

Definition montg_add_jpoint_and_apoint_y_strategy2 :=
  forall (p : Z) (y2 : Z) (z1 : Z) (y1 : Z) (x1 : Z) (x2 : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( maja_r y1 y2 z1) ( maja_e_minus_rx x1 y1 z1 x2 y2)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( maja_r_times_delta x1 y1 z1 x2 y2))))
    ).

Definition montg_add_jpoint_and_apoint_y_strategy3 :=
  forall (p : Z) (y1 : Z) (x1 : Z) (z1 : Z) (x2 : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul y1 ( maja_h3 x1 x2 z1)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( maja_y1h3 x1 y1 x2 z1))))
    ).

Definition montg_add_jpoint_and_apoint_y_strategy101 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (y1 : Z) (x2 : Z) (y2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( maja_e_minus_rx x1 y1 z1 x2 y2)) ”) &&
    (“ (Z.lt ( maja_e_minus_rx x1 y1 z1 x2 y2) ( SM2_P_Z)) ”) &&
    emp
    ).

Module Type montg_add_jpoint_and_apoint_y_Strategy_Correct.

  Axiom montg_add_jpoint_and_apoint_y_strategy1_correctness : montg_add_jpoint_and_apoint_y_strategy1.
  Axiom montg_add_jpoint_and_apoint_y_strategy2_correctness : montg_add_jpoint_and_apoint_y_strategy2.
  Axiom montg_add_jpoint_and_apoint_y_strategy3_correctness : montg_add_jpoint_and_apoint_y_strategy3.
  Axiom montg_add_jpoint_and_apoint_y_strategy101_correctness : montg_add_jpoint_and_apoint_y_strategy101.

End montg_add_jpoint_and_apoint_y_Strategy_Correct.
