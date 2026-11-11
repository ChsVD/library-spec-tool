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

Definition montg_add_jpoint_and_apoint_x_strategy1 :=
  forall (p : Z) (x2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( maja_h x1 x2 z1) ( maja_h x1 x2 z1)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( maja_h2 x1 x2 z1))))
    ).

Definition montg_add_jpoint_and_apoint_x_strategy2 :=
  forall (p : Z) (x2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( maja_h x1 x2 z1) ( maja_h2 x1 x2 z1)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( maja_h3 x1 x2 z1))))
    ).

Definition montg_add_jpoint_and_apoint_x_strategy3 :=
  forall (p : Z) (x1 : Z) (z1 : Z) (x2 : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul x1 ( maja_h2 x1 x2 z1)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( maja_u1h2 x1 x2 z1))))
    ).

Definition montg_add_jpoint_and_apoint_x_strategy4 :=
  forall (p : Z) (x2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul 2 ( mont_p ( maja_u1h2 x1 x2 z1))) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( maja_two_u1h2 x1 x2 z1))))
    ).

Definition montg_add_jpoint_and_apoint_x_strategy5 :=
  forall (p : Z) (x1 : Z) (z1 : Z) (x2 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.add ( mont_p ( maja_h3 x1 x2 z1)) ( mont_p ( maja_two_u1h2 x1 x2 z1))) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( maja_x_adjust x1 x2 z1))))
    ).

Definition montg_add_jpoint_and_apoint_x_strategy6 :=
  forall (p : Z) (y2 : Z) (z1 : Z) (y1 : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( maja_r y1 y2 z1) ( maja_r y1 y2 z1)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( maja_r2 y1 y2 z1))))
    ).

Definition montg_add_jpoint_and_apoint_x_strategy7 :=
  forall (p : Z) (y1 : Z) (z1 : Z) (y2 : Z) (x2 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( mont_p ( maja_r2 y1 y2 z1)) ( mont_p ( maja_x_adjust x1 x2 z1))) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( maja_rx x1 y1 z1 x2 y2))))
    ).

Definition montg_add_jpoint_and_apoint_x_strategy101 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (x2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( maja_h2 x1 x2 z1)) ”) &&
    (“ (Z.lt ( maja_h2 x1 x2 z1) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_and_apoint_x_strategy102 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (x2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( maja_h3 x1 x2 z1)) ”) &&
    (“ (Z.lt ( maja_h3 x1 x2 z1) ( SM2_P_Z)) ”) &&
    emp
    ).

Module Type montg_add_jpoint_and_apoint_x_Strategy_Correct.

  Axiom montg_add_jpoint_and_apoint_x_strategy1_correctness : montg_add_jpoint_and_apoint_x_strategy1.
  Axiom montg_add_jpoint_and_apoint_x_strategy2_correctness : montg_add_jpoint_and_apoint_x_strategy2.
  Axiom montg_add_jpoint_and_apoint_x_strategy3_correctness : montg_add_jpoint_and_apoint_x_strategy3.
  Axiom montg_add_jpoint_and_apoint_x_strategy4_correctness : montg_add_jpoint_and_apoint_x_strategy4.
  Axiom montg_add_jpoint_and_apoint_x_strategy5_correctness : montg_add_jpoint_and_apoint_x_strategy5.
  Axiom montg_add_jpoint_and_apoint_x_strategy6_correctness : montg_add_jpoint_and_apoint_x_strategy6.
  Axiom montg_add_jpoint_and_apoint_x_strategy7_correctness : montg_add_jpoint_and_apoint_x_strategy7.
  Axiom montg_add_jpoint_and_apoint_x_strategy101_correctness : montg_add_jpoint_and_apoint_x_strategy101.
  Axiom montg_add_jpoint_and_apoint_x_strategy102_correctness : montg_add_jpoint_and_apoint_x_strategy102.

End montg_add_jpoint_and_apoint_x_Strategy_Correct.
