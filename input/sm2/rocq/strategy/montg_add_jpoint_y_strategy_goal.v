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
Require Import SimpleC.EE.Applications_human.sm2.lib.add_JPoint_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.montg_add_jpoint_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition montg_add_jpoint_y_strategy1 :=
  forall (p : Z) (z1 : Z) (z2 : Z) (x2 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( aj_h2 x1 z1 x2 z2) ( aj_h x1 z1 x2 z2)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( Zmod (Z.mul ( aj_h2 x1 z1 x2 z2) ( aj_h x1 z1 x2 z2)) ( SM2_P_Z)))))
    ).

Definition montg_add_jpoint_y_strategy2 :=
  forall (p : Z) (z1 : Z) (z2 : Z) (y2 : Z) (y1 : Z) (x2 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( aj_s_sum y1 z1 y2 z2) ( Zmod (Z.mul ( aj_h2 x1 z1 x2 z2) ( aj_h x1 z1 x2 z2)) ( SM2_P_Z))))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_right_y x1 y1 z1 x2 y2 z2))))
    ).

Definition montg_add_jpoint_y_strategy3 :=
  forall (p : Z) (y1 : Z) (x2 : Z) (z2 : Z) (y2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( aj_base_minus_twice_rx x1 y1 z1 x2 y2 z2) ( aj_rr y1 z1 y2 z2)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_left_y x1 y1 z1 x2 y2 z2))))
    ).

Definition montg_add_jpoint_y_strategy4 :=
  forall (p : Z) (x1 : Z) (z1 : Z) (y2 : Z) (z2 : Z) (x2 : Z) (y1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( mont_p ( aj_left_y x1 y1 z1 x2 y2 z2)) ( mont_p ( aj_right_y x1 y1 z1 x2 y2 z2))) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_y_num x1 y1 z1 x2 y2 z2))))
    ).

Definition montg_add_jpoint_y_strategy5 :=
  forall (p : Z) (x1 : Z) (z1 : Z) (y2 : Z) (z2 : Z) (x2 : Z) (y1 : Z),
    TT &&
    emp **
    ((store_fp p ( fp_div2 ( mont_p ( aj_y_num x1 y1 z1 x2 y2 z2)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_ry x1 y1 z1 x2 y2 z2))))
    ).

Definition montg_add_jpoint_y_strategy101 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (x1 : Z) (x2 : Z) (z2 : Z) (z1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( Zmod (Z.mul ( aj_h2 x1 z1 x2 z2) ( aj_h x1 z1 x2 z2)) ( SM2_P_Z))) ”) &&
    (“ (Z.lt ( Zmod (Z.mul ( aj_h2 x1 z1 x2 z2) ( aj_h x1 z1 x2 z2)) ( SM2_P_Z)) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_y_strategy102 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (y1 : Z) (x2 : Z) (z2 : Z) (y2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_right_y x1 y1 z1 x2 y2 z2)) ”) &&
    (“ (Z.lt ( aj_right_y x1 y1 z1 x2 y2 z2) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_y_strategy103 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (y1 : Z) (x2 : Z) (z2 : Z) (y2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_left_y x1 y1 z1 x2 y2 z2)) ”) &&
    (“ (Z.lt ( aj_left_y x1 y1 z1 x2 y2 z2) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_y_strategy104 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (y1 : Z) (x2 : Z) (z2 : Z) (y2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_y_num x1 y1 z1 x2 y2 z2)) ”) &&
    (“ (Z.lt ( aj_y_num x1 y1 z1 x2 y2 z2) ( SM2_P_Z)) ”) &&
    emp
    ).

Module Type montg_add_jpoint_y_Strategy_Correct.

  Axiom montg_add_jpoint_y_strategy1_correctness : montg_add_jpoint_y_strategy1.
  Axiom montg_add_jpoint_y_strategy2_correctness : montg_add_jpoint_y_strategy2.
  Axiom montg_add_jpoint_y_strategy3_correctness : montg_add_jpoint_y_strategy3.
  Axiom montg_add_jpoint_y_strategy4_correctness : montg_add_jpoint_y_strategy4.
  Axiom montg_add_jpoint_y_strategy5_correctness : montg_add_jpoint_y_strategy5.
  Axiom montg_add_jpoint_y_strategy101_correctness : montg_add_jpoint_y_strategy101.
  Axiom montg_add_jpoint_y_strategy102_correctness : montg_add_jpoint_y_strategy102.
  Axiom montg_add_jpoint_y_strategy103_correctness : montg_add_jpoint_y_strategy103.
  Axiom montg_add_jpoint_y_strategy104_correctness : montg_add_jpoint_y_strategy104.

End montg_add_jpoint_y_Strategy_Correct.
