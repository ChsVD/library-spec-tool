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

Definition montg_add_jpoint_x_strategy1 :=
  forall (p : Z) (x1 : Z) (z2 : Z) (z1 : Z) (x2 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( mont_p ( aj_u1 x1 z2)) ( mont_p ( aj_u2 x2 z1))) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_h x1 z1 x2 z2))))
    ).

Definition montg_add_jpoint_x_strategy2 :=
  forall (p : Z) (y1 : Z) (z2 : Z) (z1 : Z) (y2 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( mont_p ( aj_s1 y1 z2)) ( mont_p ( aj_s2 y2 z1))) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_rr y1 z1 y2 z2))))
    ).

Definition montg_add_jpoint_x_strategy3 :=
  forall (p : Z) (x1 : Z) (z2 : Z) (z1 : Z) (x2 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.add ( mont_p ( aj_u1 x1 z2)) ( mont_p ( aj_u2 x2 z1))) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_u_sum x1 z1 x2 z2))))
    ).

Definition montg_add_jpoint_x_strategy4 :=
  forall (p : Z) (y1 : Z) (z2 : Z) (z1 : Z) (y2 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.add ( mont_p ( aj_s1 y1 z2)) ( mont_p ( aj_s2 y2 z1))) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_s_sum y1 z1 y2 z2))))
    ).

Definition montg_add_jpoint_x_strategy5 :=
  forall (p : Z) (z1 : Z) (z2 : Z) (x2 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( aj_h x1 z1 x2 z2) ( aj_h x1 z1 x2 z2)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_h2 x1 z1 x2 z2))))
    ).

Definition montg_add_jpoint_x_strategy6 :=
  forall (p : Z) (z1 : Z) (z2 : Z) (x2 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( aj_u_sum x1 z1 x2 z2) ( aj_h2 x1 z1 x2 z2)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_base x1 z1 x2 z2))))
    ).

Definition montg_add_jpoint_x_strategy7 :=
  forall (p : Z) (z1 : Z) (z2 : Z) (y2 : Z) (y1 : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( aj_rr y1 z1 y2 z2) ( aj_rr y1 z1 y2 z2)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_rr2 y1 z1 y2 z2))))
    ).

Definition montg_add_jpoint_x_strategy8 :=
  forall (p : Z) (y1 : Z) (y2 : Z) (z2 : Z) (z1 : Z) (x2 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( mont_p ( aj_rr2 y1 z1 y2 z2)) ( mont_p ( aj_base x1 z1 x2 z2))) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_rx x1 y1 z1 x2 y2 z2))))
    ).

Definition montg_add_jpoint_x_strategy9 :=
  forall (p : Z) (y1 : Z) (x2 : Z) (z2 : Z) (y2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul 2 ( mont_p ( aj_rx x1 y1 z1 x2 y2 z2))) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_twice_rx x1 y1 z1 x2 y2 z2))))
    ).

Definition montg_add_jpoint_x_strategy10 :=
  forall (p : Z) (x1 : Z) (x2 : Z) (z2 : Z) (z1 : Z) (y1 : Z) (y2 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( mont_p ( aj_base x1 z1 x2 z2)) ( mont_p ( aj_twice_rx x1 y1 z1 x2 y2 z2))) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_base_minus_twice_rx x1 y1 z1 x2 y2 z2))))
    ).

Definition montg_add_jpoint_x_strategy101 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z1 : Z) (z2 : Z) (x2 : Z) (x1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_h x1 z1 x2 z2)) ”) &&
    (“ (Z.lt ( aj_h x1 z1 x2 z2) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_x_strategy102 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z1 : Z) (z2 : Z) (y2 : Z) (y1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_rr y1 z1 y2 z2)) ”) &&
    (“ (Z.lt ( aj_rr y1 z1 y2 z2) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_x_strategy103 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z1 : Z) (z2 : Z) (x2 : Z) (x1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_u_sum x1 z1 x2 z2)) ”) &&
    (“ (Z.lt ( aj_u_sum x1 z1 x2 z2) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_x_strategy104 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z1 : Z) (z2 : Z) (y2 : Z) (y1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_s_sum y1 z1 y2 z2)) ”) &&
    (“ (Z.lt ( aj_s_sum y1 z1 y2 z2) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_x_strategy105 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z1 : Z) (z2 : Z) (x2 : Z) (x1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_h2 x1 z1 x2 z2)) ”) &&
    (“ (Z.lt ( aj_h2 x1 z1 x2 z2) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_x_strategy106 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z1 : Z) (z2 : Z) (x2 : Z) (x1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_base x1 z1 x2 z2)) ”) &&
    (“ (Z.lt ( aj_base x1 z1 x2 z2) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_x_strategy107 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z1 : Z) (z2 : Z) (y2 : Z) (y1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_rr2 y1 z1 y2 z2)) ”) &&
    (“ (Z.lt ( aj_rr2 y1 z1 y2 z2) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_x_strategy108 :=
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
    (“ (Z.le 0 ( aj_rx x1 y1 z1 x2 y2 z2)) ”) &&
    (“ (Z.lt ( aj_rx x1 y1 z1 x2 y2 z2) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_x_strategy109 :=
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
    (“ (Z.le 0 ( aj_twice_rx x1 y1 z1 x2 y2 z2)) ”) &&
    (“ (Z.lt ( aj_twice_rx x1 y1 z1 x2 y2 z2) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_x_strategy110 :=
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
    (“ (Z.le 0 ( aj_base_minus_twice_rx x1 y1 z1 x2 y2 z2)) ”) &&
    (“ (Z.lt ( aj_base_minus_twice_rx x1 y1 z1 x2 y2 z2) ( SM2_P_Z)) ”) &&
    emp
    ).

Module Type montg_add_jpoint_x_Strategy_Correct.

  Axiom montg_add_jpoint_x_strategy1_correctness : montg_add_jpoint_x_strategy1.
  Axiom montg_add_jpoint_x_strategy2_correctness : montg_add_jpoint_x_strategy2.
  Axiom montg_add_jpoint_x_strategy3_correctness : montg_add_jpoint_x_strategy3.
  Axiom montg_add_jpoint_x_strategy4_correctness : montg_add_jpoint_x_strategy4.
  Axiom montg_add_jpoint_x_strategy5_correctness : montg_add_jpoint_x_strategy5.
  Axiom montg_add_jpoint_x_strategy6_correctness : montg_add_jpoint_x_strategy6.
  Axiom montg_add_jpoint_x_strategy7_correctness : montg_add_jpoint_x_strategy7.
  Axiom montg_add_jpoint_x_strategy8_correctness : montg_add_jpoint_x_strategy8.
  Axiom montg_add_jpoint_x_strategy9_correctness : montg_add_jpoint_x_strategy9.
  Axiom montg_add_jpoint_x_strategy10_correctness : montg_add_jpoint_x_strategy10.
  Axiom montg_add_jpoint_x_strategy101_correctness : montg_add_jpoint_x_strategy101.
  Axiom montg_add_jpoint_x_strategy102_correctness : montg_add_jpoint_x_strategy102.
  Axiom montg_add_jpoint_x_strategy103_correctness : montg_add_jpoint_x_strategy103.
  Axiom montg_add_jpoint_x_strategy104_correctness : montg_add_jpoint_x_strategy104.
  Axiom montg_add_jpoint_x_strategy105_correctness : montg_add_jpoint_x_strategy105.
  Axiom montg_add_jpoint_x_strategy106_correctness : montg_add_jpoint_x_strategy106.
  Axiom montg_add_jpoint_x_strategy107_correctness : montg_add_jpoint_x_strategy107.
  Axiom montg_add_jpoint_x_strategy108_correctness : montg_add_jpoint_x_strategy108.
  Axiom montg_add_jpoint_x_strategy109_correctness : montg_add_jpoint_x_strategy109.
  Axiom montg_add_jpoint_x_strategy110_correctness : montg_add_jpoint_x_strategy110.

End montg_add_jpoint_x_Strategy_Correct.
