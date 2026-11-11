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
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition add_JPoint_trace_strategy10 :=
  forall (p : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul z z) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_pz2 z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy11 :=
  forall (p : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul z z) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_qz2 z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy12 :=
  forall (p : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( aj_pz2 z) z) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_pz3 z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy13 :=
  forall (p : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( aj_qz2 z) z) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_qz3 z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy14 :=
  forall (p : Z) (x : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul x ( aj_qz2 z)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_u1 x z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy15 :=
  forall (p : Z) (x : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul x ( aj_pz2 z)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_u2 x z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy16 :=
  forall (p : Z) (y : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul y ( aj_qz3 z)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_s1 y z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy17 :=
  forall (p : Z) (y : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul y ( aj_pz3 z)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_s2 y z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy18 :=
  forall (p : Z) (z2 : Z) (y1 : Z) (y2 : Z) (z1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.add ( aj_s1 y1 z2) ( aj_s2 y2 z1)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_s_sum y1 z1 y2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy19 :=
  forall (p : Z) (z2 : Z) (x1 : Z) (x2 : Z) (z1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( aj_u1 x1 z2) ( aj_u2 x2 z1)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_h x1 z1 x2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy20 :=
  forall (p : Z) (z2 : Z) (y1 : Z) (y2 : Z) (z1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( aj_s1 y1 z2) ( aj_s2 y2 z1)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_rr y1 z1 y2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy21 :=
  forall (p : Z) (z2 : Z) (x1 : Z) (x2 : Z) (z1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.add ( aj_u1 x1 z2) ( aj_u2 x2 z1)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_u_sum x1 z1 x2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy22 :=
  forall (p : Z) (z1 : Z) (z2 : Z) (y2 : Z) (y1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( aj_rr y1 z1 y2 z2) ( aj_rr y1 z1 y2 z2)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_rr2 y1 z1 y2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy23 :=
  forall (p : Z) (z1 : Z) (z2 : Z) (x2 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( aj_h x1 z1 x2 z2) ( aj_h x1 z1 x2 z2)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_h2 x1 z1 x2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy24 :=
  forall (p : Z) (z1 : Z) (z2 : Z) (x2 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( aj_u_sum x1 z1 x2 z2) ( aj_h2 x1 z1 x2 z2)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_base x1 z1 x2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy25 :=
  forall (p : Z) (z1 : Z) (z2 : Z) (y2 : Z) (y1 : Z) (x1 : Z) (x2 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( aj_rr2 y1 z1 y2 z2) ( aj_base x1 z1 x2 z2)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_rx x1 y1 z1 x2 y2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy26 :=
  forall (p : Z) (y1 : Z) (x2 : Z) (z2 : Z) (y2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.add ( aj_rx x1 y1 z1 x2 y2 z2) ( aj_rx x1 y1 z1 x2 y2 z2)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_twice_rx x1 y1 z1 x2 y2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy27 :=
  forall (p : Z) (z1 : Z) (z2 : Z) (x2 : Z) (x1 : Z) (y2 : Z) (y1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( aj_base x1 z1 x2 z2) ( aj_twice_rx x1 y1 z1 x2 y2 z2)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_base_minus_twice_rx x1 y1 z1 x2 y2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy28 :=
  forall (p : Z) (y1 : Z) (x2 : Z) (z2 : Z) (y2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( aj_base_minus_twice_rx x1 y1 z1 x2 y2 z2) ( aj_rr y1 z1 y2 z2)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_left_y x1 y1 z1 x2 y2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy29 :=
  forall (p : Z) (x2 : Z) (x1 : Z) (y1 : Z) (y2 : Z) (z2 : Z) (z1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( Zmod (Z.mul ( aj_s_sum y1 z1 y2 z2) ( aj_h2 x1 z1 x2 z2)) ( SM2_P_Z)) ( aj_h x1 z1 x2 z2)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_right_y x1 y1 z1 x2 y2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy30 :=
  forall (p : Z) (y1 : Z) (x2 : Z) (z2 : Z) (y2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( aj_left_y x1 y1 z1 x2 y2 z2) ( aj_right_y x1 y1 z1 x2 y2 z2)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_y_num x1 y1 z1 x2 y2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy31 :=
  forall (p : Z) (y1 : Z) (x2 : Z) (z2 : Z) (y2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( aj_y_num x1 y1 z1 x2 y2 z2) ( SM2_P_INV2_Z)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_ry x1 y1 z1 x2 y2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy33 :=
  forall (p : Z) (z2 : Z) (z1 : Z) (x1 : Z) (x2 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( aj_zbase z1 z2) ( aj_h x1 z1 x2 z2)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_rz x1 z1 x2 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy32 :=
  forall (p : Z) (z1 : Z) (z2 : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul z1 z2) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( aj_zbase z1 z2)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy34 :=
  forall (z1 : Z) (x1 : Z) (P1 : ec_point) (x2 : Z) (z2 : Z) (P2 : ec_point) (y2 : Z) (y1 : Z),
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (jpoint_represents x2 y2 z2 P2) ”) &&
    (“ (x1 = 1) ”) &&
    (“ (y1 = 1) ”) &&
    (“ (z1 = 0) ”) &&
    emp
    |--
    (
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (jpoint_represents x2 y2 z2 P2) ”) &&
    (“ (x1 = 1) ”) &&
    (“ (y1 = 1) ”) &&
    (“ (z1 = 0) ”) &&
    (“ (( sm2_point_add P1 P2) = P2) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy35 :=
  forall (z2 : Z) (x2 : Z) (y1 : Z) (P1 : ec_point) (z1 : Z) (x1 : Z) (P2 : ec_point) (y2 : Z),
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (jpoint_represents x2 y2 z2 P2) ”) &&
    (“ (x2 = 1) ”) &&
    (“ (y2 = 1) ”) &&
    (“ (z2 = 0) ”) &&
    emp
    |--
    (
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (jpoint_represents x2 y2 z2 P2) ”) &&
    (“ (x2 = 1) ”) &&
    (“ (y2 = 1) ”) &&
    (“ (z2 = 0) ”) &&
    (“ (( sm2_point_add P1 P2) = P1) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition add_JPoint_trace_strategy36 :=
  forall (y : Z) (z : Z) (x : Z) (P : ec_point),
    TT &&
    (“ (jpoint_represents x y z P) ”) &&
    (“ (jpoint_canonical_infinity_encoding x y z P) ”) &&
    (“ (aj_noncanonical_infinity x y z) ”) &&
    emp
    |--
    (
    TT &&
    (“ (jpoint_represents x y z P) ”) &&
    (“ (jpoint_canonical_infinity_encoding x y z P) ”) &&
    (“ (aj_noncanonical_infinity x y z) ”) &&
    (“ (z <> 0) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type add_JPoint_trace_Strategy_Correct.

  Axiom add_JPoint_trace_strategy10_correctness : add_JPoint_trace_strategy10.
  Axiom add_JPoint_trace_strategy11_correctness : add_JPoint_trace_strategy11.
  Axiom add_JPoint_trace_strategy12_correctness : add_JPoint_trace_strategy12.
  Axiom add_JPoint_trace_strategy13_correctness : add_JPoint_trace_strategy13.
  Axiom add_JPoint_trace_strategy14_correctness : add_JPoint_trace_strategy14.
  Axiom add_JPoint_trace_strategy15_correctness : add_JPoint_trace_strategy15.
  Axiom add_JPoint_trace_strategy16_correctness : add_JPoint_trace_strategy16.
  Axiom add_JPoint_trace_strategy17_correctness : add_JPoint_trace_strategy17.
  Axiom add_JPoint_trace_strategy18_correctness : add_JPoint_trace_strategy18.
  Axiom add_JPoint_trace_strategy19_correctness : add_JPoint_trace_strategy19.
  Axiom add_JPoint_trace_strategy20_correctness : add_JPoint_trace_strategy20.
  Axiom add_JPoint_trace_strategy21_correctness : add_JPoint_trace_strategy21.
  Axiom add_JPoint_trace_strategy22_correctness : add_JPoint_trace_strategy22.
  Axiom add_JPoint_trace_strategy23_correctness : add_JPoint_trace_strategy23.
  Axiom add_JPoint_trace_strategy24_correctness : add_JPoint_trace_strategy24.
  Axiom add_JPoint_trace_strategy25_correctness : add_JPoint_trace_strategy25.
  Axiom add_JPoint_trace_strategy26_correctness : add_JPoint_trace_strategy26.
  Axiom add_JPoint_trace_strategy27_correctness : add_JPoint_trace_strategy27.
  Axiom add_JPoint_trace_strategy28_correctness : add_JPoint_trace_strategy28.
  Axiom add_JPoint_trace_strategy29_correctness : add_JPoint_trace_strategy29.
  Axiom add_JPoint_trace_strategy30_correctness : add_JPoint_trace_strategy30.
  Axiom add_JPoint_trace_strategy31_correctness : add_JPoint_trace_strategy31.
  Axiom add_JPoint_trace_strategy33_correctness : add_JPoint_trace_strategy33.
  Axiom add_JPoint_trace_strategy32_correctness : add_JPoint_trace_strategy32.
  Axiom add_JPoint_trace_strategy34_correctness : add_JPoint_trace_strategy34.
  Axiom add_JPoint_trace_strategy35_correctness : add_JPoint_trace_strategy35.
  Axiom add_JPoint_trace_strategy36_correctness : add_JPoint_trace_strategy36.

End add_JPoint_trace_Strategy_Correct.
