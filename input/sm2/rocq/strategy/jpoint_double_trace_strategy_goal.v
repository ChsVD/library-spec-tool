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
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Require Import SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition jpoint_double_trace_strategy12 :=
  forall (p : Z) (y : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( jdouble_trace_s2 y) ( jdouble_trace_s2 y)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_m4 y)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy13 :=
  forall (p : Z) (y : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( jdouble_trace_m4 y) ( jdouble_trace_m4 y)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_t16 y)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy14 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( jdouble_trace_m4 y) x) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_s4 x y)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy15 :=
  forall (p : Z) (y : Z),
    TT &&
    emp **
    ((store_fp p ( fp_div2 ( jdouble_trace_t16 y))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_t8 y)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy16 :=
  forall (p : Z) (z : Z) (x : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.add ( jdouble_trace_z2 z) x) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_sum x z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy17 :=
  forall (p : Z) (x : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub x ( jdouble_trace_z2 z)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_diff x z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy18 :=
  forall (p : Z) (z : Z) (x : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( jdouble_trace_sum x z) ( jdouble_trace_diff x z)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_prod x z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy19 :=
  forall (p : Z) (x : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul 3 ( jdouble_trace_prod x z)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_slope x z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy20 :=
  forall (p : Z) (z : Z) (x : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( jdouble_trace_slope x z) ( jdouble_trace_slope x z)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_slope_sq x z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy21 :=
  forall (p : Z) (x : Z) (y : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul 2 ( jdouble_trace_s4 x y)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_u8 x y)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy22 :=
  forall (p : Z) (z : Z) (x : Z) (y : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( jdouble_trace_slope_sq x z) ( jdouble_trace_u8 x y)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_rx x y z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy23 :=
  forall (p : Z) (y : Z) (x : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( jdouble_trace_s4 x y) ( jdouble_trace_rx x y z)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_tmp x y z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy24 :=
  forall (p : Z) (y : Z) (z : Z) (x : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul ( jdouble_trace_tmp x y z) ( jdouble_trace_slope x z)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_tmp2 x y z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy25 :=
  forall (p : Z) (y : Z) (z : Z) (x : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.sub ( jdouble_trace_tmp2 x y z) ( jdouble_trace_t8 y)) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_ry x y z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy30 :=
  forall (p : Z) (y : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul 2 y) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_s2 y)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy31 :=
  forall (p : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( Zmod (Z.mul z z) ( SM2_P_Z))))
    |--
    (
    TT &&
    emp **
    ((store_fp p ( jdouble_trace_z2 z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy112 :=
  forall (y : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( jdouble_trace_s2 y) ( jdouble_trace_s2 y)))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_m4 y)) ”) &&
    (“ (Z.lt ( jdouble_trace_m4 y) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_m4 y))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy113 :=
  forall (y : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( jdouble_trace_m4 y) ( jdouble_trace_m4 y)))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_t16 y)) ”) &&
    (“ (Z.lt ( jdouble_trace_t16 y) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_t16 y))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy114 :=
  forall (y : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( jdouble_trace_m4 y) x))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_s4 x y)) ”) &&
    (“ (Z.lt ( jdouble_trace_s4 x y) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_s4 x y))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy115 :=
  forall (y : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p ( fp_div2 ( jdouble_trace_t16 y)))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_t8 y)) ”) &&
    (“ (Z.lt ( jdouble_trace_t8 y) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_t8 y))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy116 :=
  forall (z : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.add x ( jdouble_trace_z2 z)))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_sum x z)) ”) &&
    (“ (Z.lt ( jdouble_trace_sum x z) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_sum x z))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy117 :=
  forall (z : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.sub x ( jdouble_trace_z2 z)))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_diff x z)) ”) &&
    (“ (Z.lt ( jdouble_trace_diff x z) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_diff x z))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy118 :=
  forall (z : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( jdouble_trace_diff x z) ( jdouble_trace_sum x z)))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_prod x z)) ”) &&
    (“ (Z.lt ( jdouble_trace_prod x z) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_prod x z))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy119 :=
  forall (z : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul 3 ( jdouble_trace_prod x z)))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_slope x z)) ”) &&
    (“ (Z.lt ( jdouble_trace_slope x z) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_slope x z))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy120 :=
  forall (z : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( jdouble_trace_slope x z) ( jdouble_trace_slope x z)))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_slope_sq x z)) ”) &&
    (“ (Z.lt ( jdouble_trace_slope_sq x z) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_slope_sq x z))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy121 :=
  forall (y : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul 2 ( jdouble_trace_s4 x y)))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_u8 x y)) ”) &&
    (“ (Z.lt ( jdouble_trace_u8 x y) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_u8 x y))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy122 :=
  forall (y : Z) (z : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.sub ( jdouble_trace_slope_sq x z) ( jdouble_trace_u8 x y)))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_rx x y z)) ”) &&
    (“ (Z.lt ( jdouble_trace_rx x y z) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_rx x y z))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy123 :=
  forall (y : Z) (z : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.sub ( jdouble_trace_s4 x y) ( jdouble_trace_rx x y z)))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_tmp x y z)) ”) &&
    (“ (Z.lt ( jdouble_trace_tmp x y z) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_tmp x y z))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy124 :=
  forall (y : Z) (z : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( jdouble_trace_slope x z) ( jdouble_trace_tmp x y z)))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_tmp2 x y z)) ”) &&
    (“ (Z.lt ( jdouble_trace_tmp2 x y z) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_tmp2 x y z))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy125 :=
  forall (y : Z) (z : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.sub ( jdouble_trace_tmp2 x y z) ( jdouble_trace_t8 y)))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_ry x y z)) ”) &&
    (“ (Z.lt ( jdouble_trace_ry x y z) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_ry x y z))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy130 :=
  forall (y : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul 2 y))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_s2 y)) ”) &&
    (“ (Z.lt ( jdouble_trace_s2 y) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_s2 y))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition jpoint_double_trace_strategy131 :=
  forall (z : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul z z))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( jdouble_trace_z2 z)) ”) &&
    (“ (Z.lt ( jdouble_trace_z2 z) ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp p ( mont_p ( jdouble_trace_z2 z))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type jpoint_double_trace_Strategy_Correct.

  Axiom jpoint_double_trace_strategy12_correctness : jpoint_double_trace_strategy12.
  Axiom jpoint_double_trace_strategy13_correctness : jpoint_double_trace_strategy13.
  Axiom jpoint_double_trace_strategy14_correctness : jpoint_double_trace_strategy14.
  Axiom jpoint_double_trace_strategy15_correctness : jpoint_double_trace_strategy15.
  Axiom jpoint_double_trace_strategy16_correctness : jpoint_double_trace_strategy16.
  Axiom jpoint_double_trace_strategy17_correctness : jpoint_double_trace_strategy17.
  Axiom jpoint_double_trace_strategy18_correctness : jpoint_double_trace_strategy18.
  Axiom jpoint_double_trace_strategy19_correctness : jpoint_double_trace_strategy19.
  Axiom jpoint_double_trace_strategy20_correctness : jpoint_double_trace_strategy20.
  Axiom jpoint_double_trace_strategy21_correctness : jpoint_double_trace_strategy21.
  Axiom jpoint_double_trace_strategy22_correctness : jpoint_double_trace_strategy22.
  Axiom jpoint_double_trace_strategy23_correctness : jpoint_double_trace_strategy23.
  Axiom jpoint_double_trace_strategy24_correctness : jpoint_double_trace_strategy24.
  Axiom jpoint_double_trace_strategy25_correctness : jpoint_double_trace_strategy25.
  Axiom jpoint_double_trace_strategy30_correctness : jpoint_double_trace_strategy30.
  Axiom jpoint_double_trace_strategy31_correctness : jpoint_double_trace_strategy31.
  Axiom jpoint_double_trace_strategy112_correctness : jpoint_double_trace_strategy112.
  Axiom jpoint_double_trace_strategy113_correctness : jpoint_double_trace_strategy113.
  Axiom jpoint_double_trace_strategy114_correctness : jpoint_double_trace_strategy114.
  Axiom jpoint_double_trace_strategy115_correctness : jpoint_double_trace_strategy115.
  Axiom jpoint_double_trace_strategy116_correctness : jpoint_double_trace_strategy116.
  Axiom jpoint_double_trace_strategy117_correctness : jpoint_double_trace_strategy117.
  Axiom jpoint_double_trace_strategy118_correctness : jpoint_double_trace_strategy118.
  Axiom jpoint_double_trace_strategy119_correctness : jpoint_double_trace_strategy119.
  Axiom jpoint_double_trace_strategy120_correctness : jpoint_double_trace_strategy120.
  Axiom jpoint_double_trace_strategy121_correctness : jpoint_double_trace_strategy121.
  Axiom jpoint_double_trace_strategy122_correctness : jpoint_double_trace_strategy122.
  Axiom jpoint_double_trace_strategy123_correctness : jpoint_double_trace_strategy123.
  Axiom jpoint_double_trace_strategy124_correctness : jpoint_double_trace_strategy124.
  Axiom jpoint_double_trace_strategy125_correctness : jpoint_double_trace_strategy125.
  Axiom jpoint_double_trace_strategy130_correctness : jpoint_double_trace_strategy130.
  Axiom jpoint_double_trace_strategy131_correctness : jpoint_double_trace_strategy131.

End jpoint_double_trace_Strategy_Correct.
