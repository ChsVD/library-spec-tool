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

Definition montg_add_jpoint_result_strategy1 :=
  forall (y1 : Z) (z2 : Z) (z1 : Z) (y2 : Z) (P2 : ec_point) (P1 : ec_point) (x2 : Z) (x1 : Z),
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (jpoint_represents x2 y2 z2 P2) ”) &&
    (“ (z1 <> 0) ”) &&
    (“ (z2 <> 0) ”) &&
    (“ (( mont_p ( aj_u1 x1 z2)) = ( mont_p ( aj_u2 x2 z1))) ”) &&
    (“ (( mont_p ( aj_s1 y1 z2)) = ( mont_p ( aj_s2 y2 z1))) ”) &&
    emp
    |--
    (
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (jpoint_represents x2 y2 z2 P2) ”) &&
    (“ (P1 = P2) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition montg_add_jpoint_result_strategy2 :=
  forall (x1 : Z) (z2 : Z) (z1 : Z) (x2 : Z) (y1 : Z) (P1 : ec_point) (P2 : ec_point) (y2 : Z),
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (jpoint_represents x2 y2 z2 P2) ”) &&
    (“ (z1 <> 0) ”) &&
    (“ (z2 <> 0) ”) &&
    (“ (( mont_p ( aj_u1 x1 z2)) <> ( mont_p ( aj_u2 x2 z1))) ”) &&
    emp
    |--
    (
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (jpoint_represents x2 y2 z2 P2) ”) &&
    (“ (jpoint_represents ( aj_rx x1 y1 z1 x2 y2 z2) ( aj_ry x1 y1 z1 x2 y2 z2) ( aj_rz x1 z1 x2 z2) ( sm2_point_add P1 P2)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition montg_add_jpoint_result_strategy3 :=
  forall (y1 : Z) (z2 : Z) (z1 : Z) (y2 : Z) (P2 : ec_point) (P1 : ec_point) (x2 : Z) (x1 : Z),
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (jpoint_represents x2 y2 z2 P2) ”) &&
    (“ (z1 <> 0) ”) &&
    (“ (z2 <> 0) ”) &&
    (“ (( mont_p ( aj_u1 x1 z2)) = ( mont_p ( aj_u2 x2 z1))) ”) &&
    (“ (( mont_p ( aj_s1 y1 z2)) <> ( mont_p ( aj_s2 y2 z1))) ”) &&
    emp
    |--
    (
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (jpoint_represents x2 y2 z2 P2) ”) &&
    (“ (jpoint_represents ( aj_rx x1 y1 z1 x2 y2 z2) ( aj_ry x1 y1 z1 x2 y2 z2) ( aj_rz x1 z1 x2 z2) ( sm2_point_add P1 P2)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type montg_add_jpoint_result_Strategy_Correct.

  Axiom montg_add_jpoint_result_strategy1_correctness : montg_add_jpoint_result_strategy1.
  Axiom montg_add_jpoint_result_strategy2_correctness : montg_add_jpoint_result_strategy2.
  Axiom montg_add_jpoint_result_strategy3_correctness : montg_add_jpoint_result_strategy3.

End montg_add_jpoint_result_Strategy_Correct.
