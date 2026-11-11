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

Definition montg_add_jpoint_and_apoint_result_strategy1 :=
  forall (y1 : Z) (z1 : Z) (y2 : Z) (P2 : ec_point) (P1 : ec_point) (x2 : Z) (x1 : Z),
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (afpoint_represents x2 y2 P2) ”) &&
    (“ (P1 <> ( ECInfinity)) ”) &&
    (“ (P2 <> ( ECInfinity)) ”) &&
    (“ (( mont_p ( maja_h x1 x2 z1)) = 0) ”) &&
    (“ (( mont_p ( maja_r y1 y2 z1)) = 0) ”) &&
    emp
    |--
    (
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (afpoint_represents x2 y2 P2) ”) &&
    (“ (P1 = P2) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition montg_add_jpoint_and_apoint_result_strategy2 :=
  forall (y1 : Z) (z1 : Z) (y2 : Z) (P2 : ec_point) (P1 : ec_point) (x2 : Z) (x1 : Z),
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (afpoint_represents x2 y2 P2) ”) &&
    (“ (P1 <> ( ECInfinity)) ”) &&
    (“ (P2 <> ( ECInfinity)) ”) &&
    (“ (( mont_p ( maja_h x1 x2 z1)) = 0) ”) &&
    (“ (( mont_p ( maja_r y1 y2 z1)) <> 0) ”) &&
    emp
    |--
    (
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (afpoint_represents x2 y2 P2) ”) &&
    (“ (( sm2_point_add P1 P2) = ( ECInfinity)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition montg_add_jpoint_and_apoint_result_strategy3 :=
  forall (x1 : Z) (z1 : Z) (x2 : Z) (P1 : ec_point) (y1 : Z) (y2 : Z) (P2 : ec_point),
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (afpoint_represents x2 y2 P2) ”) &&
    (“ (P1 <> ( ECInfinity)) ”) &&
    (“ (P2 <> ( ECInfinity)) ”) &&
    (“ (( mont_p ( maja_h x1 x2 z1)) <> 0) ”) &&
    emp
    |--
    (
    TT &&
    (“ (jpoint_represents x1 y1 z1 P1) ”) &&
    (“ (afpoint_represents x2 y2 P2) ”) &&
    (“ (jpoint_represents ( maja_rx x1 y1 z1 x2 y2) ( maja_ry x1 y1 z1 x2 y2) ( maja_rz x1 x2 z1) ( sm2_point_add P1 P2)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type montg_add_jpoint_and_apoint_result_Strategy_Correct.

  Axiom montg_add_jpoint_and_apoint_result_strategy1_correctness : montg_add_jpoint_and_apoint_result_strategy1.
  Axiom montg_add_jpoint_and_apoint_result_strategy2_correctness : montg_add_jpoint_and_apoint_result_strategy2.
  Axiom montg_add_jpoint_and_apoint_result_strategy3_correctness : montg_add_jpoint_and_apoint_result_strategy3.

End montg_add_jpoint_and_apoint_result_Strategy_Correct.
