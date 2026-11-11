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

Definition montg_add_jpoint_and_apoint_precompute_strategy1 :=
  forall (p : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul z z))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( maja_z2 z))))
    ).

Definition montg_add_jpoint_and_apoint_precompute_strategy2 :=
  forall (p : Z) (x : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul x ( maja_z2 z)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( maja_u2 x z))))
    ).

Definition montg_add_jpoint_and_apoint_precompute_strategy3 :=
  forall (p : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul z ( maja_z2 z)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( maja_z3 z))))
    ).

Definition montg_add_jpoint_and_apoint_precompute_strategy4 :=
  forall (p : Z) (y : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul y ( maja_z3 z)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( maja_s2 y z))))
    ).

Definition montg_add_jpoint_and_apoint_precompute_strategy101 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( maja_z2 z)) ”) &&
    (“ (Z.lt ( maja_z2 z) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_and_apoint_precompute_strategy103 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( maja_z3 z)) ”) &&
    (“ (Z.lt ( maja_z3 z) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_and_apoint_precompute_strategy105 :=
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
    (“ (Z.le 0 ( maja_h x1 x2 z1)) ”) &&
    (“ (Z.lt ( maja_h x1 x2 z1) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_and_apoint_precompute_strategy106 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (y2 : Z) (z1 : Z) (y1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( maja_r y1 y2 z1)) ”) &&
    (“ (Z.lt ( maja_r y1 y2 z1) ( SM2_P_Z)) ”) &&
    emp
    ).

Module Type montg_add_jpoint_and_apoint_precompute_Strategy_Correct.

  Axiom montg_add_jpoint_and_apoint_precompute_strategy1_correctness : montg_add_jpoint_and_apoint_precompute_strategy1.
  Axiom montg_add_jpoint_and_apoint_precompute_strategy2_correctness : montg_add_jpoint_and_apoint_precompute_strategy2.
  Axiom montg_add_jpoint_and_apoint_precompute_strategy3_correctness : montg_add_jpoint_and_apoint_precompute_strategy3.
  Axiom montg_add_jpoint_and_apoint_precompute_strategy4_correctness : montg_add_jpoint_and_apoint_precompute_strategy4.
  Axiom montg_add_jpoint_and_apoint_precompute_strategy101_correctness : montg_add_jpoint_and_apoint_precompute_strategy101.
  Axiom montg_add_jpoint_and_apoint_precompute_strategy103_correctness : montg_add_jpoint_and_apoint_precompute_strategy103.
  Axiom montg_add_jpoint_and_apoint_precompute_strategy105_correctness : montg_add_jpoint_and_apoint_precompute_strategy105.
  Axiom montg_add_jpoint_and_apoint_precompute_strategy106_correctness : montg_add_jpoint_and_apoint_precompute_strategy106.

End montg_add_jpoint_and_apoint_precompute_Strategy_Correct.
