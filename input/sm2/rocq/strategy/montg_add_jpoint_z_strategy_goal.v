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

Definition montg_add_jpoint_z_strategy1 :=
  forall (p : Z) (z1 : Z) (z2 : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul z1 z2))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_zbase z1 z2))))
    ).

Definition montg_add_jpoint_z_strategy2 :=
  forall (p : Z) (z2 : Z) (z1 : Z) (x1 : Z) (x2 : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul ( aj_zbase z1 z2) ( aj_h x1 z1 x2 z2)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_rz x1 z1 x2 z2))))
    ).

Definition montg_add_jpoint_z_strategy101 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z2 : Z) (z1 : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_zbase z1 z2)) ”) &&
    (“ (Z.lt ( aj_zbase z1 z2) ( SM2_P_Z)) ”) &&
    emp
    ).

Module Type montg_add_jpoint_z_Strategy_Correct.

  Axiom montg_add_jpoint_z_strategy1_correctness : montg_add_jpoint_z_strategy1.
  Axiom montg_add_jpoint_z_strategy2_correctness : montg_add_jpoint_z_strategy2.
  Axiom montg_add_jpoint_z_strategy101_correctness : montg_add_jpoint_z_strategy101.

End montg_add_jpoint_z_Strategy_Correct.
