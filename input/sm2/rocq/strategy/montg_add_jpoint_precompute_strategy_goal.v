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

Definition montg_add_jpoint_precompute_strategy1 :=
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
    ((store_fp p ( mont_p ( aj_pz2 z))))
    ).

Definition montg_add_jpoint_precompute_strategy2 :=
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
    ((store_fp p ( mont_p ( aj_qz2 z))))
    ).

Definition montg_add_jpoint_precompute_strategy3 :=
  forall (p : Z) (x : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul x ( aj_qz2 z)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_u1 x z))))
    ).

Definition montg_add_jpoint_precompute_strategy4 :=
  forall (p : Z) (x : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul x ( aj_pz2 z)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_u2 x z))))
    ).

Definition montg_add_jpoint_precompute_strategy5 :=
  forall (p : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul z ( aj_pz2 z)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_pz3 z))))
    ).

Definition montg_add_jpoint_precompute_strategy6 :=
  forall (p : Z) (y : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul y ( aj_pz3 z)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_s2 y z))))
    ).

Definition montg_add_jpoint_precompute_strategy7 :=
  forall (p : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul z ( aj_qz2 z)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_qz3 z))))
    ).

Definition montg_add_jpoint_precompute_strategy8 :=
  forall (p : Z) (y : Z) (z : Z),
    TT &&
    emp **
    ((store_fp p ( mont_p (Z.mul y ( aj_qz3 z)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_fp p ( mont_p ( aj_s1 y z))))
    ).

Definition montg_add_jpoint_precompute_strategy101 :=
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
    (“ (Z.le 0 ( aj_pz2 z)) ”) &&
    (“ (Z.lt ( aj_pz2 z) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_precompute_strategy102 :=
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
    (“ (Z.le 0 ( aj_qz2 z)) ”) &&
    (“ (Z.lt ( aj_qz2 z) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_precompute_strategy103 :=
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
    (“ (Z.le 0 ( aj_pz3 z)) ”) &&
    (“ (Z.lt ( aj_pz3 z) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_precompute_strategy104 :=
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
    (“ (Z.le 0 ( aj_qz3 z)) ”) &&
    (“ (Z.lt ( aj_qz3 z) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_precompute_strategy105 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z : Z) (x : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_u1 x z)) ”) &&
    (“ (Z.lt ( aj_u1 x z) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_precompute_strategy106 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z : Z) (x : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_u2 x z)) ”) &&
    (“ (Z.lt ( aj_u2 x z) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_precompute_strategy107 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z : Z) (y : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_s1 y z)) ”) &&
    (“ (Z.lt ( aj_s1 y z) ( SM2_P_Z)) ”) &&
    emp
    ).

Definition montg_add_jpoint_precompute_strategy108 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z : Z) (y : Z),
    TT &&
    emp -*
    TT &&
    (“ (Z.le 0 ( aj_s2 y z)) ”) &&
    (“ (Z.lt ( aj_s2 y z) ( SM2_P_Z)) ”) &&
    emp
    ).

Module Type montg_add_jpoint_precompute_Strategy_Correct.

  Axiom montg_add_jpoint_precompute_strategy1_correctness : montg_add_jpoint_precompute_strategy1.
  Axiom montg_add_jpoint_precompute_strategy2_correctness : montg_add_jpoint_precompute_strategy2.
  Axiom montg_add_jpoint_precompute_strategy3_correctness : montg_add_jpoint_precompute_strategy3.
  Axiom montg_add_jpoint_precompute_strategy4_correctness : montg_add_jpoint_precompute_strategy4.
  Axiom montg_add_jpoint_precompute_strategy5_correctness : montg_add_jpoint_precompute_strategy5.
  Axiom montg_add_jpoint_precompute_strategy6_correctness : montg_add_jpoint_precompute_strategy6.
  Axiom montg_add_jpoint_precompute_strategy7_correctness : montg_add_jpoint_precompute_strategy7.
  Axiom montg_add_jpoint_precompute_strategy8_correctness : montg_add_jpoint_precompute_strategy8.
  Axiom montg_add_jpoint_precompute_strategy101_correctness : montg_add_jpoint_precompute_strategy101.
  Axiom montg_add_jpoint_precompute_strategy102_correctness : montg_add_jpoint_precompute_strategy102.
  Axiom montg_add_jpoint_precompute_strategy103_correctness : montg_add_jpoint_precompute_strategy103.
  Axiom montg_add_jpoint_precompute_strategy104_correctness : montg_add_jpoint_precompute_strategy104.
  Axiom montg_add_jpoint_precompute_strategy105_correctness : montg_add_jpoint_precompute_strategy105.
  Axiom montg_add_jpoint_precompute_strategy106_correctness : montg_add_jpoint_precompute_strategy106.
  Axiom montg_add_jpoint_precompute_strategy107_correctness : montg_add_jpoint_precompute_strategy107.
  Axiom montg_add_jpoint_precompute_strategy108_correctness : montg_add_jpoint_precompute_strategy108.

End montg_add_jpoint_precompute_Strategy_Correct.
