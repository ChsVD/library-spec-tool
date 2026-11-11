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
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition ecc_constants_strategy10 :=
  TT &&
  emp **
  ((store_sm2_a))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_a))
  ).

Definition ecc_constants_strategy13 :=
  forall (x : Z),
    TT &&
    emp **
    ((store_fp  &("SM2_a")  x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    (“ (x = ( SM2_A_Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((store_sm2_a))
    ).

Definition ecc_constants_strategy20 :=
  TT &&
  emp **
  ((store_sm2_b))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_b))
  ).

Definition ecc_constants_strategy23 :=
  forall (x : Z),
    TT &&
    emp **
    ((store_fp  &("SM2_b")  x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    (“ (x = ( SM2_B_Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((store_sm2_b))
    ).

Definition ecc_constants_strategy30 :=
  TT &&
  emp **
  ((store_jpoint_zero))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_jpoint_zero))
  ).

Definition ecc_constants_strategy33 :=
  forall (y : Z) (z : Z) (x : Z),
    TT &&
    emp **
    ((store_jpoint_fields  &("JPoint_ZERO")  x y z))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    (“ (x = 1) ”) &&
    (“ (y = 1) ”) &&
    (“ (z = 0) ”) &&
    emp -*
    TT &&
    emp **
    ((store_jpoint_zero))
    ).

Definition ecc_constants_strategy40 :=
  TT &&
  emp **
  ((store_sm2_inv2p))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_inv2p))
  ).

Definition ecc_constants_strategy43 :=
  forall (x : Z),
    TT &&
    emp **
    ((store_fp  &("SM2_inv2P")  x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    (“ (x = ( SM2_P_INV2_Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((store_sm2_inv2p))
    ).

Definition ecc_constants_strategy11 :=
  TT &&
  emp **
  ((store_sm2_a))
  |--
  (
  TT &&
  emp **
  ((store_fp  &("SM2_a")  ( SM2_A_Z)))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition ecc_constants_strategy21 :=
  TT &&
  emp **
  ((store_sm2_b))
  |--
  (
  TT &&
  emp **
  ((store_fp  &("SM2_b")  ( SM2_B_Z)))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition ecc_constants_strategy31 :=
  TT &&
  emp **
  ((store_jpoint_zero))
  |--
  (
  TT &&
  emp **
  ((store_jpoint_fields  &("JPoint_ZERO")  1 1 0))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition ecc_constants_strategy41 :=
  TT &&
  emp **
  ((store_sm2_inv2p))
  |--
  (
  TT &&
  emp **
  ((store_fp  &("SM2_inv2P")  ( SM2_P_INV2_Z)))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Module Type ecc_constants_Strategy_Correct.

  Axiom ecc_constants_strategy10_correctness : ecc_constants_strategy10.
  Axiom ecc_constants_strategy13_correctness : ecc_constants_strategy13.
  Axiom ecc_constants_strategy20_correctness : ecc_constants_strategy20.
  Axiom ecc_constants_strategy23_correctness : ecc_constants_strategy23.
  Axiom ecc_constants_strategy30_correctness : ecc_constants_strategy30.
  Axiom ecc_constants_strategy33_correctness : ecc_constants_strategy33.
  Axiom ecc_constants_strategy40_correctness : ecc_constants_strategy40.
  Axiom ecc_constants_strategy43_correctness : ecc_constants_strategy43.
  Axiom ecc_constants_strategy11_correctness : ecc_constants_strategy11.
  Axiom ecc_constants_strategy21_correctness : ecc_constants_strategy21.
  Axiom ecc_constants_strategy31_correctness : ecc_constants_strategy31.
  Axiom ecc_constants_strategy41_correctness : ecc_constants_strategy41.

End ecc_constants_Strategy_Correct.
