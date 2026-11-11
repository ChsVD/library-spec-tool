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

Definition ecc_point_facts_strategy1 :=
  forall (point : ec_point) (x : Z) (z : Z) (y : Z),
    TT &&
    (“ (jpoint_represents x y z point) ”) &&
    (“ (point <> ( ECInfinity)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (jpoint_represents x y z point) ”) &&
    (“ (point <> ( ECInfinity)) ”) &&
    (“ (z <> 0) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_point_facts_strategy2 :=
  forall (y : Z) (point : ec_point) (x : Z),
    TT &&
    (“ (afpoint_represents x y point) ”) &&
    emp
    |--
    (
    TT &&
    (“ (afpoint_represents x y point) ”) &&
    (“ (valid_afpoint x y) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type ecc_point_facts_Strategy_Correct.

  Axiom ecc_point_facts_strategy1_correctness : ecc_point_facts_strategy1.
  Axiom ecc_point_facts_strategy2_correctness : ecc_point_facts_strategy2.

End ecc_point_facts_Strategy_Correct.
