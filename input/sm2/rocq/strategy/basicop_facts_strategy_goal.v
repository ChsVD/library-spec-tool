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
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition basicop_facts_strategy1 :=
  forall (y : Z) (x : Z),
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_N_Z)) ”) &&
    (“ (Z.le 0 y) ”) &&
    (“ (Z.lt y ( SM2_N_Z)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_N_Z)) ”) &&
    (“ (Z.le 0 y) ”) &&
    (“ (Z.lt y ( SM2_N_Z)) ”) &&
    (“ (Z.le 0 (Z.mul x y)) ”) &&
    (“ (Z.lt (Z.mul x y) (Z.mul ( SM2_N_Z) ( U256_MOD))) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type basicop_facts_Strategy_Correct.

  Axiom basicop_facts_strategy1_correctness : basicop_facts_strategy1.

End basicop_facts_Strategy_Correct.
