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

Definition ecc_point_overwrite_strategy1 :=
  forall (p : Z) (q : Z) (point : ec_point),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_mont_jpoint p point))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full &( ((&( ((q)) # "JPoint" ->ₛ "x"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( ((q)) # "JPoint" ->ₛ "y"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( ((q)) # "JPoint" ->ₛ "z"))) # "u32" ->ₛ "v") 4))
    ).

Module Type ecc_point_overwrite_Strategy_Correct.

  Axiom ecc_point_overwrite_strategy1_correctness : ecc_point_overwrite_strategy1.

End ecc_point_overwrite_Strategy_Correct.
