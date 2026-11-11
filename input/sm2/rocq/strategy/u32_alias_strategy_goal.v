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

Definition u32_alias_strategy10 :=
  forall (b : Z) (a : Z) (x : Z) (i : Z),
    TT &&
    (“ (a = b) ” || “ (b = a) ”) &&
    emp **
    ((poly_store FET_uint64 (Z.add &( ((a)) # "u32" ->ₛ "v") (Z.mul i (@sizeof_front_end_type FET_uint64))) x))
    |--
    (
    TT &&
    (“ (a = b) ” || “ (b = a) ”) &&
    emp
    ) ** (
    ALL (y : Z),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_uint64 (Z.add &( ((b)) # "u32" ->ₛ "v") (Z.mul i (@sizeof_front_end_type FET_uint64))) y))
      ).

Module Type u32_alias_Strategy_Correct.

  Axiom u32_alias_strategy10_correctness : u32_alias_strategy10.

End u32_alias_Strategy_Correct.
