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

Definition raw_mul_arrays_strategy1 :=
  forall (p : Z) (x0 : Z) (x2 : Z) (x1 : Z),
    TT &&
    emp **
    ((UInt64Array.mixed_full p 8 (@replace_Znth (@option Z) 0 (@Some Z x0) (@replace_Znth (@option Z) 1 (@Some Z x1) (@replace_Znth (@option Z) 2 (@Some Z x2) (@repeat_Z (@option Z) (@None Z) 8))))))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_uint64 (Z.add p (Z.mul 0 (@sizeof_front_end_type FET_uint64))) x0)) **
    ((poly_store FET_uint64 (Z.add p (Z.mul 1 (@sizeof_front_end_type FET_uint64))) x1)) **
    ((poly_store FET_uint64 (Z.add p (Z.mul 2 (@sizeof_front_end_type FET_uint64))) x2)) **
    ((UInt64Array.undef_seg p 3 8))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition raw_mul_arrays_strategy2 :=
  forall (i : Z) (j : Z) (v : Z) (p : Z),
    TT &&
    (“ (i = j) ”) &&
    emp **
    ((poly_store FET_uint64 (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint64))) v))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (w : Z),
      TT &&
      (“ (v = w) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_uint64 (Z.add p (Z.mul j (@sizeof_front_end_type FET_uint64))) w))
      ).

Definition raw_mul_arrays_strategy3 :=
  forall (i : Z) (j : Z) (q : Z) (p : Z) (v : Z),
    TT &&
    (“ (p = q) ”) &&
    (“ (i = j) ”) &&
    emp **
    ((poly_store FET_uint64 (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint64))) v))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (w : Z),
      TT &&
      (“ (v = w) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_uint64 (Z.add q (Z.mul j (@sizeof_front_end_type FET_uint64))) w))
      ).

Module Type raw_mul_arrays_Strategy_Correct.

  Axiom raw_mul_arrays_strategy1_correctness : raw_mul_arrays_strategy1.
  Axiom raw_mul_arrays_strategy2_correctness : raw_mul_arrays_strategy2.
  Axiom raw_mul_arrays_strategy3_correctness : raw_mul_arrays_strategy3.

End raw_mul_arrays_Strategy_Correct.
