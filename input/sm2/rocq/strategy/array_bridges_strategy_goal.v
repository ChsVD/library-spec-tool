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

Definition array_bridges_strategy3 :=
  forall (m : Z) (n : Z) (p : Z) (q : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    (“ (Z.le 0 m) ”) &&
    (“ (Z.le m n) ”) &&
    emp **
    ((UInt64Array.full p n (@repeat_Z Z x n)))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.full (Z.add q (Z.mul m (@sizeof_front_end_type FET_uint64))) (Z.sub n m) (@repeat_Z Z x (Z.sub n m))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full q m))
    ).

Definition array_bridges_strategy4 :=
  forall (m : Z) (n : Z) (p : Z) (q : Z) (xs : (@list Z)),
    TT &&
    (“ (p = q) ”) &&
    (“ (Z.le 0 m) ”) &&
    (“ (Z.le m n) ”) &&
    emp **
    ((UInt64Array.full p n xs))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.full (Z.add q (Z.mul m (@sizeof_front_end_type FET_uint64))) (Z.sub n m) (@sublist Z m n xs)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full q m))
    ).

Definition array_bridges_strategy5 :=
  forall (x : Z) (y : Z) (n : Z) (q : Z) (p : Z),
    TT &&
    (“ (n = 1) ”) &&
    (“ (p = q) ”) &&
    (“ (x = y) ”) &&
    emp **
    ((UInt64Array.full p n (@repeat_Z Z x n)))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_store FET_uint64 q y))
    ).

Definition array_bridges_strategy7 :=
  forall (i : Z) (n : Z) (p : Z) (q : Z) (xs : (@list Z)),
    TT &&
    (“ (u64_list_bounded xs) ”) &&
    (“ (p = q) ”) &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((UInt64Array.full p n xs))
    |--
    (
    TT &&
    (“ (u64_list_bounded xs) ”) &&
    (“ (Z.le 0 (@Znth Z i xs 0)) ”) &&
    (“ (Z.lt (@Znth Z i xs 0) ( U64_MOD)) ”) &&
    emp **
    ((UInt64Array.missing_i p i 0 n xs))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (@Znth Z i xs 0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_uint64 (Z.add q (Z.mul i (@sizeof_front_end_type FET_uint64))) v))
      ).

Definition array_bridges_strategy10 :=
  forall (p : Z) (n : Z),
    TT &&
    emp **
    ((UInt64Array.full_shape p n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full p n))
    ).

Definition array_bridges_strategy11 :=
  forall (n : Z) (m : Z) (q : Z) (p : Z),
    TT &&
    (“ (p = q) ”) &&
    (“ (n = m) ”) &&
    emp **
    ((UInt64Array.undef_full p n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full (Z.add q (Z.mul 0 (@sizeof_front_end_type FET_uint64))) m))
    ).

Definition array_bridges_strategy13 :=
  forall (xs : (@list Z)) (ys : (@list Z)) (p : Z) (q : Z) (m : Z) (n : Z),
    TT &&
    (“ (p = q) ”) &&
    (“ (n = m) ”) &&
    (“ (xs = ys) ”) &&
    emp **
    ((UCharArray.full p n xs))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UCharArray.full q m ys))
    ).

Definition array_bridges_strategy1 :=
  forall (p : Z) (xs : (@list Z)),
    TT &&
    emp **
    ((UInt64Array.full p 4 xs))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_uint64 (Z.add p (Z.mul 0 (@sizeof_front_end_type FET_uint64))) (@Znth Z 0 xs 0))) **
    ((poly_store FET_uint64 (Z.add p (Z.mul 1 (@sizeof_front_end_type FET_uint64))) (@Znth Z 1 xs 0))) **
    ((poly_store FET_uint64 (Z.add p (Z.mul 2 (@sizeof_front_end_type FET_uint64))) (@Znth Z 2 xs 0))) **
    ((poly_store FET_uint64 (Z.add p (Z.mul 3 (@sizeof_front_end_type FET_uint64))) (@Znth Z 3 xs 0)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array_bridges_strategy9 :=
  forall (p : Z) (n : Z),
    TT &&
    emp **
    ((UInt64Array.full_shape (Z.add p (Z.mul 0 (@sizeof_front_end_type FET_uint64))) n))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.full_shape p n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array_bridges_strategy12 :=
  forall (i : Z) (n : Z) (xs : (@list Z)) (p : Z),
    TT &&
    (“ ((@Zlength Z xs) = n) ”) &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((UInt64Array.full p n (@replace_Znth Z i (@Znth Z i xs 0) xs)))
    |--
    (
    TT &&
    (“ ((@Zlength Z xs) = n) ”) &&
    emp **
    ((UInt64Array.full p n xs))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array_bridges_strategy8 :=
  forall (i : Z) (n : Z) (v : Z) (xs : (@list Z)) (p : Z),
    TT &&
    (“ (u64_list_bounded xs) ”) &&
    (“ ((@Zlength Z xs) = n) ”) &&
    (“ (Z.le 0 v) ”) &&
    (“ (Z.lt v ( U64_MOD)) ”) &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((UInt64Array.full p n (@replace_Znth Z i v xs)))
    |--
    (
    TT &&
    (“ (u64_list_bounded xs) ”) &&
    (“ ((@Zlength Z xs) = n) ”) &&
    (“ (Z.le 0 v) ”) &&
    (“ (Z.lt v ( U64_MOD)) ”) &&
    (“ ((@Zlength Z (@replace_Znth Z i v xs)) = n) ”) &&
    (“ (u64_list_bounded (@replace_Znth Z i v xs)) ”) &&
    emp **
    ((UInt64Array.full p n (@replace_Znth Z i v xs)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array_bridges_strategy14 :=
  forall (n : Z) (p : Z) (xs : (@list Z)),
    TT &&
    (“ (n = 0) ”) &&
    emp **
    ((UInt64Array.full p n xs))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array_bridges_strategy2 :=
  forall (p : Z) (q : Z) (x2 : Z) (x0 : Z) (x1 : Z) (x3 : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((poly_store FET_uint64 (Z.add p (Z.mul 0 (@sizeof_front_end_type FET_uint64))) x0)) **
    ((poly_store FET_uint64 (Z.add p (Z.mul 1 (@sizeof_front_end_type FET_uint64))) x1)) **
    ((poly_store FET_uint64 (Z.add p (Z.mul 2 (@sizeof_front_end_type FET_uint64))) x2)) **
    ((poly_store FET_uint64 (Z.add p (Z.mul 3 (@sizeof_front_end_type FET_uint64))) x3))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (xs : (@list Z)),
      TT &&
      (“ (xs = (@cons Z x0 (@cons Z x1 (@cons Z x2 (@cons Z x3 (@nil Z)))))) ”) &&
      emp -*
      TT &&
      emp **
      ((UInt64Array.full q 4 xs))
      ).

Module Type array_bridges_Strategy_Correct.

  Axiom array_bridges_strategy3_correctness : array_bridges_strategy3.
  Axiom array_bridges_strategy4_correctness : array_bridges_strategy4.
  Axiom array_bridges_strategy5_correctness : array_bridges_strategy5.
  Axiom array_bridges_strategy7_correctness : array_bridges_strategy7.
  Axiom array_bridges_strategy10_correctness : array_bridges_strategy10.
  Axiom array_bridges_strategy11_correctness : array_bridges_strategy11.
  Axiom array_bridges_strategy13_correctness : array_bridges_strategy13.
  Axiom array_bridges_strategy1_correctness : array_bridges_strategy1.
  Axiom array_bridges_strategy9_correctness : array_bridges_strategy9.
  Axiom array_bridges_strategy12_correctness : array_bridges_strategy12.
  Axiom array_bridges_strategy8_correctness : array_bridges_strategy8.
  Axiom array_bridges_strategy14_correctness : array_bridges_strategy14.
  Axiom array_bridges_strategy2_correctness : array_bridges_strategy2.

End array_bridges_Strategy_Correct.
