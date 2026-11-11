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

Definition sm2_representation_strategy10 :=
  forall (p : Z) (x : Z),
    TT &&
    emp **
    ((store_u256 p x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (y : Z),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u256 p y))
      ).

Definition sm2_representation_strategy13 :=
  forall (p : Z) (q : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_u256 p x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full &( ((q)) # "u32" ->ₛ "v") 4))
    ).

Definition sm2_representation_strategy14 :=
  forall (p : Z) (q : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_u256 p x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (y : Z),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u256_limbs (Z.add &( ((q)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) y))
      ).

Definition sm2_representation_strategy20 :=
  forall (p : Z) (x : Z),
    TT &&
    emp **
    ((store_u256_limbs p x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (y : Z),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u256_limbs p y))
      ).

Definition sm2_representation_strategy23 :=
  forall (p : Z) (xs : (@list Z)),
    TT &&
    emp **
    ((UInt64Array.full p 4 xs))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (x : Z),
      TT &&
      (“ (( u64_list_value xs) = x) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u256_limbs p x))
      ).

Definition sm2_representation_strategy25 :=
  forall (source : Z) (result : Z) (x : Z),
    TT &&
    (“ (result = source) ” || “ (source = result) ”) &&
    emp **
    ((store_u256_limbs (Z.add &( ((source)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) x))
    |--
    (
    TT &&
    (“ (result = source) ” || “ (source = result) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full &( ((result)) # "u32" ->ₛ "v") 4))
    ).

Definition sm2_representation_strategy24 :=
  forall (p : Z) (q : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_u256_limbs p x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full q 4))
    ).

Definition sm2_representation_strategy30 :=
  forall (p : Z) (x : Z) (n : Z),
    TT &&
    emp **
    ((store_u64_limbs p n x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (y : Z),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u64_limbs p n y))
      ).

Definition sm2_representation_strategy40 :=
  forall (p : Z) (x : Z),
    TT &&
    emp **
    ((store_fp p x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (y : Z),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((store_fp p y))
      ).

Definition sm2_representation_strategy46 :=
  forall (p : Z) (q : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_fp p x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full &( ((q)) # "u32" ->ₛ "v") 4))
    ).

Definition sm2_representation_strategy47 :=
  forall (p : Z) (q : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_fp p x))
    |--
    (
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    emp
    ) ** (
    ALL (y : Z),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u256 q y))
      ).

Definition sm2_representation_strategy43 :=
  forall (p : Z) (x : Z),
    TT &&
    emp **
    ((store_fn p x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (y : Z),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((store_fn p y))
      ).

Definition sm2_representation_strategy48 :=
  forall (p : Z) (q : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_fn p x))
    |--
    (
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_N_Z)) ”) &&
    emp
    ) ** (
    ALL (y : Z),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u256 q y))
      ).

Definition sm2_representation_strategy51 :=
  forall (p : Z) (q : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_fn p x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full &( ((q)) # "u32" ->ₛ "v") 4))
    ).

Definition sm2_representation_strategy52 :=
  forall (p : Z) (q : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_fn p x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full (Z.add &( ((q)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) 4))
    ).

Definition sm2_representation_strategy11 :=
  forall (p : Z) (x : Z),
    TT &&
    emp **
    ((store_u256 p x))
    |--
    (
    TT &&
    emp **
    ((store_u256_limbs &( ((p)) # "u32" ->ₛ "v") x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm2_representation_strategy21 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((store_u256_limbs p x))
    |--
    EX (x0 : Z) (x1 : Z) (x2 : Z) (x3 : Z),
      (
      TT &&
      (“ (Z.le 0 x0) ”) &&
      (“ (Z.lt x0 ( U64_MOD)) ”) &&
      (“ (Z.le 0 x1) ”) &&
      (“ (Z.lt x1 ( U64_MOD)) ”) &&
      (“ (Z.le 0 x2) ”) &&
      (“ (Z.lt x2 ( U64_MOD)) ”) &&
      (“ (Z.le 0 x3) ”) &&
      (“ (Z.lt x3 ( U64_MOD)) ”) &&
      (“ (x = ( u256_of_limbs x0 x1 x2 x3)) ”) &&
      emp **
      ((poly_store FET_uint64 (Z.add p (Z.mul 0 (@sizeof_front_end_type FET_uint64))) x0)) **
      ((poly_store FET_uint64 (Z.add p (Z.mul 1 (@sizeof_front_end_type FET_uint64))) x1)) **
      ((poly_store FET_uint64 (Z.add p (Z.mul 2 (@sizeof_front_end_type FET_uint64))) x2)) **
      ((poly_store FET_uint64 (Z.add p (Z.mul 3 (@sizeof_front_end_type FET_uint64))) x3))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition sm2_representation_strategy15 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((store_u256 p x))
    |--
    EX (xs : (@list Z)),
      (
      TT &&
      (“ ((@Zlength Z xs) = 4) ”) &&
      (“ (u64_list_bounded xs) ”) &&
      (“ (( u64_list_value xs) = x) ”) &&
      emp **
      ((UInt64Array.full &( ((p)) # "u32" ->ₛ "v") 4 xs))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition sm2_representation_strategy31 :=
  forall (x : Z) (n : Z) (p : Z),
    TT &&
    emp **
    ((store_u64_limbs p n x))
    |--
    EX (xs : (@list Z)),
      (
      TT &&
      (“ ((@Zlength Z xs) = n) ”) &&
      (“ (u64_list_bounded xs) ”) &&
      (“ (( u64_list_value xs) = x) ”) &&
      emp **
      ((UInt64Array.full p n xs))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition sm2_representation_strategy41 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p x))
    |--
    (
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    emp **
    ((store_u256 p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm2_representation_strategy44 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((store_fn p x))
    |--
    (
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_N_Z)) ”) &&
    emp **
    ((store_u256 p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm2_representation_strategy12 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z) (x : Z),
    TT &&
    emp **
    ((store_u256_limbs &( ((p)) # "u32" ->ₛ "v") x)) -*
    TT &&
    emp **
    ((store_u256 p x))
    ).

Definition sm2_representation_strategy22 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (x : Z) (x0 : Z) (x2 : Z) (x3 : Z) (x1 : Z) (p : Z),
    TT &&
    (“ (Z.le 0 x0) ”) &&
    (“ (Z.lt x0 ( U64_MOD)) ”) &&
    (“ (Z.le 0 x1) ”) &&
    (“ (Z.lt x1 ( U64_MOD)) ”) &&
    (“ (Z.le 0 x2) ”) &&
    (“ (Z.lt x2 ( U64_MOD)) ”) &&
    (“ (Z.le 0 x3) ”) &&
    (“ (Z.lt x3 ( U64_MOD)) ”) &&
    (“ (x = ( u256_of_limbs x0 x1 x2 x3)) ”) &&
    emp **
    ((poly_store FET_uint64 (Z.add p (Z.mul 0 (@sizeof_front_end_type FET_uint64))) x0)) **
    ((poly_store FET_uint64 (Z.add p (Z.mul 1 (@sizeof_front_end_type FET_uint64))) x1)) **
    ((poly_store FET_uint64 (Z.add p (Z.mul 2 (@sizeof_front_end_type FET_uint64))) x2)) **
    ((poly_store FET_uint64 (Z.add p (Z.mul 3 (@sizeof_front_end_type FET_uint64))) x3)) -*
    TT &&
    emp **
    ((store_u256_limbs p x))
    ).

Definition sm2_representation_strategy32 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (xs : (@list Z)) (x : Z) (n : Z) (p : Z),
    TT &&
    (“ ((@Zlength Z xs) = n) ”) &&
    (“ (u64_list_bounded xs) ”) &&
    (“ (( u64_list_value xs) = x) ”) &&
    emp **
    ((UInt64Array.full p n xs)) -*
    TT &&
    emp **
    ((store_u64_limbs p n x))
    ).

Definition sm2_representation_strategy42 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (x : Z) (p : Z),
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    emp **
    ((store_u256 p x)) -*
    TT &&
    emp **
    ((store_fp p x))
    ).

Definition sm2_representation_strategy45 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (x : Z) (p : Z),
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_N_Z)) ”) &&
    emp **
    ((store_u256 p x)) -*
    TT &&
    emp **
    ((store_fn p x))
    ).

Module Type sm2_representation_Strategy_Correct.

  Axiom sm2_representation_strategy10_correctness : sm2_representation_strategy10.
  Axiom sm2_representation_strategy13_correctness : sm2_representation_strategy13.
  Axiom sm2_representation_strategy14_correctness : sm2_representation_strategy14.
  Axiom sm2_representation_strategy20_correctness : sm2_representation_strategy20.
  Axiom sm2_representation_strategy23_correctness : sm2_representation_strategy23.
  Axiom sm2_representation_strategy25_correctness : sm2_representation_strategy25.
  Axiom sm2_representation_strategy24_correctness : sm2_representation_strategy24.
  Axiom sm2_representation_strategy30_correctness : sm2_representation_strategy30.
  Axiom sm2_representation_strategy40_correctness : sm2_representation_strategy40.
  Axiom sm2_representation_strategy46_correctness : sm2_representation_strategy46.
  Axiom sm2_representation_strategy47_correctness : sm2_representation_strategy47.
  Axiom sm2_representation_strategy43_correctness : sm2_representation_strategy43.
  Axiom sm2_representation_strategy48_correctness : sm2_representation_strategy48.
  Axiom sm2_representation_strategy51_correctness : sm2_representation_strategy51.
  Axiom sm2_representation_strategy52_correctness : sm2_representation_strategy52.
  Axiom sm2_representation_strategy11_correctness : sm2_representation_strategy11.
  Axiom sm2_representation_strategy21_correctness : sm2_representation_strategy21.
  Axiom sm2_representation_strategy15_correctness : sm2_representation_strategy15.
  Axiom sm2_representation_strategy31_correctness : sm2_representation_strategy31.
  Axiom sm2_representation_strategy41_correctness : sm2_representation_strategy41.
  Axiom sm2_representation_strategy44_correctness : sm2_representation_strategy44.
  Axiom sm2_representation_strategy12_correctness : sm2_representation_strategy12.
  Axiom sm2_representation_strategy22_correctness : sm2_representation_strategy22.
  Axiom sm2_representation_strategy32_correctness : sm2_representation_strategy32.
  Axiom sm2_representation_strategy42_correctness : sm2_representation_strategy42.
  Axiom sm2_representation_strategy45_correctness : sm2_representation_strategy45.

End sm2_representation_Strategy_Correct.
