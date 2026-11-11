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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_ecc_const_table.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_basepoint_mul.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition basepoint_bytes_strategy10 :=
  forall (i : Z) (bytes : (@list Z)) (p : Z),
    TT &&
    (“ ((@Zlength Z bytes) = 32) ”) &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i 4) ”) &&
    emp **
    ((UCharArray.full p 32 bytes))
    |--
    (
    TT &&
    (“ ((@Zlength Z bytes) = 32) ”) &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i 4) ”) &&
    emp **
    ((UCharArray.full p (Z.mul 8 i) (@sublist Z 0 (Z.mul 8 i) bytes))) **
    ((UCharArray.full (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint64))) 8 (@sublist Z (Z.mul 8 i) (Z.add (Z.mul 8 i) 8) bytes))) **
    ((UCharArray.full (Z.add p (Z.mul (Z.add i 1) (@sizeof_front_end_type FET_uint64))) (Z.sub 32 (Z.add (Z.mul 8 i) 8)) (@sublist Z (Z.add (Z.mul 8 i) 8) 32 bytes)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition basepoint_bytes_strategy11 :=
  forall (i : Z) (bytes : (@list Z)) (p : Z),
    TT &&
    (“ ((@Zlength Z bytes) = 32) ”) &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i 4) ”) &&
    emp **
    ((UCharArray.full p (Z.mul 8 i) (@sublist Z 0 (Z.mul 8 i) bytes))) **
    ((UCharArray.full (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint64))) 8 (@sublist Z (Z.mul 8 i) (Z.add (Z.mul 8 i) 8) bytes))) **
    ((UCharArray.full (Z.add p (Z.mul (Z.add i 1) (@sizeof_front_end_type FET_uint64))) (Z.sub 32 (Z.add (Z.mul 8 i) 8)) (@sublist Z (Z.add (Z.mul 8 i) 8) 32 bytes)))
    |--
    (
    TT &&
    (“ ((@Zlength Z bytes) = 32) ”) &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i 4) ”) &&
    emp **
    ((UCharArray.full p 32 bytes))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition basepoint_bytes_strategy20 :=
  forall (bytes : (@list Z)) (p : Z),
    TT &&
    (“ ((@Zlength Z bytes) = 32) ”) &&
    emp **
    ((UCharArray.full p 32 bytes))
    |--
    (
    TT &&
    (“ ((@Zlength Z bytes) = 32) ”) &&
    emp **
    ((UCharArray.full p 8 (@sublist Z 0 8 bytes))) **
    ((UCharArray.full (Z.add p (Z.mul 1 (@sizeof_front_end_type FET_uint64))) 8 (@sublist Z 8 16 bytes))) **
    ((UCharArray.full (Z.add p (Z.mul 2 (@sizeof_front_end_type FET_uint64))) 8 (@sublist Z 16 24 bytes))) **
    ((UCharArray.full (Z.add p (Z.mul 3 (@sizeof_front_end_type FET_uint64))) 8 (@sublist Z 24 32 bytes)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition basepoint_bytes_strategy21 :=
  forall (bytes : (@list Z)) (p : Z),
    TT &&
    (“ ((@Zlength Z bytes) = 32) ”) &&
    emp **
    ((UCharArray.full p 8 (@sublist Z 0 8 bytes))) **
    ((UCharArray.full (Z.add p (Z.mul 1 (@sizeof_front_end_type FET_uint64))) 8 (@sublist Z 8 16 bytes))) **
    ((UCharArray.full (Z.add p (Z.mul 2 (@sizeof_front_end_type FET_uint64))) 8 (@sublist Z 16 24 bytes))) **
    ((UCharArray.full (Z.add p (Z.mul 3 (@sizeof_front_end_type FET_uint64))) 8 (@sublist Z 24 32 bytes)))
    |--
    (
    TT &&
    (“ ((@Zlength Z bytes) = 32) ”) &&
    emp **
    ((UCharArray.full p 32 bytes))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition basepoint_bytes_strategy30 :=
  forall (slot : Z) (base : Z) (bytes : (@list Z)) (n : Z),
    TT &&
    emp **
    ((poly_store FET_ptr slot (Z.add base (Z.mul 0 (@sizeof_front_end_type FET_uint64))))) **
    ((UCharArray.full base n bytes))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_ptr slot (Z.add base (Z.mul 0 (@sizeof_front_end_type FET_uint64))))) **
    ((UCharArray.full (Z.add base (Z.mul 0 (@sizeof_front_end_type FET_uint64))) n bytes))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition basepoint_bytes_strategy31 :=
  forall (slot : Z) (base : Z) (bytes : (@list Z)) (n : Z),
    TT &&
    emp **
    ((poly_store FET_ptr slot (Z.add base (Z.mul 0 (@sizeof_front_end_type FET_uint64))))) **
    ((UCharArray.full (Z.add base (Z.mul 0 (@sizeof_front_end_type FET_uint64))) n bytes))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_ptr slot (Z.add base (Z.mul 0 (@sizeof_front_end_type FET_uint64))))) **
    ((UCharArray.full base n bytes))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition basepoint_bytes_strategy32 :=
  forall (alias : Z) (base : Z) (bytes : (@list Z)) (n : Z),
    TT &&
    (“ (alias = base) ”) &&
    emp **
    ((UCharArray.full alias n bytes))
    |--
    (
    TT &&
    (“ (alias = base) ”) &&
    emp **
    ((UCharArray.full base n bytes))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition basepoint_bytes_strategy40 :=
  forall (k : Z) (value : Z) (bytes : (@list Z)),
    TT &&
    (“ (Z.le 0 value) ”) &&
    (“ (Z.lt value ( SM2_N_Z)) ”) &&
    (“ ((@Zlength Z bytes) = 32) ”) &&
    (“ (u8_list_bounded bytes) ”) &&
    (“ (( u8_list_value bytes) = value) ”) &&
    (“ (aligned_4 &( ((k)) # "u32" ->ₛ "v")) ”) &&
    emp **
    ((UCharArray.full &( ((k)) # "u32" ->ₛ "v") 32 bytes))
    |--
    (
    TT &&
    (“ (Z.le 0 value) ”) &&
    (“ (Z.lt value ( SM2_N_Z)) ”) &&
    (“ ((@Zlength Z bytes) = 32) ”) &&
    (“ (u8_list_bounded bytes) ”) &&
    (“ (( u8_list_value bytes) = value) ”) &&
    (“ (aligned_4 &( ((k)) # "u32" ->ₛ "v")) ”) &&
    emp **
    ((store_fn k value))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type basepoint_bytes_Strategy_Correct.

  Axiom basepoint_bytes_strategy10_correctness : basepoint_bytes_strategy10.
  Axiom basepoint_bytes_strategy11_correctness : basepoint_bytes_strategy11.
  Axiom basepoint_bytes_strategy20_correctness : basepoint_bytes_strategy20.
  Axiom basepoint_bytes_strategy21_correctness : basepoint_bytes_strategy21.
  Axiom basepoint_bytes_strategy30_correctness : basepoint_bytes_strategy30.
  Axiom basepoint_bytes_strategy31_correctness : basepoint_bytes_strategy31.
  Axiom basepoint_bytes_strategy32_correctness : basepoint_bytes_strategy32.
  Axiom basepoint_bytes_strategy40_correctness : basepoint_bytes_strategy40.

End basepoint_bytes_Strategy_Correct.
