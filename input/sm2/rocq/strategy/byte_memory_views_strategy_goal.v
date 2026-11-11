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
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition byte_memory_views_strategy1 :=
  forall (n : Z) (m : Z) (q : Z) (p : Z) (bytes : (@list Z)),
    TT &&
    (“ (p = q) ”) &&
    (“ (n = m) ”) &&
    emp **
    ((store_bytes p n bytes))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (required : (@list Z)),
      TT &&
      (“ (bytes = required) ”) &&
      emp -*
      TT &&
      emp **
      ((store_bytes q m required))
      ).

Definition byte_memory_views_strategy4 :=
  forall (n : Z) (m : Z) (q : Z) (p : Z) (bytes : (@list Z)),
    TT &&
    (“ (p = q) ”) &&
    (“ (n = m) ”) &&
    emp **
    ((store_bytes p n bytes))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UCharArray.undef_full q m))
    ).

Definition byte_memory_views_strategy5 :=
  forall (n : Z) (m : Z) (q : Z) (p : Z),
    TT &&
    (“ (p = q) ”) &&
    (“ (n = m) ”) &&
    emp **
    ((UCharArray.undef_full p n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UCharArray.undef_full (Z.add q (Z.mul 0 (@sizeof_front_end_type FET_uchar))) m))
    ).

Definition byte_memory_views_strategy6 :=
  forall (n : Z) (m : Z) (q : Z) (p : Z) (bytes : (@list Z)),
    TT &&
    (“ (p = q) ”) &&
    (“ (n = m) ”) &&
    emp **
    ((store_bytes (Z.add p (Z.mul 0 (@sizeof_front_end_type FET_uchar))) n bytes))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UCharArray.undef_full q m))
    ).

Definition byte_memory_views_strategy10 :=
  forall (n : Z) (m : Z) (q : Z) (p : Z) (words : (@list Z)),
    TT &&
    (“ (p = q) ”) &&
    (“ (n = m) ”) &&
    emp **
    ((store_u32_words p n words))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (required : (@list Z)),
      TT &&
      (“ (words = required) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u32_words q m required))
      ).

Definition byte_memory_views_strategy13 :=
  forall (n : Z) (m : Z) (q : Z) (p : Z) (words : (@list Z)),
    TT &&
    (“ (p = q) ”) &&
    (“ (n = m) ”) &&
    emp **
    ((store_u32_words p n words))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UIntArray.undef_full q m))
    ).

Definition byte_memory_views_strategy20 :=
  forall (capacity : Z) (required_capacity : Z) (q : Z) (p : Z) (bytes : (@list Z)),
    TT &&
    (“ (p = q) ”) &&
    (“ (capacity = required_capacity) ”) &&
    emp **
    ((store_byte_prefix p capacity bytes))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (required : (@list Z)),
      TT &&
      (“ (bytes = required) ”) &&
      emp -*
      TT &&
      emp **
      ((store_byte_prefix q required_capacity required))
      ).

Definition byte_memory_views_strategy2 :=
  forall (bytes : (@list Z)) (n : Z) (p : Z),
    TT &&
    emp **
    ((store_bytes p n bytes))
    |--
    (
    TT &&
    (“ ((@Zlength Z bytes) = n) ”) &&
    (“ (u8_list_bounded bytes) ”) &&
    emp **
    ((UCharArray.full p n bytes))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition byte_memory_views_strategy11 :=
  forall (words : (@list Z)) (n : Z) (p : Z),
    TT &&
    emp **
    ((store_u32_words p n words))
    |--
    (
    TT &&
    (“ ((@Zlength Z words) = n) ”) &&
    (“ (limb_list_bounded ( SM3_WORD_MODULUS) words) ”) &&
    emp **
    ((UIntArray.full p n words))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition byte_memory_views_strategy21 :=
  forall (bytes : (@list Z)) (capacity : Z) (p : Z),
    TT &&
    emp **
    ((store_byte_prefix p capacity bytes))
    |--
    (
    TT &&
    (“ (Z.le 0 (@Zlength Z bytes)) ”) &&
    (“ (Z.le (@Zlength Z bytes) capacity) ”) &&
    (“ (u8_list_bounded bytes) ”) &&
    emp **
    ((UCharArray.full p (@Zlength Z bytes) bytes)) **
    ((UCharArray.undef_full (Z.add p (@Zlength Z bytes)) (Z.sub capacity (@Zlength Z bytes))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition byte_memory_views_strategy23 :=
  forall (capacity : Z) (p : Z),
    TT &&
    (“ (Z.le 0 capacity) ”) &&
    emp **
    ((UCharArray.undef_full p capacity))
    |--
    (
    TT &&
    emp **
    ((store_byte_prefix p capacity (@nil Z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition byte_memory_views_strategy30 :=
  forall (p : Z) (value : Z),
    TT &&
    emp **
    ((store_u256 p value))
    |--
    EX (bytes : (@list Z)),
      (
      TT &&
      (“ (( u8_list_value bytes) = value) ”) &&
      (“ (aligned_4 p) ”) &&
      emp **
      ((store_bytes p 32 bytes))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition byte_memory_views_strategy31 :=
  forall (p : Z) (value : Z) (bytes : (@list Z)),
    TT &&
    (“ (( u8_list_value bytes) = value) ”) &&
    (“ (aligned_4 p) ”) &&
    emp **
    ((store_bytes p 32 bytes))
    |--
    (
    TT &&
    (“ (( u8_list_value bytes) = value) ”) &&
    (“ (aligned_4 p) ”) &&
    emp **
    ((store_u256 p value))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition byte_memory_views_strategy32 :=
  forall (p : Z),
    TT &&
    emp **
    ((UndefStructPredu32 p))
    |--
    (
    TT &&
    (“ (aligned_4 p) ”) &&
    emp **
    ((UCharArray.undef_full p 32))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition byte_memory_views_strategy3 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (bytes : (@list Z)) (n : Z) (p : Z),
    TT &&
    (“ ((@Zlength Z bytes) = n) ”) &&
    (“ (u8_list_bounded bytes) ”) &&
    emp **
    ((UCharArray.full p n bytes)) -*
    TT &&
    emp **
    ((store_bytes p n bytes))
    ).

Definition byte_memory_views_strategy12 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (words : (@list Z)) (n : Z) (p : Z),
    TT &&
    (“ ((@Zlength Z words) = n) ”) &&
    (“ (limb_list_bounded ( SM3_WORD_MODULUS) words) ”) &&
    emp **
    ((UIntArray.full p n words)) -*
    TT &&
    emp **
    ((store_u32_words p n words))
    ).

Definition byte_memory_views_strategy22 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (bytes : (@list Z)) (capacity : Z) (p : Z),
    TT &&
    (“ (Z.le 0 (@Zlength Z bytes)) ”) &&
    (“ (Z.le (@Zlength Z bytes) capacity) ”) &&
    (“ (u8_list_bounded bytes) ”) &&
    emp **
    ((UCharArray.full p (@Zlength Z bytes) bytes)) **
    ((UCharArray.undef_full (Z.add p (@Zlength Z bytes)) (Z.sub capacity (@Zlength Z bytes)))) -*
    TT &&
    emp **
    ((store_byte_prefix p capacity bytes))
    ).

Module Type byte_memory_views_Strategy_Correct.

  Axiom byte_memory_views_strategy1_correctness : byte_memory_views_strategy1.
  Axiom byte_memory_views_strategy4_correctness : byte_memory_views_strategy4.
  Axiom byte_memory_views_strategy5_correctness : byte_memory_views_strategy5.
  Axiom byte_memory_views_strategy6_correctness : byte_memory_views_strategy6.
  Axiom byte_memory_views_strategy10_correctness : byte_memory_views_strategy10.
  Axiom byte_memory_views_strategy13_correctness : byte_memory_views_strategy13.
  Axiom byte_memory_views_strategy20_correctness : byte_memory_views_strategy20.
  Axiom byte_memory_views_strategy2_correctness : byte_memory_views_strategy2.
  Axiom byte_memory_views_strategy11_correctness : byte_memory_views_strategy11.
  Axiom byte_memory_views_strategy21_correctness : byte_memory_views_strategy21.
  Axiom byte_memory_views_strategy23_correctness : byte_memory_views_strategy23.
  Axiom byte_memory_views_strategy30_correctness : byte_memory_views_strategy30.
  Axiom byte_memory_views_strategy31_correctness : byte_memory_views_strategy31.
  Axiom byte_memory_views_strategy32_correctness : byte_memory_views_strategy32.
  Axiom byte_memory_views_strategy3_correctness : byte_memory_views_strategy3.
  Axiom byte_memory_views_strategy12_correctness : byte_memory_views_strategy12.
  Axiom byte_memory_views_strategy22_correctness : byte_memory_views_strategy22.

End byte_memory_views_Strategy_Correct.
