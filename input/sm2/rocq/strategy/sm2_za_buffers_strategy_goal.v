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

Definition sm2_za_buffers_strategy4 :=
  forall (hi : Z) (required_hi : Z) (required_lo : Z) (lo : Z) (p : Z) (actual_bytes : (@list Z)),
    TT &&
    (“ (lo = required_lo) ”) &&
    (“ (hi = required_hi) ”) &&
    emp **
    ((UCharArray.seg p lo hi actual_bytes))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (required_bytes : (@list Z)),
      TT &&
      (“ (actual_bytes = required_bytes) ”) &&
      emp -*
      TT &&
      emp **
      ((UCharArray.seg p required_lo required_hi required_bytes))
      ).

Definition sm2_za_buffers_strategy6 :=
  forall (n : Z) (required_n : Z) (p : Z) (actual_bytes : (@list Z)),
    TT &&
    (“ (n = required_n) ”) &&
    emp **
    ((UCharArray.full p n actual_bytes))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (required_bytes : (@list Z)),
      TT &&
      (“ (actual_bytes = required_bytes) ”) &&
      emp -*
      TT &&
      emp **
      ((UCharArray.full p required_n required_bytes))
      ).

Definition sm2_za_buffers_strategy8 :=
  forall (n : Z) (required_n : Z) (p : Z),
    TT &&
    (“ (n = required_n) ”) &&
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
    ((UCharArray.undef_full p required_n))
    ).

Definition sm2_za_buffers_strategy1 :=
  forall (p : Z),
    TT &&
    emp **
    ((UCharArray.undef_full p 250))
    |--
    (
    TT &&
    emp **
    ((UCharArray.mixed_full p 250 (@repeat_Z (@option Z) (@None Z) 250)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm2_za_buffers_strategy2 :=
  forall (n : Z) (p : Z) (b1 : Z) (b0 : Z),
    TT &&
    (“ (Z.le 2 n) ”) &&
    emp **
    ((UCharArray.mixed_full p n (@replace_Znth (@option Z) 1 (@Some Z b1) (@replace_Znth (@option Z) 0 (@Some Z b0) (@repeat_Z (@option Z) (@None Z) n)))))
    |--
    (
    TT &&
    emp **
    ((UCharArray.seg p 0 2 (@cons Z b0 (@cons Z b1 (@nil Z))))) **
    ((UCharArray.undef_seg p 2 n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm2_za_buffers_strategy3 :=
  forall (mid : Z) (next : Z) (lo : Z) (left_bytes : (@list Z)) (p : Z) (hi : Z) (right_bytes : (@list Z)),
    TT &&
    (“ (mid = next) ”) &&
    emp **
    ((UCharArray.seg p lo mid left_bytes)) **
    ((UCharArray.seg p next hi right_bytes))
    |--
    (
    TT &&
    emp **
    ((UCharArray.seg p lo hi (@app Z left_bytes right_bytes)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm2_za_buffers_strategy5 :=
  forall (p : Z) (hi : Z) (bytes : (@list Z)),
    TT &&
    emp **
    ((UCharArray.seg p 0 hi bytes))
    |--
    (
    TT &&
    emp **
    ((UCharArray.full p hi bytes))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm2_za_buffers_strategy7 :=
  forall (p : Z) (bytes : (@list Z)) (n : Z),
    TT &&
    emp **
    ((UCharArray.full p n bytes))
    |--
    (
    TT &&
    emp **
    ((UCharArray.undef_full p n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm2_za_buffers_strategy9 :=
  forall (bytes : (@list Z)) (base : Z) (capacity : Z) (used : Z),
    TT &&
    emp **
    ((store_bytes (Z.add base (Z.mul 0 (@sizeof_front_end_type FET_uchar))) used bytes)) **
    ((UCharArray.undef_seg base used capacity))
    |--
    (
    TT &&
    emp **
    ((UCharArray.undef_full base capacity))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm2_za_buffers_strategy11 :=
  forall (bytes : (@list Z)) (count : Z) (lo : Z) (base : Z),
    TT &&
    emp **
    ((store_bytes (Z.add base (Z.mul lo (@sizeof_front_end_type FET_uchar))) count bytes))
    |--
    (
    TT &&
    (“ ((@Zlength Z bytes) = count) ”) &&
    (“ (u8_list_bounded bytes) ”) &&
    emp **
    ((UCharArray.seg base lo (Z.add lo count) bytes))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm2_za_buffers_strategy10 :=
  forall (count : Z) (lo : Z) (hi : Z) (base : Z) (address : Z) (bytes : (@list Z)),
    TT &&
    (“ (address = (Z.add base (Z.mul lo (@sizeof_front_end_type FET_uchar)))) ”) &&
    (“ (count = (Z.sub hi lo)) ”) &&
    emp **
    ((UCharArray.seg base lo hi bytes))
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
      ((UCharArray.full address count required))
      ).

Module Type sm2_za_buffers_Strategy_Correct.

  Axiom sm2_za_buffers_strategy4_correctness : sm2_za_buffers_strategy4.
  Axiom sm2_za_buffers_strategy6_correctness : sm2_za_buffers_strategy6.
  Axiom sm2_za_buffers_strategy8_correctness : sm2_za_buffers_strategy8.
  Axiom sm2_za_buffers_strategy1_correctness : sm2_za_buffers_strategy1.
  Axiom sm2_za_buffers_strategy2_correctness : sm2_za_buffers_strategy2.
  Axiom sm2_za_buffers_strategy3_correctness : sm2_za_buffers_strategy3.
  Axiom sm2_za_buffers_strategy5_correctness : sm2_za_buffers_strategy5.
  Axiom sm2_za_buffers_strategy7_correctness : sm2_za_buffers_strategy7.
  Axiom sm2_za_buffers_strategy9_correctness : sm2_za_buffers_strategy9.
  Axiom sm2_za_buffers_strategy11_correctness : sm2_za_buffers_strategy11.
  Axiom sm2_za_buffers_strategy10_correctness : sm2_za_buffers_strategy10.

End sm2_za_buffers_Strategy_Correct.
