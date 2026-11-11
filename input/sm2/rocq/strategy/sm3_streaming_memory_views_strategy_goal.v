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

Definition sm3_streaming_memory_views_strategy6 :=
  forall (n : Z) (m : Z) (q : Z) (p : Z) (bytes : (@list Z)),
    TT &&
    (“ (p = q) ”) &&
    (“ (n = m) ”) &&
    emp **
    ((UCharArray.full p n bytes))
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
      ((UCharArray.full (Z.add q (Z.mul 0 (@sizeof_front_end_type FET_uchar))) m required))
      ).

Definition sm3_streaming_memory_views_strategy7 :=
  forall (n : Z) (m : Z) (q : Z) (p : Z) (words : (@list Z)),
    TT &&
    (“ (p = q) ”) &&
    (“ (n = m) ”) &&
    emp **
    ((UIntArray.full p n words))
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
      ((UIntArray.full (Z.add q (Z.mul 0 (@sizeof_front_end_type FET_uint))) m required))
      ).

Definition sm3_streaming_memory_views_strategy8 :=
  forall (n : Z) (m : Z) (p : Z) (q : Z) (j : Z) (i : Z),
    TT &&
    (“ (p = q) ”) &&
    (“ (i = j) ”) &&
    (“ (n = m) ”) &&
    emp **
    ((UCharArray.undef_full (Z.add p i) n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UCharArray.undef_full (Z.add q (Z.mul j (@sizeof_front_end_type FET_uchar))) m))
    ).

Definition sm3_streaming_memory_views_strategy13 :=
  forall (n : Z) (m : Z) (p : Z) (q : Z) (j : Z) (i : Z),
    TT &&
    (“ (p = q) ”) &&
    (“ (i = j) ”) &&
    (“ (n = m) ”) &&
    emp **
    ((UCharArray.undef_full (Z.add p (Z.mul i (@sizeof_front_end_type FET_uchar))) n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UCharArray.undef_full (Z.add q (Z.mul j (@sizeof_front_end_type FET_uchar))) m))
    ).

Definition sm3_streaming_memory_views_strategy3 :=
  forall (count : Z) (capacity : Z) (p : Z) (src : Z) (bytes : (@list Z)),
    TT &&
    (“ (Z.lt count capacity) ”) &&
    emp **
    ((UCharArray.undef_full p capacity)) **
    ((store_bytes src count bytes))
    |--
    (
    TT &&
    (“ (Z.lt count capacity) ”) &&
    emp **
    ((store_bytes src count bytes)) **
    ((UCharArray.undef_full p count)) **
    ((UCharArray.undef_full (Z.add p (Z.mul count (@sizeof_front_end_type FET_uchar))) (Z.sub capacity count)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm3_streaming_memory_views_strategy4 :=
  forall (count : Z) (total : Z) (bytes : (@list Z)) (p : Z) (dest : Z),
    TT &&
    (“ (Z.le 0 count) ”) &&
    (“ (Z.le count total) ”) &&
    emp **
    ((store_bytes p total bytes)) **
    ((UCharArray.undef_full dest count))
    |--
    (
    TT &&
    (“ ((@Zlength Z bytes) = total) ”) &&
    (“ (u8_list_bounded bytes) ”) &&
    (“ ((@Zlength Z (@sublist Z 0 count bytes)) = count) ”) &&
    (“ (u8_list_bounded (@sublist Z 0 count bytes)) ”) &&
    emp **
    ((UCharArray.undef_full dest count)) **
    ((UCharArray.full p count (@sublist Z 0 count bytes))) **
    ((UCharArray.full (Z.add p (Z.mul count (@sizeof_front_end_type FET_uchar))) (Z.sub total count) (@sublist Z count total bytes)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm3_streaming_memory_views_strategy5 :=
  forall (prefix_len : Z) (total : Z) (prefix : (@list Z)) (p : Z) (suffix : (@list Z)),
    TT &&
    (“ (Z.le 0 prefix_len) ”) &&
    (“ (Z.le prefix_len total) ”) &&
    emp **
    ((UCharArray.full p prefix_len prefix)) **
    ((UCharArray.full (Z.add p (Z.mul prefix_len (@sizeof_front_end_type FET_uchar))) (Z.sub total prefix_len) suffix))
    |--
    (
    TT &&
    emp **
    ((UCharArray.full p total (@app Z prefix suffix)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm3_streaming_memory_views_strategy9 :=
  forall (mid : Z) (hi : Z) (next : Z) (lo : Z) (left_bytes : (@list Z)) (p : Z) (right_bytes : (@list Z)),
    TT &&
    (“ (mid = next) ”) &&
    (“ (Z.le lo mid) ”) &&
    (“ (Z.le mid hi) ”) &&
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

Definition sm3_streaming_memory_views_strategy10 :=
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

Definition sm3_streaming_memory_views_strategy12 :=
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

Definition sm3_streaming_memory_views_strategy11 :=
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

Definition sm3_streaming_memory_views_strategy2 :=
  forall (n : Z) (words : (@list Z)) (p : Z) (i : Z),
    TT &&
    emp **
    ((store_u32_words_missing_i p n i words)) **
    ((poly_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint))) (@Znth Z i words 0)))
    |--
    (
    TT &&
    emp **
    ((store_u32_words p n words))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm3_streaming_memory_views_strategy1 :=
  forall (i : Z) (n : Z) (p : Z) (words : (@list Z)),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((store_u32_words p n words))
    |--
    (
    TT &&
    emp **
    ((store_u32_words_missing_i p n i words))
    ) ** (
    ALL (value : Z),
      TT &&
      (“ (value = (@Znth Z i words 0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_uint (Z.add p (Z.mul i (@sizeof_front_end_type FET_uint))) value))
      ).

Module Type sm3_streaming_memory_views_Strategy_Correct.

  Axiom sm3_streaming_memory_views_strategy6_correctness : sm3_streaming_memory_views_strategy6.
  Axiom sm3_streaming_memory_views_strategy7_correctness : sm3_streaming_memory_views_strategy7.
  Axiom sm3_streaming_memory_views_strategy8_correctness : sm3_streaming_memory_views_strategy8.
  Axiom sm3_streaming_memory_views_strategy13_correctness : sm3_streaming_memory_views_strategy13.
  Axiom sm3_streaming_memory_views_strategy3_correctness : sm3_streaming_memory_views_strategy3.
  Axiom sm3_streaming_memory_views_strategy4_correctness : sm3_streaming_memory_views_strategy4.
  Axiom sm3_streaming_memory_views_strategy5_correctness : sm3_streaming_memory_views_strategy5.
  Axiom sm3_streaming_memory_views_strategy9_correctness : sm3_streaming_memory_views_strategy9.
  Axiom sm3_streaming_memory_views_strategy10_correctness : sm3_streaming_memory_views_strategy10.
  Axiom sm3_streaming_memory_views_strategy12_correctness : sm3_streaming_memory_views_strategy12.
  Axiom sm3_streaming_memory_views_strategy11_correctness : sm3_streaming_memory_views_strategy11.
  Axiom sm3_streaming_memory_views_strategy2_correctness : sm3_streaming_memory_views_strategy2.
  Axiom sm3_streaming_memory_views_strategy1_correctness : sm3_streaming_memory_views_strategy1.

End sm3_streaming_memory_views_Strategy_Correct.
