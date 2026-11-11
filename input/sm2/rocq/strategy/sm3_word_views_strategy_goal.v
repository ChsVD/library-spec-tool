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

Definition sm3_word_views_strategy15 :=
  forall (base : Z) (bytes : (@list Z)) (capacity : Z),
    TT &&
    emp **
    ((store_byte_prefix base capacity (@app Z (@nil Z) bytes)))
    |--
    (
    TT &&
    emp **
    ((store_byte_prefix base capacity bytes))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm3_word_views_strategy1 :=
  forall (index : Z) (word_base : Z) (byte_base : Z) (n : Z) (bytes : (@list Z)),
    TT &&
    (“ ((@Zlength Z bytes) = n) ”) &&
    (“ (u8_list_bounded bytes) ”) &&
    (“ (aligned_4 word_base) ”) &&
    (“ (Z.le 0 (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base)) ”) &&
    (“ (Z.le (Z.add (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) 4) n) ”) &&
    emp **
    ((UCharArray.full byte_base n bytes))
    |--
    (
    TT &&
    (“ ((@Zlength Z bytes) = n) ”) &&
    (“ (u8_list_bounded bytes) ”) &&
    (“ (aligned_4 word_base) ”) &&
    emp **
    ((UCharArray.full byte_base (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) (@sublist Z 0 (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) bytes))) **
    ((UCharArray.full (Z.add word_base (Z.mul (Z.add index 1) (@sizeof_front_end_type FET_uint))) (Z.sub n (Z.add (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) 4)) (@sublist Z (Z.add (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) 4) n bytes)))
    ) ** (
    ALL (value : Z),
      TT &&
      (“ (value = ( u8_list_value (@sublist Z (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) (Z.add (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) 4) bytes))) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_uint (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) value))
      ).

Definition sm3_word_views_strategy2 :=
  forall (index : Z) (word_base : Z) (byte_base : Z) (n : Z) (bytes : (@list Z)),
    TT &&
    (“ ((@Zlength Z bytes) = n) ”) &&
    (“ (u8_list_bounded bytes) ”) &&
    (“ (aligned_4 word_base) ”) &&
    (“ (Z.le 0 (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base)) ”) &&
    (“ (Z.le (Z.add (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) 4) n) ”) &&
    emp **
    ((UCharArray.full byte_base (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) (@sublist Z 0 (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) bytes))) **
    ((poly_store FET_uint (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) ( u8_list_value (@sublist Z (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) (Z.add (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) 4) bytes)))) **
    ((UCharArray.full (Z.add word_base (Z.mul (Z.add index 1) (@sizeof_front_end_type FET_uint))) (Z.sub n (Z.add (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) 4)) (@sublist Z (Z.add (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) 4) n bytes)))
    |--
    (
    TT &&
    (“ ((@Zlength Z bytes) = n) ”) &&
    (“ (u8_list_bounded bytes) ”) &&
    (“ (aligned_4 word_base) ”) &&
    emp **
    ((UCharArray.full byte_base n bytes))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm3_word_views_strategy11 :=
  forall (word_base : Z) (value : Z) (capacity : Z) (prefix : (@list Z)) (base : Z) (index : Z),
    TT &&
    (“ (Z.le 0 (@Zlength Z prefix)) ”) &&
    (“ (Z.le (Z.add (@Zlength Z prefix) 4) capacity) ”) &&
    (“ (u8_list_bounded prefix) ”) &&
    (“ ((Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) base) = (@Zlength Z prefix)) ”) &&
    (“ (aligned_4 word_base) ”) &&
    emp **
    ((UCharArray.full base (@Zlength Z prefix) prefix)) **
    ((poly_store FET_uint (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) value)) **
    ((UCharArray.undef_full (Z.add word_base (Z.mul (Z.add index 1) (@sizeof_front_end_type FET_uint))) (Z.sub (Z.sub capacity (@Zlength Z prefix)) 4)))
    |--
    EX (word_bytes : (@list Z)),
      (
      TT &&
      (“ (Z.le 0 (@Zlength Z prefix)) ”) &&
      (“ (Z.le (Z.add (@Zlength Z prefix) 4) capacity) ”) &&
      (“ (u8_list_bounded prefix) ”) &&
      (“ (aligned_4 word_base) ”) &&
      (“ ((@Zlength Z word_bytes) = 4) ”) &&
      (“ (u8_list_bounded word_bytes) ”) &&
      (“ (( u8_list_value word_bytes) = value) ”) &&
      emp **
      ((store_byte_prefix base capacity (@app Z prefix word_bytes)))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition sm3_word_views_strategy3 :=
  forall (index : Z) (word_base : Z) (byte_base : Z) (n : Z) (value : Z) (bytes : (@list Z)),
    TT &&
    (“ ((@Zlength Z bytes) = n) ”) &&
    (“ (u8_list_bounded bytes) ”) &&
    (“ (aligned_4 word_base) ”) &&
    (“ (Z.le 0 (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base)) ”) &&
    (“ (Z.le (Z.add (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) 4) n) ”) &&
    emp **
    ((UCharArray.full byte_base (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) (@sublist Z 0 (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) bytes))) **
    ((poly_store FET_uint (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) value)) **
    ((UCharArray.full (Z.add word_base (Z.mul (Z.add index 1) (@sizeof_front_end_type FET_uint))) (Z.sub n (Z.add (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) 4)) (@sublist Z (Z.add (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) 4) n bytes)))
    |--
    EX (word_bytes : (@list Z)),
      (
      TT &&
      (“ ((@Zlength Z bytes) = n) ”) &&
      (“ (u8_list_bounded bytes) ”) &&
      (“ (aligned_4 word_base) ”) &&
      (“ ((@Zlength Z word_bytes) = 4) ”) &&
      (“ (u8_list_bounded word_bytes) ”) &&
      (“ (( u8_list_value word_bytes) = value) ”) &&
      (“ ((@Zlength Z (@app Z (@sublist Z 0 (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) bytes) (@app Z word_bytes (@sublist Z (Z.add (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) 4) n bytes)))) = n) ”) &&
      (“ (u8_list_bounded (@app Z (@sublist Z 0 (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) bytes) (@app Z word_bytes (@sublist Z (Z.add (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) 4) n bytes)))) ”) &&
      emp **
      ((UCharArray.full byte_base n (@app Z (@sublist Z 0 (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) bytes) (@app Z word_bytes (@sublist Z (Z.add (Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) byte_base) 4) n bytes)))))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition sm3_word_views_strategy10 :=
  forall (word_base : Z) (capacity : Z) (prefix : (@list Z)) (base : Z) (index : Z),
    TT &&
    (“ (Z.le (Z.add (@Zlength Z prefix) 4) capacity) ”) &&
    (“ ((Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) base) = (@Zlength Z prefix)) ”) &&
    (“ (aligned_4 word_base) ”) &&
    emp **
    ((store_byte_prefix base capacity prefix))
    |--
    (
    TT &&
    (“ (Z.le 0 (@Zlength Z prefix)) ”) &&
    (“ (Z.le (Z.add (@Zlength Z prefix) 4) capacity) ”) &&
    (“ (u8_list_bounded prefix) ”) &&
    (“ ((Z.sub (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint))) base) = (@Zlength Z prefix)) ”) &&
    (“ (aligned_4 word_base) ”) &&
    emp **
    ((UCharArray.full base (@Zlength Z prefix) prefix)) **
    ((UCharArray.undef_full (Z.add word_base (Z.mul (Z.add index 1) (@sizeof_front_end_type FET_uint))) (Z.sub (Z.sub capacity (@Zlength Z prefix)) 4)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_uint (Z.add word_base (Z.mul index (@sizeof_front_end_type FET_uint)))))
    ).

Definition sm3_word_views_strategy13 :=
  forall (capacity : Z) (base : Z),
    TT &&
    (“ (aligned_4 base) ”) &&
    (“ (Z.le 4 capacity) ”) &&
    emp **
    ((store_byte_prefix base capacity (@nil Z)))
    |--
    (
    TT &&
    (“ (aligned_4 base) ”) &&
    (“ (Z.le 0 (@Zlength Z (@nil Z))) ”) &&
    (“ (Z.le (Z.add (@Zlength Z (@nil Z)) 4) capacity) ”) &&
    (“ (u8_list_bounded (@nil Z)) ”) &&
    (“ ((Z.sub (Z.add base (Z.mul 0 (@sizeof_front_end_type FET_uint))) base) = (@Zlength Z (@nil Z))) ”) &&
    emp **
    ((UCharArray.full base (@Zlength Z (@nil Z)) (@nil Z))) **
    ((UCharArray.undef_full (Z.add base (Z.mul (Z.add 0 1) (@sizeof_front_end_type FET_uint))) (Z.sub (Z.sub capacity (@Zlength Z (@nil Z))) 4)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_uint (Z.add base (Z.mul 0 (@sizeof_front_end_type FET_uint)))))
    ).

Module Type sm3_word_views_Strategy_Correct.

  Axiom sm3_word_views_strategy15_correctness : sm3_word_views_strategy15.
  Axiom sm3_word_views_strategy1_correctness : sm3_word_views_strategy1.
  Axiom sm3_word_views_strategy2_correctness : sm3_word_views_strategy2.
  Axiom sm3_word_views_strategy11_correctness : sm3_word_views_strategy11.
  Axiom sm3_word_views_strategy3_correctness : sm3_word_views_strategy3.
  Axiom sm3_word_views_strategy10_correctness : sm3_word_views_strategy10.
  Axiom sm3_word_views_strategy13_correctness : sm3_word_views_strategy13.

End sm3_word_views_Strategy_Correct.
