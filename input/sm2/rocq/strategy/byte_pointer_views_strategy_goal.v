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

Definition byte_pointer_views_strategy1 :=
  forall (index : Z) (length : Z) (cursor : Z) (base : Z) (bytes : (@list Z)),
    TT &&
    (“ (cursor = (Z.add base (Z.mul index (@sizeof_front_end_type FET_uchar)))) ”) &&
    (“ (Z.le 0 index) ”) &&
    (“ (Z.lt index length) ”) &&
    emp **
    ((UCharArray.full base length bytes))
    |--
    (
    TT &&
    (“ (cursor = (Z.add base (Z.mul index (@sizeof_front_end_type FET_uchar)))) ”) &&
    emp **
    ((UCharArray.missing_i base index 0 length bytes))
    ) ** (
    ALL (value : Z),
      TT &&
      (“ (value = (@Znth Z index bytes 0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_uchar cursor value))
      ).

Definition byte_pointer_views_strategy4 :=
  forall (index : Z) (length : Z) (cursor : Z) (base : Z) (bytes : (@list Z)),
    TT &&
    (“ (cursor = (Z.add base (Z.mul index (@sizeof_front_end_type FET_uchar)))) ”) &&
    (“ (Z.le 0 index) ”) &&
    (“ (Z.lt index length) ”) &&
    emp **
    ((UCharArray.full base length bytes))
    |--
    (
    TT &&
    (“ (cursor = (Z.add base (Z.mul index (@sizeof_front_end_type FET_uchar)))) ”) &&
    emp **
    ((UCharArray.missing_i base index 0 length bytes))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_uchar cursor))
    ).

Definition byte_pointer_views_strategy2 :=
  forall (index : Z) (length : Z) (cursor : Z) (base : Z) (bytes : (@list Z)),
    TT &&
    (“ (cursor = (Z.add base (Z.mul index (@sizeof_front_end_type FET_uchar)))) ”) &&
    (“ (Z.le 0 index) ”) &&
    (“ (Z.lt index length) ”) &&
    emp **
    ((UCharArray.missing_i base index 0 length bytes)) **
    ((poly_store FET_uchar cursor (@Znth Z index bytes 0)))
    |--
    (
    TT &&
    (“ (cursor = (Z.add base (Z.mul index (@sizeof_front_end_type FET_uchar)))) ”) &&
    emp **
    ((UCharArray.full base length bytes))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition byte_pointer_views_strategy3 :=
  forall (index : Z) (length : Z) (cursor : Z) (base : Z) (bytes : (@list Z)) (value : Z),
    TT &&
    (“ (cursor = (Z.add base (Z.mul index (@sizeof_front_end_type FET_uchar)))) ”) &&
    (“ (Z.le 0 index) ”) &&
    (“ (Z.lt index length) ”) &&
    emp **
    ((UCharArray.missing_i base index 0 length bytes)) **
    ((poly_store FET_uchar cursor value))
    |--
    (
    TT &&
    (“ (cursor = (Z.add base (Z.mul index (@sizeof_front_end_type FET_uchar)))) ”) &&
    emp **
    ((UCharArray.full base length (@replace_Znth Z index value bytes)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type byte_pointer_views_Strategy_Correct.

  Axiom byte_pointer_views_strategy1_correctness : byte_pointer_views_strategy1.
  Axiom byte_pointer_views_strategy4_correctness : byte_pointer_views_strategy4.
  Axiom byte_pointer_views_strategy2_correctness : byte_pointer_views_strategy2.
  Axiom byte_pointer_views_strategy3_correctness : byte_pointer_views_strategy3.

End byte_pointer_views_Strategy_Correct.
