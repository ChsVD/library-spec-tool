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
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition wnaf3_predicate_cancellation_strategy1 :=
  forall (negative : Z) (required_negative : Z) (required_positive : Z) (positive : Z),
    TT &&
    (“ (positive = required_positive) ”) &&
    (“ (negative = required_negative) ”) &&
    emp **
    ((wnaf3_precomp_undef positive negative))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((wnaf3_precomp_undef required_positive required_negative))
    ).

Definition wnaf3_predicate_cancellation_strategy2 :=
  forall (point : ec_point) (required_point : ec_point) (positive : Z) (required_positive : Z) (required_negative : Z) (negative : Z),
    TT &&
    (“ (positive = required_positive) ”) &&
    (“ (negative = required_negative) ”) &&
    (“ (point = required_point) ”) &&
    emp **
    ((store_mont_wnaf3_precomp positive negative point))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_mont_wnaf3_precomp required_positive required_negative required_point))
    ).

Definition wnaf3_predicate_cancellation_strategy3 :=
  forall (negative : Z) (required_negative : Z) (required_positive : Z) (positive : Z),
    TT &&
    (“ (positive = required_positive) ”) &&
    (“ (negative = required_negative) ”) &&
    emp **
    ((wnaf3_precomp_unused positive negative))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((wnaf3_precomp_unused required_positive required_negative))
    ).

Definition wnaf3_predicate_cancellation_strategy4 :=
  forall (length : Z) (required_length : Z) (required_address : Z) (address : Z),
    TT &&
    (“ (address = required_address) ”) &&
    (“ (length = required_length) ”) &&
    emp **
    ((CharArray.undef_full address length))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((CharArray.undef_full required_address required_length))
    ).

Definition wnaf3_predicate_cancellation_strategy5 :=
  forall (digits : (@list Z)) (required_digits : (@list Z)) (address : Z) (required_address : Z) (required_length : Z) (length : Z),
    TT &&
    (“ (address = required_address) ”) &&
    (“ (length = required_length) ”) &&
    (“ (digits = required_digits) ”) &&
    emp **
    ((CharArray.full address length digits))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((CharArray.full required_address required_length required_digits))
    ).

Definition wnaf3_predicate_cancellation_strategy6 :=
  forall (base_point : ec_point) (required_base_point : ec_point) (start : Z) (required_start : Z) (required_address : Z) (address : Z) (required_digits : (@list Z)) (digits : (@list Z)),
    TT &&
    (“ (address = required_address) ”) &&
    (“ (start = required_start) ”) &&
    (“ (digits = required_digits) ”) &&
    (“ (base_point = required_base_point) ”) &&
    emp **
    ((store_mont_jpoint address ( sm2_point_mul ( wnaf3_value (@sublist Z start 257 digits)) base_point)))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_mont_jpoint required_address ( sm2_point_mul ( wnaf3_value (@sublist Z required_start 257 required_digits)) required_base_point)))
    ).

Definition wnaf3_predicate_cancellation_strategy7 :=
  forall (point : ec_point) (required_point : ec_point) (required_address : Z) (address : Z),
    TT &&
    (“ (address = required_address) ”) &&
    (“ (point = required_point) ”) &&
    emp **
    ((store_mont_jpoint address point))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_mont_jpoint required_address required_point))
    ).

Definition wnaf3_predicate_cancellation_strategy8 :=
  forall (base_point : ec_point) (required_base_point : ec_point) (start : Z) (required_start : Z) (point : ec_point) (required_address : Z) (address : Z) (required_digits : (@list Z)) (digits : (@list Z)),
    TT &&
    (“ (point = ( sm2_point_mul ( wnaf3_value (@sublist Z start 257 digits)) base_point)) ”) &&
    (“ (address = required_address) ”) &&
    (“ (start = required_start) ”) &&
    (“ (digits = required_digits) ”) &&
    (“ (base_point = required_base_point) ”) &&
    emp **
    ((store_mont_jpoint address point))
    |--
    (
    TT &&
    (“ (point = ( sm2_point_mul ( wnaf3_value (@sublist Z start 257 digits)) base_point)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_mont_jpoint required_address ( sm2_point_mul ( wnaf3_value (@sublist Z required_start 257 required_digits)) required_base_point)))
    ).

Module Type wnaf3_predicate_cancellation_Strategy_Correct.

  Axiom wnaf3_predicate_cancellation_strategy1_correctness : wnaf3_predicate_cancellation_strategy1.
  Axiom wnaf3_predicate_cancellation_strategy2_correctness : wnaf3_predicate_cancellation_strategy2.
  Axiom wnaf3_predicate_cancellation_strategy3_correctness : wnaf3_predicate_cancellation_strategy3.
  Axiom wnaf3_predicate_cancellation_strategy4_correctness : wnaf3_predicate_cancellation_strategy4.
  Axiom wnaf3_predicate_cancellation_strategy5_correctness : wnaf3_predicate_cancellation_strategy5.
  Axiom wnaf3_predicate_cancellation_strategy6_correctness : wnaf3_predicate_cancellation_strategy6.
  Axiom wnaf3_predicate_cancellation_strategy7_correctness : wnaf3_predicate_cancellation_strategy7.
  Axiom wnaf3_predicate_cancellation_strategy8_correctness : wnaf3_predicate_cancellation_strategy8.

End wnaf3_predicate_cancellation_Strategy_Correct.
