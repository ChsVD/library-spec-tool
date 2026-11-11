(** Shared mathematical and memory interfaces for SM2 scalar multiplication. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SumLib Require Import SumLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.Applications_human.sm2.lib Require Import ecc.

Import ListNotations.
Import Snaive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.

(** * Width-3 non-adjacent form *)

Definition WNAF3_LENGTH : Z := 257.

Definition wnaf3_digit (digit : Z) : Prop :=
  digit = -3 \/ digit = -1 \/ digit = 0 \/ digit = 1 \/ digit = 3.

(** Digits are stored least-significant first. *)
Definition wnaf3_value (digits : list Z) : Z :=
  Sum.sum (fun index => 0 <= index < Zlength digits)
          (fun index => Znth index digits 0 * 2 ^ index).

(** A nonzero width-3 digit is followed by two zero digits whenever those
    positions are still inside the representation. *)
Definition wnaf3_separated (digits : list Z) : Prop :=
  forall index,
    0 <= index < Zlength digits ->
    Znth index digits 0 <> 0 ->
    (index + 1 < Zlength digits ->
       Znth (index + 1) digits 0 = 0) /\
    (index + 2 < Zlength digits ->
       Znth (index + 2) digits 0 = 0).

Definition wnaf3_representation (scalar : Z) (digits : list Z) : Prop :=
  Zlength digits = WNAF3_LENGTH /\
  (forall index,
      0 <= index < Zlength digits ->
      wnaf3_digit (Znth index digits 0)) /\
  wnaf3_separated digits /\
  wnaf3_value digits = scalar.

(** The signed-byte array produced by [get_naf_w3]. *)
Definition store_wnaf3 (address : addr) (scalar : Z) : Assertion :=
  EX digits,
    “ wnaf3_representation scalar digits ” &&
    CharArray.full address WNAF3_LENGTH digits.

Lemma wnaf3_digit_bounds :
  forall digit,
    wnaf3_digit digit ->
    -3 <= digit <= 3.
Proof.
  intros digit Hdigit.
  unfold wnaf3_digit in Hdigit.
  repeat destruct Hdigit as [Hdigit | Hdigit]; subst; lia.
Qed.

Lemma wnaf3_representation_length :
  forall scalar digits,
    wnaf3_representation scalar digits ->
    Zlength digits = WNAF3_LENGTH.
Proof.
  intros scalar digits Hrepresentation.
  exact (proj1 Hrepresentation).
Qed.

Lemma wnaf3_representation_value :
  forall scalar digits,
    wnaf3_representation scalar digits ->
    wnaf3_value digits = scalar.
Proof.
  intros scalar digits Hrepresentation.
  exact (proj2 (proj2 (proj2 Hrepresentation))).
Qed.

Lemma wnaf3_suffix_step :
  forall scalar digits index,
    wnaf3_representation scalar digits ->
    0 <= index < WNAF3_LENGTH ->
    wnaf3_value (sublist index WNAF3_LENGTH digits) =
      Znth index digits 0 +
      2 * wnaf3_value (sublist (index + 1) WNAF3_LENGTH digits).
Proof.
  intros scalar digits index Hrepresentation Hindex.
  pose proof
    (wnaf3_representation_length scalar digits Hrepresentation) as Hlength.
  unfold WNAF3_LENGTH in Hlength, Hindex |- *.
  assert (Hcons :
    sublist index 257 digits =
      Znth index digits 0 :: sublist (index + 1) 257 digits).
  {
    rewrite (sublist_split index 257 (index + 1)) by lia.
    rewrite (sublist_single 0 index digits) by lia.
    reflexivity.
  }
  rewrite Hcons.
  unfold wnaf3_value.
  rewrite
    (SumLib.ZRange.sum_Z_range_Znth_cons_indexed
      0 (Znth index digits 0) (sublist (index + 1) 257 digits)
      (fun offset value => value * 2 ^ offset)).
  cbn [Z.pow].
  rewrite <- SumLib.ZRange.sum_Z_range_factor_l.
  ring_simplify.
  f_equal.
  apply SumLib.ZRange.sum_Z_range_ext.
  intros offset Hoffset.
  rewrite Z.pow_add_r by lia.
  replace (2 ^ 1) with 2 by reflexivity.
  ring.
Qed.

Lemma wnaf3_last_suffix_value :
  forall scalar digits,
    wnaf3_representation scalar digits ->
    wnaf3_value (sublist 256 WNAF3_LENGTH digits) =
      Znth 256 digits 0.
Proof.
  intros scalar digits Hrepresentation.
  pose proof
    (wnaf3_representation_length scalar digits Hrepresentation) as Hlength.
  unfold WNAF3_LENGTH in Hlength |- *.
  assert (Hsingle :
    sublist 256 257 digits = Znth 256 digits 0 :: nil).
  {
    replace 257 with (256 + 1) by lia.
    apply sublist_single.
    lia.
  }
  rewrite Hsingle.
  unfold wnaf3_value, Sum.sum.
  simpl.
  unfold Znth.
  simpl.
  lia.
Qed.

Lemma wnaf3_suffix_nonnegative :
  forall scalar digits index,
    0 <= scalar ->
    wnaf3_representation scalar digits ->
    0 <= index < WNAF3_LENGTH ->
    0 <= wnaf3_value (sublist index WNAF3_LENGTH digits).
Proof.
  intros scalar digits index Hscalar Hrepresentation Hindex.
  pose proof
    (wnaf3_representation_length scalar digits Hrepresentation) as Hlength.
  assert (Hrec : forall position,
    0 <= position < WNAF3_LENGTH ->
    wnaf3_value (sublist position WNAF3_LENGTH digits) =
      Znth position digits 0 +
      2 * wnaf3_value
        (sublist (position + 1) WNAF3_LENGTH digits)).
  {
    intros position Hposition.
    exact
      (wnaf3_suffix_step scalar digits position
        Hrepresentation Hposition).
  }
  destruct Hrepresentation as
    [Hlength' [Hdigits [Hseparated Hvalue]]].
  unfold WNAF3_LENGTH in Hlength, Hlength', Hindex, Hrec |- *.
  destruct
    (Z_lt_ge_dec (wnaf3_value (sublist index 257 digits)) 0)
    as [Hnegative | Hnonnegative].
  - assert (Hback : forall count : nat,
      Z.of_nat count <= index ->
      wnaf3_value (sublist (index - Z.of_nat count) 257 digits) < 0).
    {
      intro count.
      induction count as [| count IH]; intros Hcount.
      - simpl.
        replace (index - 0) with index by lia.
        exact Hnegative.
      - assert (Hprevious : Z.of_nat count <= index) by lia.
        specialize (IH Hprevious).
        set (position := index - Z.of_nat (S count)).
        assert (Hposition : 0 <= position < 256) by
          (unfold position; lia).
        assert (Hnext : position + 1 = index - Z.of_nat count) by
          (unfold position; lia).
        pose proof (Hrec position ltac:(lia)) as Hstep0.
        specialize (Hdigits position ltac:(lia)) as Hdigit.
        pose proof (wnaf3_digit_bounds _ Hdigit) as Hdigit_bounds.
        destruct (Z_le_gt_dec (Znth position digits 0) 0)
          as [Hdigit_nonpositive | Hdigit_positive].
        + rewrite <- Hnext in IH.
          lia.
        + assert (Hdigit_nonzero : Znth position digits 0 <> 0) by lia.
          specialize
            (Hseparated position ltac:(lia) Hdigit_nonzero)
            as [Hzero1 _].
          specialize (Hzero1 ltac:(lia)).
          pose proof (Hrec (position + 1) ltac:(lia)) as Hstep1.
          rewrite Hzero1 in Hstep1.
          assert (Hsuffix2_negative :
            wnaf3_value (sublist (position + 2) 257 digits) < 0).
          {
            rewrite <- Hnext in IH.
            replace (position + 1 + 1) with (position + 2) in Hstep1
              by lia.
            lia.
          }
          replace (position + 1 + 1) with (position + 2) in Hstep1
            by lia.
          rewrite <- Hnext in IH.
          assert (Hsuffix2_le :
            wnaf3_value (sublist (position + 2) 257 digits) <= -1)
            by lia.
          assert (Hsuffix1_le :
            wnaf3_value (sublist (position + 1) 257 digits) <= -2)
            by lia.
          destruct Hdigit_bounds as [Hdigit_lower Hdigit_upper].
          assert (Htwice_le :
            2 * wnaf3_value
              (sublist (position + 1) 257 digits) <= -4).
          {
            replace (-4) with (2 * (-2)) by ring.
            apply Z.mul_le_mono_nonneg_l; lia.
          }
          rewrite Hstep0.
          apply Z.le_lt_trans with (-1); [| lia].
          replace (-1) with (3 + (-4)) by ring.
          apply Z.add_le_mono; assumption.
    }
    specialize (Hback (Z.to_nat index) ltac:(lia)).
    rewrite Z2Nat.id in Hback by lia.
    replace (index - index) with 0 in Hback by lia.
    assert (Hsub0 : sublist 0 257 digits = digits).
    {
      rewrite <- Hlength'.
      pose proof (@sublist_app_exact1 Z digits nil) as Hsame.
      rewrite app_nil_r in Hsame.
      exact Hsame.
    }
    rewrite Hsub0, Hvalue in Hback.
    lia.
  - lia.
Qed.

(** * The two four-entry width-3 precomputation arrays *)

Definition afpoint_array_slot (base : addr) (index : Z) : addr :=
  base + index * StoreStructAFPointAsElement.sizeA.

(** Role-labelled ownership for a freshly allocated local table.  The two
    predicates have the same layout but distinct heads, so an unordered
    separating conjunction cannot swap the positive and negative arrays. *)
Definition wnaf3_positive_array_undef (positive : addr) : Assertion :=
  UndefStructPredAFPoint (afpoint_array_slot positive 0) **
  UndefStructPredAFPoint (afpoint_array_slot positive 1) **
  UndefStructPredAFPoint (afpoint_array_slot positive 2) **
  UndefStructPredAFPoint (afpoint_array_slot positive 3).

Definition wnaf3_negative_array_undef (negative : addr) : Assertion :=
  UndefStructPredAFPoint (afpoint_array_slot negative 0) **
  UndefStructPredAFPoint (afpoint_array_slot negative 1) **
  UndefStructPredAFPoint (afpoint_array_slot negative 2) **
  UndefStructPredAFPoint (afpoint_array_slot negative 3).

(** Only slots 1 and 3 are overwritten by [montg_pre_compute_naf_w3].
    Slots 0 and 2 are deliberately left outside this predicate. *)
Definition wnaf3_precomp_undef
    (positive negative : addr) : Assertion :=
  UndefStructPredAFPoint (afpoint_array_slot positive 1) **
  UndefStructPredAFPoint (afpoint_array_slot positive 3) **
  UndefStructPredAFPoint (afpoint_array_slot negative 1) **
  UndefStructPredAFPoint (afpoint_array_slot negative 3).

(** PT[1] = P, PT[3] = 3P and NT contains their negations.  All four
    materialized points use Montgomery coordinates. *)
Definition store_mont_wnaf3_precomp
    (positive negative : addr) (point : ec_point) : Assertion :=
  store_mont_afpoint (afpoint_array_slot positive 1) point **
  store_mont_afpoint
    (afpoint_array_slot positive 3) (sm2_point_mul 3 point) **
  store_mont_afpoint
    (afpoint_array_slot negative 1) (sm2_point_negate point) **
  store_mont_afpoint
    (afpoint_array_slot negative 3)
    (sm2_point_negate (sm2_point_mul 3 point)).

(** Slots 0 and 2 of the two automatic arrays are never read or written. *)
Definition wnaf3_precomp_unused
    (positive negative : addr) : Assertion :=
  UndefStructPredAFPoint (afpoint_array_slot positive 0) **
  UndefStructPredAFPoint (afpoint_array_slot positive 2) **
  UndefStructPredAFPoint (afpoint_array_slot negative 0) **
  UndefStructPredAFPoint (afpoint_array_slot negative 2).

(** The three owned entries left after focusing one dynamic WNAF digit. *)
Definition store_mont_wnaf3_precomp_rest
    (positive negative : addr) (point : ec_point) (digit : Z)
    : Assertion :=
  if Z.eq_dec digit 1 then
    store_mont_afpoint
      (afpoint_array_slot positive 3) (sm2_point_mul 3 point) **
    store_mont_afpoint
      (afpoint_array_slot negative 1) (sm2_point_negate point) **
    store_mont_afpoint
      (afpoint_array_slot negative 3)
      (sm2_point_negate (sm2_point_mul 3 point))
  else if Z.eq_dec digit 3 then
    store_mont_afpoint (afpoint_array_slot positive 1) point **
    store_mont_afpoint
      (afpoint_array_slot negative 1) (sm2_point_negate point) **
    store_mont_afpoint
      (afpoint_array_slot negative 3)
      (sm2_point_negate (sm2_point_mul 3 point))
  else if Z.eq_dec digit (-1) then
    store_mont_afpoint (afpoint_array_slot positive 1) point **
    store_mont_afpoint
      (afpoint_array_slot positive 3) (sm2_point_mul 3 point) **
    store_mont_afpoint
      (afpoint_array_slot negative 3)
      (sm2_point_negate (sm2_point_mul 3 point))
  else if Z.eq_dec digit (-3) then
    store_mont_afpoint (afpoint_array_slot positive 1) point **
    store_mont_afpoint
      (afpoint_array_slot positive 3) (sm2_point_mul 3 point) **
    store_mont_afpoint
      (afpoint_array_slot negative 1) (sm2_point_negate point)
  else emp.

Lemma wnaf3_positive_digit_cases :
  forall digit,
    wnaf3_digit digit -> digit > 0 -> digit = 1 \/ digit = 3.
Proof.
  intros digit Hdigit Hpositive.
  unfold wnaf3_digit in Hdigit.
  repeat destruct Hdigit as [-> | Hdigit]; try lia.
Qed.

Lemma wnaf3_negative_digit_cases :
  forall digit,
    wnaf3_digit digit -> digit < 0 -> digit = -1 \/ digit = -3.
Proof.
  intros digit Hdigit Hnegative.
  unfold wnaf3_digit in Hdigit.
  repeat destruct Hdigit as [-> | Hdigit]; try lia.
Qed.

Lemma store_mont_wnaf3_precomp_focus_positive :
  forall positive negative point digit,
    wnaf3_digit digit -> digit > 0 ->
    store_mont_wnaf3_precomp positive negative point |--
      store_mont_afpoint
        (afpoint_array_slot positive digit)
        (sm2_point_mul digit point) **
      store_mont_wnaf3_precomp_rest positive negative point digit.
Proof.
  intros positive negative point digit Hdigit Hpositive.
  destruct (wnaf3_positive_digit_cases digit Hdigit Hpositive) as [-> | ->];
    unfold store_mont_wnaf3_precomp,
      store_mont_wnaf3_precomp_rest;
    repeat destruct Z.eq_dec; try lia;
    repeat rewrite sm2_point_mul_one;
    entailer!.
Qed.

Lemma store_mont_wnaf3_precomp_focus_negative :
  forall positive negative point digit,
    wnaf3_digit digit -> digit < 0 ->
    store_mont_wnaf3_precomp positive negative point |--
      store_mont_afpoint
        (afpoint_array_slot negative (-digit))
        (sm2_point_negate (sm2_point_mul (-digit) point)) **
      store_mont_wnaf3_precomp_rest positive negative point digit.
Proof.
  intros positive negative point digit Hdigit Hnegative.
  destruct (wnaf3_negative_digit_cases digit Hdigit Hnegative) as [-> | ->];
    unfold store_mont_wnaf3_precomp,
      store_mont_wnaf3_precomp_rest;
    repeat destruct Z.eq_dec; try lia;
    repeat rewrite sm2_point_mul_one;
    entailer!.
Qed.

Lemma store_mont_wnaf3_precomp_restore_positive :
  forall positive negative point digit,
    wnaf3_digit digit -> digit > 0 ->
    store_mont_afpoint
      (afpoint_array_slot positive digit)
      (sm2_point_mul digit point) **
    store_mont_wnaf3_precomp_rest positive negative point digit |--
      store_mont_wnaf3_precomp positive negative point.
Proof.
  intros positive negative point digit Hdigit Hpositive.
  destruct (wnaf3_positive_digit_cases digit Hdigit Hpositive) as [-> | ->];
    unfold store_mont_wnaf3_precomp,
      store_mont_wnaf3_precomp_rest;
    repeat destruct Z.eq_dec; try lia;
    repeat rewrite sm2_point_mul_one;
    entailer!.
Qed.

Lemma store_mont_wnaf3_precomp_restore_negative :
  forall positive negative point digit,
    wnaf3_digit digit -> digit < 0 ->
    store_mont_afpoint
      (afpoint_array_slot negative (-digit))
      (sm2_point_negate (sm2_point_mul (-digit) point)) **
    store_mont_wnaf3_precomp_rest positive negative point digit |--
      store_mont_wnaf3_precomp positive negative point.
Proof.
  intros positive negative point digit Hdigit Hnegative.
  destruct (wnaf3_negative_digit_cases digit Hdigit Hnegative) as [-> | ->];
    unfold store_mont_wnaf3_precomp,
      store_mont_wnaf3_precomp_rest;
    repeat destruct Z.eq_dec; try lia;
    repeat rewrite sm2_point_mul_one;
    entailer!.
Qed.

(** * Small scalar facts used by the precomputation proof *)

Lemma sm2_point_mul_three_intro :
  forall point doubled triple,
    sm2_point_double point = doubled ->
    sm2_point_add doubled point = triple ->
    sm2_point_mul 3 point = triple.
Proof.
  intros point doubled triple Hdouble Hadd.
  rewrite sm2_point_mul_three, Hdouble.
  exact Hadd.
Qed.
