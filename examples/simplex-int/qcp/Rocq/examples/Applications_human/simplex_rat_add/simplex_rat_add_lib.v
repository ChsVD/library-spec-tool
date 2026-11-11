From Coq Require Import ZArith Lia Bool.
From SimpleC.EE.Applications_human.simplex_checked_add
  Require Export simplex_checked_add_lib.
From SimpleC.EE.Applications_human.simplex_checked_mul
  Require Export simplex_checked_mul_lib.
From SimpleC.EE.Applications_human.simplex_rat_reduce
  Require Export simplex_rat_reduce_lib.
From SimpleC.EE.Applications_human.simplex_rat_mul
  Require Export simplex_rat_mul_lib.
Local Open Scope Z_scope.

(* Reference audit (SPECIFICATION_WRITING_OPTIMIZATION 2026-11-02):
   FME fme.c:59-72 supplies a sufficient-only symmetric-domain sum check;
   fme.c:207-215 scales integer coefficients using positive gcd quotients.
   implement_lemma.v:293-353 proves positivity only for strictly positive
   dividends; algorithm.v:196-218 proves integer linear scaling/addition.
   fme_proof_manual.v:574-613 bounds those scaled coefficients.
   These are not a complete rational-addition library. Signed and zero
   normalization and exact checked arithmetic are imported above.
   New material only composes checks, normalization and caller cases. *)

Definition simplex_rat_add_flag (a b c d : Z) : Z :=
  if Z.eqb (checked_mul_flag a d) 1 then
    if Z.eqb (checked_mul_flag c b) 1 then
      if Z.eqb (checked_add_flag (a*d) (c*b)) 1 then
        checked_mul_flag b d
      else 0
    else 0
  else 0.

(* One case-level mathematical interface; each quotient is deterministic.
   There is no input-range or ownership condition in the result relation. *)
Definition simplex_rat_add_result (a b c d p q : Z) : Prop :=
  simplex_rat_reduce_result (a*d+c*b) (b*d) p q.

Lemma simplex_rat_add_flag_range : forall a b c d,
  simplex_rat_add_flag a b c d = 0 \/ simplex_rat_add_flag a b c d = 1.
Proof.
  intros. unfold simplex_rat_add_flag.
  repeat destruct (Z.eqb _ _); auto using checked_mul_flag_range.
Qed.

Lemma simplex_rat_add_flag_success : forall a b c d,
  simplex_rat_add_flag a b c d = 1 <->
  checked_mul_flag a d = 1 /\ checked_mul_flag c b = 1 /\
  checked_add_flag (a*d) (c*b) = 1 /\ checked_mul_flag b d = 1.
Proof.
  intros. unfold simplex_rat_add_flag.
  destruct (Z.eqb (checked_mul_flag a d) 1) eqn:H1;
  destruct (Z.eqb (checked_mul_flag c b) 1) eqn:H2;
  destruct (Z.eqb (checked_add_flag (a*d) (c*b)) 1) eqn:H3;
  repeat match goal with
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  end; intuition lia.
Qed.

Lemma simplex_rat_add_flag_failure_ordered : forall a b c d,
  simplex_rat_add_flag a b c d = 0 <->
  checked_mul_flag a d = 0 \/
  (checked_mul_flag a d = 1 /\ checked_mul_flag c b = 0) \/
  (checked_mul_flag a d = 1 /\ checked_mul_flag c b = 1 /\
   checked_add_flag (a*d) (c*b) = 0) \/
  (checked_mul_flag a d = 1 /\ checked_mul_flag c b = 1 /\
   checked_add_flag (a*d) (c*b) = 1 /\ checked_mul_flag b d = 0).
Proof.
  intros.
  pose proof (checked_mul_flag_range a d).
  pose proof (checked_mul_flag_range c b).
  pose proof (checked_add_flag_range (a*d) (c*b)).
  pose proof (checked_mul_flag_range b d).
  pose proof (simplex_rat_add_flag_range a b c d).
  pose proof (simplex_rat_add_flag_success a b c d).
  intuition lia.
Qed.

(* Equivalence in the selected natural domain, without requiring any check
   in advance. The sum bound alone cannot replace the two product checks. *)
Lemma simplex_rat_add_success_iff : forall a b c d,
  -2147483647 <= a <= 2147483647 ->
  -2147483647 <= c <= 2147483647 ->
  1 <= b <= 2147483647 -> 1 <= d <= 2147483647 ->
  (simplex_rat_add_flag a b c d = 1 <->
   Z.abs (a*d) <= 2147483647 /\ Z.abs (c*b) <= 2147483647 /\
   -2147483647 <= a*d+c*b <= 2147483647 /\ b*d <= 2147483647).
Proof.
  intros a b c d Ha Hc Hb Hd.
  rewrite simplex_rat_add_flag_success, !checked_mul_flag_success_iff,
    checked_add_flag_success_iff.
  rewrite (Z.abs_eq (b*d)) by nia.
  split.
  - intuition.
  - intros [HP [HQ [HN HE]]].
    apply Z.abs_le in HP. apply Z.abs_le in HQ. intuition lia.
Qed.

(* Only after a successful return are these callee input bounds derived. *)
Lemma simplex_rat_add_reduce_inputs : forall a b c d,
  1 <= b -> 1 <= d -> simplex_rat_add_flag a b c d = 1 ->
  -2147483647 <= a*d+c*b <= 2147483647 /\
  1 <= b*d <= 2147483647.
Proof.
  intros a b c d Hb Hd H.
  apply simplex_rat_add_flag_success in H.
  destruct H as [_ [_ [HN HE]]].
  apply checked_add_flag_success_iff in HN.
  pose proof (checked_mul_success_product_range b d HE). split; nia.
Qed.

Lemma simplex_rat_add_result_unique : forall a b c d p q p' q',
  simplex_rat_add_result a b c d p q ->
  simplex_rat_add_result a b c d p' q' -> p = p' /\ q = q'.
Proof. intros. eapply simplex_rat_reduce_unique; eassumption. Qed.

Lemma simplex_rat_add_properties : forall a b c d p q,
  1 <= b -> 1 <= d -> simplex_rat_add_flag a b c d = 1 ->
  simplex_rat_add_result a b c d p q ->
  -2147483647 <= p <= 2147483647 /\ 1 <= q <= 2147483647 /\
  Z.gcd (Z.abs p) q = 1 /\ (a*d+c*b)*q = p*(b*d) /\
  (a*d+c*b = 0 -> p = 0 /\ q = 1).
Proof.
  intros a b c d p q Hb Hd HF HR.
  destruct (simplex_rat_add_reduce_inputs a b c d Hb Hd HF) as [HN HE].
  pose proof (simplex_rat_reduce_properties (a*d+c*b) (b*d) p q
    2147483647 HN HE HR) as [HP [HQ [HG [HV [HZ _]]]]].
  auto.
Qed.

(* Rational sum equality is integer cross multiplication, never truncated
   integer division substituted for either input rational value. *)
Lemma simplex_rat_add_value : forall a b c d p q,
  0 < b -> 0 < d -> simplex_rat_add_result a b c d p q ->
  0 < q /\ (a*d+c*b)*q = p*(b*d).
Proof.
  intros a b c d p q Hb Hd [HP HQ].
  pose proof (simplex_rat_reduce_den_bounds (a*d+c*b) (b*d) ltac:(nia)).
  pose proof (simplex_rat_reduce_value (a*d+c*b) (b*d) ltac:(nia)).
  rewrite HP, HQ. split; lia.
Qed.

Lemma simplex_rat_add_cancellation : forall a b c d,
  0 < b -> 0 < d -> a*d+c*b = 0 ->
  simplex_rat_add_result a b c d 0 1.
Proof.
  intros a b c d Hb Hd HN. unfold simplex_rat_add_result.
  rewrite HN. apply simplex_rat_reduce_zero; nia.
Qed.

(* Caller initialization: endpoints included, no nonzero restriction. *)
Lemma simplex_rat_add_integer_zero : forall a,
  -2147483647 <= a <= 2147483647 ->
  simplex_rat_add_flag a 1 0 1 = 1 /\
  simplex_rat_add_result a 1 0 1 a 1.
Proof.
  intros a Ha. split.
  - apply simplex_rat_add_flag_success.
    rewrite Z.mul_1_r, Z.mul_0_l.
    repeat split; try (apply checked_mul_one_success; lia).
    apply (proj1 (checked_add_zero_success a Ha)).
  - unfold simplex_rat_add_result.
    rewrite Z.mul_1_r, Z.mul_0_l, Z.add_0_r, Z.mul_1_l.
    apply simplex_rat_reduce_already_reduced.
    apply Z.gcd_1_r.
Qed.

Example simplex_rat_add_positive_endpoint :
  simplex_rat_add_flag 2147483647 1 0 1 = 1 /\
  simplex_rat_add_result 2147483647 1 0 1 2147483647 1.
Proof. apply simplex_rat_add_integer_zero; lia. Qed.

Example simplex_rat_add_negative_endpoint :
  simplex_rat_add_flag (-2147483647) 1 0 1 = 1 /\
  simplex_rat_add_result (-2147483647) 1 0 1 (-2147483647) 1.
Proof. apply simplex_rat_add_integer_zero; lia. Qed.

(* Even cancellation does not bypass the final denominator check. *)
Example simplex_rat_add_zero_den_overflow :
  simplex_rat_add_flag 1 50000 (-1) 50000 = 0 /\
  simplex_rat_add_result 1 50000 (-1) 50000 0 1.
Proof. vm_compute. auto. Qed.

(* A representable mathematical answer may be rejected before reduction. *)
Example simplex_rat_add_representable_rejected :
  simplex_rat_add_flag 2147483647 2147483647 1 1 = 0 /\
  simplex_rat_add_result 2147483647 2147483647 1 1 2 1.
Proof. vm_compute. auto. Qed.
