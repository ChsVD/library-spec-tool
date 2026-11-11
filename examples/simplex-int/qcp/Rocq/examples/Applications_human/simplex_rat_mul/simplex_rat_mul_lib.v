From Coq Require Import ZArith Lia.
From SimpleC.EE.Applications_human.simplex_checked_mul
  Require Export simplex_checked_mul_lib.
From SimpleC.EE.Applications_human.simplex_rat_reduce
  Require Export simplex_rat_reduce_lib.
Local Open Scope Z_scope.

(* Reference audit: FME fme.c:207-215 computes positive gcd quotients
   before coefficient scaling; fme_proof_manual.v:574-613 bounds scaled
   coefficients using Z_mult_quot_ge/le. implement_lemma.v:293-353 only
   establishes positive quotients for two strictly positive gcd inputs.
   algorithm.v:196-218 establishes integer coefficient linear scaling,
   not rational multiplication. The checked-product bounds and signed,
   zero-inclusive exact normalization adaptations already exist in the
   imported verified libraries. Only their composition is new here.
   Stage4 candidate items arith/guards/norm/ops and review are design
   references, not assumptions. No C execution or ABI model is asserted. *)

Definition simplex_rat_mul_flag (a b c d : Z) : Z :=
  if Z.eqb (checked_mul_flag a c) 1
  then checked_mul_flag b d else 0.

(* Exact normalized product: the imported relation fixes both quotients;
   it does not allow an arbitrary common scaling factor. *)
Definition simplex_rat_mul_result (a b c d p q : Z) : Prop :=
  simplex_rat_reduce_result (a*c) (b*d) p q.

Lemma simplex_rat_mul_flag_range : forall a b c d,
  simplex_rat_mul_flag a b c d = 0 \/ simplex_rat_mul_flag a b c d = 1.
Proof.
  intros. unfold simplex_rat_mul_flag. destruct (Z.eqb _ _).
  - apply checked_mul_flag_range.
  - auto.
Qed.

Lemma simplex_rat_mul_flag_success : forall a b c d,
  simplex_rat_mul_flag a b c d = 1 <->
  checked_mul_flag a c = 1 /\ checked_mul_flag b d = 1.
Proof.
  intros. unfold simplex_rat_mul_flag.
  destruct (Z.eqb (checked_mul_flag a c) 1) eqn:H.
  - apply Z.eqb_eq in H. intuition.
  - apply Z.eqb_neq in H. intuition lia.
Qed.

(* Records short-circuit failure responsibility: second check is relevant
   only after the numerator check succeeds. *)
Lemma simplex_rat_mul_flag_failure_ordered : forall a b c d,
  simplex_rat_mul_flag a b c d = 0 <->
  checked_mul_flag a c = 0 \/
  (checked_mul_flag a c = 1 /\ checked_mul_flag b d = 0).
Proof.
  intros. pose proof (checked_mul_flag_range a c) as HN.
  pose proof (checked_mul_flag_range b d) as HD.
  unfold simplex_rat_mul_flag.
  destruct (Z.eqb (checked_mul_flag a c) 1) eqn:H;
    [apply Z.eqb_eq in H | apply Z.eqb_neq in H]; intuition lia.
Qed.

Lemma simplex_rat_mul_success_iff : forall a b c d,
  1 <= b -> 1 <= d ->
  (simplex_rat_mul_flag a b c d = 1 <->
   a <> -2147483648 /\ c <> -2147483648 /\
   Z.abs (a*c) <= 2147483647 /\ b*d <= 2147483647).
Proof.
  intros a b c d Hb Hd.
  rewrite simplex_rat_mul_flag_success, !checked_mul_flag_success_iff.
  rewrite (Z.abs_eq (b*d)) by nia. intuition lia.
Qed.

Lemma simplex_rat_mul_failure_iff : forall a b c d,
  1 <= b -> 1 <= d ->
  (simplex_rat_mul_flag a b c d = 0 <->
   a = -2147483648 \/ c = -2147483648 \/
   2147483647 < Z.abs (a*c) \/ 2147483647 < b*d).
Proof.
  intros a b c d Hb Hd.
  pose proof (simplex_rat_mul_success_iff a b c d Hb Hd).
  pose proof (simplex_rat_mul_flag_range a b c d).
  destruct (Z.eq_dec a (-2147483648));
  destruct (Z.eq_dec c (-2147483648));
  destruct (Z_le_dec (Z.abs (a*c)) 2147483647);
  destruct (Z_le_dec (b*d) 2147483647); intuition lia.
Qed.

(* These are callee preconditions derived on the successful path, never
   entrance restrictions on rational multiplication. *)
Lemma simplex_rat_mul_reduce_inputs : forall a b c d,
  1 <= b -> 1 <= d -> simplex_rat_mul_flag a b c d = 1 ->
  -2147483647 <= a*c <= 2147483647 /\ 1 <= b*d <= 2147483647.
Proof.
  intros a b c d Hb Hd H.
  apply simplex_rat_mul_flag_success in H. destruct H as [HN HD].
  pose proof (checked_mul_success_product_range a c HN).
  pose proof (checked_mul_success_product_range b d HD). split; nia.
Qed.

Lemma simplex_rat_mul_result_unique : forall a b c d p q p' q',
  simplex_rat_mul_result a b c d p q ->
  simplex_rat_mul_result a b c d p' q' -> p = p' /\ q = q'.
Proof. intros. eapply simplex_rat_reduce_unique; eassumption. Qed.

Lemma simplex_rat_mul_properties : forall a b c d p q,
  1 <= b -> 1 <= d -> simplex_rat_mul_flag a b c d = 1 ->
  simplex_rat_mul_result a b c d p q ->
  -2147483647 <= p <= 2147483647 /\ 1 <= q <= 2147483647 /\
  Z.gcd (Z.abs p) q = 1 /\ (a*c)*q = p*(b*d) /\
  (a*c = 0 -> p = 0 /\ q = 1).
Proof.
  intros a b c d p q Hb Hd HF HR.
  destruct (simplex_rat_mul_reduce_inputs a b c d Hb Hd HF) as [HN HD].
  pose proof (simplex_rat_reduce_properties (a*c) (b*d) p q
    2147483647 HN HD HR) as [HP [HQ [HG [HV [HZ _]]]]].
  auto.
Qed.

(* Rational equality is expressed by integer cross multiplication with
   positive denominators; no division rounded toward zero is substituted
   for the rational values of the inputs. *)
Lemma simplex_rat_mul_value : forall a b c d p q,
  0 < b -> 0 < d -> simplex_rat_mul_result a b c d p q ->
  0 < q /\ (a*c)*q = p*(b*d).
Proof.
  intros a b c d p q Hb Hd [HP HQ].
  pose proof (simplex_rat_reduce_den_bounds (a*c) (b*d) ltac:(nia)).
  pose proof (simplex_rat_reduce_value (a*c) (b*d) ltac:(nia)).
  rewrite HP, HQ. split; lia.
Qed.

Lemma simplex_rat_mul_integer_zero : forall k,
  -2147483647 <= k <= 2147483647 ->
  simplex_rat_mul_flag k 1 0 1 = 1 /\
  simplex_rat_mul_result k 1 0 1 0 1 /\
  simplex_rat_mul_flag 0 1 k 1 = 1 /\
  simplex_rat_mul_result 0 1 k 1 0 1.
Proof.
  intros k Hk.
  assert (Hk0 : checked_mul_flag k 0 = 1).
  { apply (proj1 (checked_mul_zero_success k 0 ltac:(lia) ltac:(lia) ltac:(auto))). }
  assert (H0k : checked_mul_flag 0 k = 1).
  { apply (proj1 (checked_mul_zero_success 0 k ltac:(lia) ltac:(lia) ltac:(auto))). }
  assert (H11 : checked_mul_flag 1 1 = 1) by (apply checked_mul_one_success; lia).
  split; [apply simplex_rat_mul_flag_success; auto |].
  split.
  - unfold simplex_rat_mul_result. rewrite Z.mul_0_r, Z.mul_1_l.
    apply simplex_rat_reduce_zero; lia.
  - split; [apply simplex_rat_mul_flag_success; auto |].
    unfold simplex_rat_mul_result. rewrite Z.mul_0_l, Z.mul_1_l.
    apply simplex_rat_reduce_zero; lia.
Qed.

Lemma simplex_rat_mul_min_rejected : forall a b c d,
  a = -2147483648 \/ c = -2147483648 ->
  simplex_rat_mul_flag a b c d = 0.
Proof.
  intros a b c d H. unfold simplex_rat_mul_flag.
  rewrite checked_mul_min_rejected by exact H. reflexivity.
Qed.

(* Zero numerator does not bypass the denominator product check. *)
Example simplex_rat_mul_zero_den_overflow :
  simplex_rat_mul_flag 0 2147483647 1 2 = 0.
Proof. vm_compute. reflexivity. Qed.

(* The mathematical answer 1/1 exists and is representable, but the
   pre-reduction products fail; rejection is not mathematical insolvability. *)
Example simplex_rat_mul_representable_rejected :
  simplex_rat_mul_flag 2147483647 2147483647 2 2 = 0 /\
  simplex_rat_mul_result 2147483647 2147483647 2 2 1 1.
Proof. vm_compute. auto. Qed.
