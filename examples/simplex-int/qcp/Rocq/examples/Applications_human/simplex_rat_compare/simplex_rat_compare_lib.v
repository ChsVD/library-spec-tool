From Coq Require Import ZArith Lia.
From SimpleC.EE.Applications_human.simplex_rat_mul
  Require Export simplex_rat_mul_lib.
Local Open Scope Z_scope.

(* Reference audit (2026-11-02): FME fme.c:207-214 scales coefficients by
   positive gcd quotients; fme_proof_manual.v:574-613 uses positive scaling
   and Z_mult_quot_ge/le to bound products. algorithm.v:196-237 proves
   linear integer scaling, not a rational comparison interface. Existing
   checked_mul common already supplies the adapted exact signed threshold.
   Stage4 arith/guards/compare requirements are design references only.
   Here rational order is EXACT cross-product order for positive denominators,
   without integer division, reduction, or any machine-product-range premise. *)

(* Parameter permutation reuses precisely the two ordered cross checks:
   rat_mul(a,c,d,b) checks a*d first, then c*b. *)
Definition simplex_rat_compare_flag (a b c d : Z) : Z :=
  simplex_rat_mul_flag a c d b.

Definition simplex_rat_compare_order (a b c d : Z) : Z :=
  match Z.compare (a*d) (c*b) with
  | Lt => -1 | Eq => 0 | Gt => 1
  end.

Lemma simplex_rat_compare_flag_range : forall a b c d,
  simplex_rat_compare_flag a b c d = 0 \/
  simplex_rat_compare_flag a b c d = 1.
Proof. intros. apply simplex_rat_mul_flag_range. Qed.

Lemma simplex_rat_compare_flag_success : forall a b c d,
  simplex_rat_compare_flag a b c d = 1 <->
  checked_mul_flag a d = 1 /\ checked_mul_flag c b = 1.
Proof. intros. apply simplex_rat_mul_flag_success. Qed.

Lemma simplex_rat_compare_flag_failure_ordered : forall a b c d,
  simplex_rat_compare_flag a b c d = 0 <->
  checked_mul_flag a d = 0 \/
  (checked_mul_flag a d = 1 /\ checked_mul_flag c b = 0).
Proof. intros. apply simplex_rat_mul_flag_failure_ordered. Qed.

Lemma simplex_rat_compare_products : forall a b c d,
  simplex_rat_compare_flag a b c d = 1 ->
  -2147483647 <= a*d <= 2147483647 /\
  -2147483647 <= c*b <= 2147483647.
Proof.
  intros a b c d H. apply simplex_rat_compare_flag_success in H.
  destruct H as [HP HQ]. split; apply checked_mul_success_product_range; assumption.
Qed.

(* This is the exact three-way rational relation on positive denominators.
   It also characterizes every possible output, so no arbitrary witness can
   satisfy the result. The integer statement remains total beyond that domain. *)
Lemma simplex_rat_compare_order_spec : forall a b c d,
  (simplex_rat_compare_order a b c d = -1 <-> a*d < c*b) /\
  (simplex_rat_compare_order a b c d = 0 <-> a*d = c*b) /\
  (simplex_rat_compare_order a b c d = 1 <-> a*d > c*b).
Proof.
  intros. unfold simplex_rat_compare_order.
  destruct (Z.compare_spec (a*d) (c*b)); simpl; repeat split; lia.
Qed.

Lemma simplex_rat_compare_order_characterization : forall a b c d r,
  ((r = -1 /\ a*d < c*b) \/ (r = 0 /\ a*d = c*b) \/
   (r = 1 /\ a*d > c*b)) <-> r = simplex_rat_compare_order a b c d.
Proof.
  intros. unfold simplex_rat_compare_order.
  destruct (Z.compare_spec (a*d) (c*b)); simpl; intuition lia.
Qed.

Lemma simplex_rat_compare_order_range : forall a b c d,
  simplex_rat_compare_order a b c d = -1 \/
  simplex_rat_compare_order a b c d = 0 \/
  simplex_rat_compare_order a b c d = 1.
Proof. intros. unfold simplex_rat_compare_order. destruct (Z.compare _ _); auto. Qed.

(* Positive independent rescalings preserve the represented fractions and
   their comparison. This is the scalar adaptation of FME positive scaling;
   there is no claim to reuse its constraint/list types as fraction types. *)
Lemma simplex_rat_compare_positive_scale : forall a b c d k l,
  0 < k -> 0 < l ->
  simplex_rat_compare_order (k*a) (k*b) (l*c) (l*d) =
  simplex_rat_compare_order a b c d.
Proof.
  intros a b c d k l Hk Hl.
  assert (HK : 0 < k*l) by nia.
  assert (HP : (k*a)*(l*d) = (k*l)*(a*d)) by ring.
  assert (HQ : (l*c)*(k*b) = (k*l)*(c*b)) by ring.
  unfold simplex_rat_compare_order. rewrite HP, HQ.
  destruct (Z.compare_spec (a*d) (c*b));
  destruct (Z.compare_spec ((k*l)*(a*d)) ((k*l)*(c*b))); simpl; try reflexivity; nia.
Qed.

Example simplex_rat_compare_equal_unreduced :
  simplex_rat_compare_flag 1 2 2 4 = 1 /\
  simplex_rat_compare_order 1 2 2 4 = 0.
Proof. vm_compute. auto. Qed.

Example simplex_rat_compare_negative_and_zero :
  simplex_rat_compare_flag (-1) 2 0 3 = 1 /\
  simplex_rat_compare_order (-1) 2 0 3 = -1.
Proof. vm_compute. auto. Qed.

(* Rejection does not deny mathematical comparability. *)
Example simplex_rat_compare_min_rejected_but_ordered :
  simplex_rat_compare_flag (-2147483648) 1 0 1 = 0 /\
  simplex_rat_compare_order (-2147483648) 1 0 1 = -1.
Proof. vm_compute. auto. Qed.

Example simplex_rat_compare_second_product_overflow :
  checked_mul_flag 0 1 = 1 /\
  simplex_rat_compare_flag 0 2147483647 2 1 = 0 /\
  simplex_rat_compare_order 0 2147483647 2 1 = -1.
Proof. vm_compute. auto. Qed.