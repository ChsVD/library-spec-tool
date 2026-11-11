From Coq Require Import ZArith Lia.
From SimpleC.EE.Applications_human.simplex_rat_mul
  Require Export simplex_rat_mul_lib.
Local Open Scope Z_scope.

(* Sources actually read: FME fme.c:185-225, implement_lemma.v:293-353,
   fme_proof_manual.v:574-613, algorithm.v:196-218. FME scales integer
   coefficients by positive gcd quotients; it does not specify rational
   division or signed denominator normalization. Reuse the verified
   checked-product composition and signed/zero numerator reduction below.
   Input bounds and ownership remain in the future C contracts. *)
Definition simplex_rat_div_flag (a b c e : Z) : Z :=
  if Z.eqb c 0 then 0 else simplex_rat_mul_flag a b e c.

(* Both fields are uniquely fixed by the imported exact quotient relation.
   The mathematical result is conditional on nonzero divisor; a zero
   divisor is rejected by flag, rather than given a rational meaning. *)
Definition simplex_rat_div_result (a b c e p q : Z) : Prop :=
  simplex_rat_reduce_result
    (if Z.ltb (b*c) 0 then -(a*e) else a*e) (Z.abs (b*c)) p q.

Lemma simplex_rat_div_flag_range : forall a b c e,
  simplex_rat_div_flag a b c e = 0 \/ simplex_rat_div_flag a b c e = 1.
Proof.
  intros. unfold simplex_rat_div_flag. destruct (Z.eqb c 0).
  - auto.
  - apply simplex_rat_mul_flag_range.
Qed.

Lemma simplex_rat_div_zero_rejected : forall a b e,
  simplex_rat_div_flag a b 0 e = 0.
Proof. reflexivity. Qed.

Lemma simplex_rat_div_flag_success : forall a b c e,
  simplex_rat_div_flag a b c e = 1 <->
  c <> 0 /\ checked_mul_flag a e = 1 /\ checked_mul_flag b c = 1.
Proof.
  intros. unfold simplex_rat_div_flag. destruct (Z.eqb c 0) eqn:H.
  - apply Z.eqb_eq in H. intuition lia.
  - apply Z.eqb_neq in H. rewrite simplex_rat_mul_flag_success. tauto.
Qed.

Lemma simplex_rat_div_failure_ordered : forall a b c e,
  simplex_rat_div_flag a b c e = 0 <->
  c = 0 \/ (c <> 0 /\ checked_mul_flag a e = 0) \/
  (c <> 0 /\ checked_mul_flag a e = 1 /\ checked_mul_flag b c = 0).
Proof.
  intros. unfold simplex_rat_div_flag. destruct (Z.eqb c 0) eqn:H.
  - apply Z.eqb_eq in H. intuition.
  - apply Z.eqb_neq in H. rewrite simplex_rat_mul_flag_failure_ordered. tauto.
Qed.

(* Derived successful-path facts, never entrance assumptions. *)
Lemma simplex_rat_div_reduce_inputs : forall a b c e,
  1 <= b -> simplex_rat_div_flag a b c e = 1 ->
  -2147483647 <= (if Z.ltb (b*c) 0 then -(a*e) else a*e) <= 2147483647 /\
  1 <= Z.abs (b*c) <= 2147483647.
Proof.
  intros a b c e Hb HF. apply simplex_rat_div_flag_success in HF.
  destruct HF as [Hc [HN HD]].
  pose proof (checked_mul_success_product_range a e HN) as HP.
  pose proof (checked_mul_success_product_range b c HD) as HQ.
  assert (b*c <> 0) by nia.
  destruct (Z.ltb (b*c) 0) eqn:HS.
  - apply Z.ltb_lt in HS. rewrite Z.abs_neq by lia. split; lia.
  - apply Z.ltb_ge in HS. rewrite Z.abs_eq by lia. split; lia.
Qed.

Lemma simplex_rat_div_normalized_bridge : forall a b c e p q,
  0 < b -> c <> 0 ->
  simplex_rat_div_result a b c e p q ->
  0 < q /\ (a*e)*q = p*(b*c).
Proof.
  intros a b c e p q Hb Hc HR.
  unfold simplex_rat_div_result in HR.
  assert (HD : 0 < Z.abs (b*c)).
  { apply Z.abs_pos. nia. }
  pose proof (simplex_rat_reduce_den_bounds
    (if Z.ltb (b*c) 0 then -(a*e) else a*e) (Z.abs (b*c)) HD) as HQ.
  pose proof (simplex_rat_reduce_value
    (if Z.ltb (b*c) 0 then -(a*e) else a*e) (Z.abs (b*c)) HD) as HV.
  destruct HR as [HP HE]. rewrite <- HE in HQ. rewrite <- HP, <- HE in HV.
  destruct (Z.ltb (b*c) 0) eqn:HS.
  - apply Z.ltb_lt in HS. rewrite Z.abs_neq in HV by lia. split; nia.
  - apply Z.ltb_ge in HS. rewrite Z.abs_eq in HV by lia. split; nia.
Qed.

Lemma simplex_rat_div_result_unique : forall a b c e p q p' q',
  simplex_rat_div_result a b c e p q ->
  simplex_rat_div_result a b c e p' q' -> p = p' /\ q = q'.
Proof. intros. eapply simplex_rat_reduce_unique; eassumption. Qed.

Lemma simplex_rat_div_properties : forall a b c e p q,
  1 <= b -> simplex_rat_div_flag a b c e = 1 ->
  simplex_rat_div_result a b c e p q ->
  -2147483647 <= p <= 2147483647 /\ 1 <= q <= 2147483647 /\
  Z.gcd (Z.abs p) q = 1 /\ (a*e)*q = p*(b*c) /\
  (a = 0 -> p = 0 /\ q = 1).
Proof.
  intros a b c e p q Hb HF HR.
  destruct (simplex_rat_div_reduce_inputs a b c e Hb HF) as [HN HD].
  pose proof (simplex_rat_reduce_properties
    (if Z.ltb (b*c) 0 then -(a*e) else a*e) (Z.abs (b*c)) p q
    2147483647 HN HD HR) as [HP [HQ [HG [HV [HZ _]]]]].
  pose proof (simplex_rat_div_flag_success a b c e) as HFS.
  apply HFS in HF. destruct HF as [Hc _].
  pose proof (simplex_rat_div_normalized_bridge a b c e p q ltac:(lia) Hc HR)
    as [_ HE].
  split; [exact HP |]. split; [exact HQ |]. split; [exact HG |]. split; [exact HE |].
  intros Ha. apply HZ. rewrite Ha. destruct (Z.ltb (b*c) 0); ring.
Qed.

(* Boundary diagnostics for the pure model, not C call tests. *)
Example simplex_rat_div_negative_divisor :
  simplex_rat_div_flag 1 2 (-3) 4 = 1 /\
  simplex_rat_div_result 1 2 (-3) 4 (-2) 3.
Proof. vm_compute. auto. Qed.

Example simplex_rat_div_zero_numerator_second_rejected :
  simplex_rat_div_flag 0 2147483647 2 1 = 0.
Proof. vm_compute. reflexivity. Qed.

Example simplex_rat_div_representable_rejected :
  simplex_rat_div_flag 2147483647 2147483647 2 2 = 0 /\
  simplex_rat_div_result 2147483647 2147483647 2 2 1 1.
Proof. vm_compute. auto. Qed.



(* Exact predicate on the selected natural-spec domain; no nonzero or
   no-overflow precondition is imposed on callers. *)
Lemma simplex_rat_div_success_iff : forall a b c e,
  -2147483647 <= a <= 2147483647 ->
  -2147483647 <= c <= 2147483647 ->
  1 <= b <= 2147483647 -> 1 <= e <= 2147483647 ->
  (simplex_rat_div_flag a b c e = 1 <->
   c <> 0 /\ Z.abs (a*e) <= 2147483647 /\ Z.abs (b*c) <= 2147483647).
Proof.
  intros a b c e Ha Hc Hb He.
  rewrite simplex_rat_div_flag_success, !checked_mul_flag_success_iff.
  intuition lia.
Qed.

Lemma simplex_rat_div_failure_iff : forall a b c e,
  -2147483647 <= a <= 2147483647 ->
  -2147483647 <= c <= 2147483647 ->
  1 <= b <= 2147483647 -> 1 <= e <= 2147483647 ->
  (simplex_rat_div_flag a b c e = 0 <->
   c = 0 \/ 2147483647 < Z.abs (a*e) \/ 2147483647 < Z.abs (b*c)).
Proof.
  intros a b c e Ha Hc Hb He.
  pose proof (simplex_rat_div_success_iff a b c e Ha Hc Hb He).
  pose proof (simplex_rat_div_flag_range a b c e).
  destruct (Z.eq_dec c 0);
  destruct (Z_le_dec (Z.abs (a*e)) 2147483647);
  destruct (Z_le_dec (Z.abs (b*c)) 2147483647); intuition lia.
Qed.
