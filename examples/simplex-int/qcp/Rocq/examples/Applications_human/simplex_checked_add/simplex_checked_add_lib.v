From Coq Require Import ZArith Lia Bool.
Local Open Scope Z_scope.

(* FME reference: fme/QCP_examples/fme.c:59-72; fme/Rocq/fme_goal.v:
   126-177 (threshold safety), 179-213 (return witnesses).
   Its contract is sufficient-only on [-M,M]. The following arithmetic
   extracts that actual sign/threshold argument and proves its converse.
   No FME theorem/axiom is imported; its automatic proof entry points are
   fme_proof_auto.v:16-43, with no same-named manual proof. *)
Lemma fme_add_threshold_iff : forall M x y,
  0 <= M -> -M <= x <= M -> -M <= y <= M ->
  ((0 < x /\ y <= M-x) \/ (x <= 0 /\ -M-x <= y) <->
   -M <= x+y <= M).
Proof. intros; lia. Qed.

Lemma fme_add_threshold_bounds : forall M x,
  0 <= M -> -M <= x <= M ->
  (0 < x -> 0 <= M-x <= M) /\
  (x <= 0 -> -M <= -M-x <= 0).
Proof. intros; lia. Qed.

(* Adaptation: commute operands to the target's Y sign split.  The
   target omits the lower check when Y=0, so that case is proved too. *)
Lemma add_y_threshold_iff : forall M x y,
  0 <= M -> -M <= x <= M -> -M <= y <= M ->
  ((0 < y -> x <= M-y) /\ (y < 0 -> -M-y <= x) <->
   -M <= x+y <= M).
Proof.
  intros M x y HM Hx Hy.
  pose proof (fme_add_threshold_iff M y x HM Hy Hx) as Href.
  rewrite (Z.add_comm x y). rewrite <- Href.
  destruct (Z_lt_ge_dec 0 y); destruct (Z_lt_ge_dec y 0); intuition lia.
Qed.

(* Exact mathematical return value; INT_MIN exclusion is answer semantics,
   not a restriction of the input domain or an ownership predicate. *)
Definition checked_add_flag (x y : Z) : Z :=
  if (negb (Z.eqb x (-2147483648)) &&
      negb (Z.eqb y (-2147483648)) &&
      Z.leb (-2147483647) (x+y) &&
      Z.leb (x+y) 2147483647)%bool then 1 else 0.

Lemma checked_add_flag_success_iff : forall x y,
  checked_add_flag x y = 1 <->
  x <> -2147483648 /\ y <> -2147483648 /\
  -2147483647 <= x+y <= 2147483647.
Proof.
  intros x y. unfold checked_add_flag.
  destruct (_ && _ && _ && _)%bool eqn:H.
  - rewrite !Bool.andb_true_iff, !Bool.negb_true_iff,
      !Z.eqb_neq, !Z.leb_le in H. tauto.
  - split; [lia | intros [Hx [Hy Hs]]].
    assert ((negb (x =? -2147483648) && negb (y =? -2147483648) &&
      (-2147483647 <=? x+y) && (x+y <=? 2147483647))%bool = true).
    { rewrite !Bool.andb_true_iff, !Bool.negb_true_iff,
        !Z.eqb_neq, !Z.leb_le. tauto. }
    congruence.
Qed.

Lemma checked_add_flag_range : forall x y,
  checked_add_flag x y = 0 \/ checked_add_flag x y = 1.
Proof. intros; unfold checked_add_flag; destruct (_ && _ && _ && _)%bool; auto. Qed.

Lemma checked_add_flag_failure_iff : forall x y,
  checked_add_flag x y = 0 <->
  x = -2147483648 \/ y = -2147483648 \/
  x+y < -2147483647 \/ 2147483647 < x+y.
Proof.
  intros x y. pose proof (checked_add_flag_success_iff x y).
  pose proof (checked_add_flag_range x y).
  destruct (Z.eq_dec x (-2147483648));
  destruct (Z.eq_dec y (-2147483648));
  destruct (Z_le_dec (-2147483647) (x+y));
  destruct (Z_le_dec (x+y) 2147483647); intuition lia.
Qed.

(* New full-int32 extension and exact refusal equivalence. FME's symmetric
   entrance is recovered only after the explicit non-INT_MIN path facts. *)
Lemma checked_add_guard_success_iff : forall x y,
  -2147483648 <= x <= 2147483647 ->
  -2147483648 <= y <= 2147483647 ->
  (checked_add_flag x y = 1 <->
   x <> -2147483648 /\ y <> -2147483648 /\
   (0 < y -> x <= 2147483647-y) /\
   (y < 0 -> -2147483647-y <= x)).
Proof.
  intros x y Hx Hy. rewrite checked_add_flag_success_iff.
  destruct (Z.eq_dec x (-2147483648));
  destruct (Z.eq_dec y (-2147483648)); try tauto.
  rewrite <- (add_y_threshold_iff 2147483647 x y ltac:(lia)
    ltac:(lia) ltac:(lia)). tauto.
Qed.

Lemma checked_add_guard_rejection_iff : forall x y,
  -2147483648 <= x <= 2147483647 ->
  -2147483648 <= y <= 2147483647 ->
  (checked_add_flag x y = 0 <->
   x = -2147483648 \/ y = -2147483648 \/
   (0 < y /\ 2147483647-y < x) \/
   (y < 0 /\ x < -2147483647-y)).
Proof.
  intros x y Hx Hy.
  pose proof (checked_add_guard_success_iff x y Hx Hy) as Href.
  pose proof (checked_add_flag_range x y) as Hr.
  destruct (Z.eq_dec x (-2147483648));
  destruct (Z.eq_dec y (-2147483648));
  destruct (Z_lt_ge_dec 0 y); destruct (Z_lt_ge_dec y 0);
  destruct (Z_le_dec x (2147483647-y));
  destruct (Z_le_dec (-2147483647-y) x); intuition lia.
Qed.

Lemma checked_add_threshold_safety : forall x y,
  -2147483648 <= x <= 2147483647 ->
  -2147483648 <= y <= 2147483647 -> y <> -2147483648 ->
  (0 < y -> 0 <= 2147483647-y <= 2147483646) /\
  (y < 0 -> -2147483646 <= -2147483647-y <= 0).
Proof.
  intros x y Hx Hy Hn.
  pose proof (fme_add_threshold_bounds 2147483647 y ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma checked_add_min_rejected : forall x y,
  x = -2147483648 \/ y = -2147483648 -> checked_add_flag x y = 0.
Proof. intros. apply checked_add_flag_failure_iff. tauto. Qed.

Lemma checked_add_zero_success : forall x,
  -2147483647 <= x <= 2147483647 ->
  checked_add_flag x 0 = 1 /\ checked_add_flag 0 x = 1.
Proof. intros; split; apply checked_add_flag_success_iff; intuition lia. Qed.

Lemma checked_add_min_sum_rejected : forall x y,
  x+y = -2147483648 -> checked_add_flag x y = 0.
Proof. intros. apply checked_add_flag_failure_iff. intuition lia. Qed.
