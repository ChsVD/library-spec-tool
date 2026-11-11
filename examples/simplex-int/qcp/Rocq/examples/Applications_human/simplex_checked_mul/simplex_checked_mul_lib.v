From Coq Require Import ZArith ZArith.Zquot Lia Bool.
Local Open Scope Z_scope.

(* Pure mathematical flag; no ownership or restriction of the input domain.
   Stage-four arith/guards are design references, not imported assumptions. *)
Definition checked_mul_flag (x y : Z) : Z :=
  if (negb (Z.eqb x (-2147483648)) &&
      negb (Z.eqb y (-2147483648)) &&
      Z.leb (Z.abs (x * y)) 2147483647)%bool then 1 else 0.

Lemma checked_mul_flag_success_iff : forall x y,
  checked_mul_flag x y = 1 <->
  x <> -2147483648 /\ y <> -2147483648 /\
  Z.abs (x * y) <= 2147483647.
Proof.
  intros x y. unfold checked_mul_flag.
  destruct (_ && _ && _)%bool eqn:H.
  - rewrite !Bool.andb_true_iff, !Bool.negb_true_iff,
      !Z.eqb_neq, Z.leb_le in H. tauto.
  - split; [lia | intros [Hx [Hy Hp]]].
    assert ((negb (x =? -2147483648) && negb (y =? -2147483648) &&
      (Z.abs (x * y) <=? 2147483647))%bool = true).
    { rewrite !Bool.andb_true_iff, !Bool.negb_true_iff,
        !Z.eqb_neq, Z.leb_le. tauto. }
    congruence.
Qed.

Lemma checked_mul_flag_range : forall x y,
  checked_mul_flag x y = 0 \/ checked_mul_flag x y = 1.
Proof. intros; unfold checked_mul_flag; destruct (_ && _ && _)%bool; auto. Qed.

Lemma checked_mul_flag_failure_iff : forall x y,
  checked_mul_flag x y = 0 <->
  x = -2147483648 \/ y = -2147483648 \/
  2147483647 < Z.abs (x * y).
Proof.
  intros x y. pose proof (checked_mul_flag_success_iff x y).
  pose proof (checked_mul_flag_range x y).
  destruct (Z.eq_dec x (-2147483648));
  destruct (Z.eq_dec y (-2147483648));
  destruct (Z_le_dec (Z.abs (x*y)) 2147483647); intuition lia.
Qed.

(* FME implement.v124-128 uses [-INT_MAX,INT_MAX], rather than the
   asymmetric machine domain. Adapted here without importing constraints. *)
Lemma int32_nonmin_abs_bound : forall x,
  -2147483648 <= x <= 2147483647 -> x <> -2147483648 ->
  0 <= Z.abs x <= 2147483647.
Proof.
  intros x H Hn. destruct (Z_le_dec 0 x).
  - rewrite Z.abs_eq; lia.
  - rewrite Z.abs_neq; lia.
Qed.

(* Adapt FME manual574-613: sandwich a product between scaled quotient
   endpoints, using exactly its two Zquot facts, generalized to bound M. *)
Lemma scaled_quot_interval : forall M b a,
  0 <= M -> 0 < b ->
  Z.quot (-M) b <= a <= Z.quot M b -> -M <= b*a <= M.
Proof.
  intros M b a HM Hb Ha.
  pose proof (Zquot.Z_mult_quot_ge (-M) b ltac:(lia)).
  pose proof (Zquot.Z_mult_quot_le M b HM).
  nia.
Qed.

(* Extend FME's sufficient upper bound to the exact rejection test.
   The reverse implication needs the positive remainder bound as well. *)
Lemma nonnegative_quot_product_iff : forall M a b,
  0 <= M -> 0 <= a -> 0 < b ->
  (a <= Z.quot M b <-> a*b <= M).
Proof.
  intros M a b HM Ha Hb.
  pose proof (Zquot.Z_mult_quot_le M b HM).
  pose proof (Z.quot_rem M b ltac:(lia)).
  pose proof (Z.rem_bound_pos M b HM Hb).
  split; intros; nia.
Qed.

Lemma abs_product_quot_iff : forall M x y,
  0 <= M -> Z.abs y <> 0 ->
  (Z.abs x <= Z.quot M (Z.abs y) <-> Z.abs (x*y) <= M).
Proof.
  intros M x y HM Hy. rewrite Z.abs_mul.
  pose proof (Z.abs_nonneg x). pose proof (Z.abs_nonneg y).
  apply nonnegative_quot_product_iff; lia.
Qed.

Lemma abs_product_guard_iff : forall M x y,
  0 <= M ->
  ((Z.abs y = 0 \/ Z.abs x <= Z.quot M (Z.abs y)) <->
    Z.abs (x*y) <= M).
Proof.
  intros M x y HM. destruct (Z.eq_dec (Z.abs y) 0) as [Hz|Hz].
  - rewrite Z.abs_mul, Hz, Z.mul_0_r. intuition lia.
  - rewrite <- (abs_product_quot_iff M x y HM Hz). tauto.
Qed.

Lemma positive_quot_is_floor : forall M b,
  0 <= M -> 0 < b -> Z.quot M b = M / b.
Proof. intros. apply Z.quot_div_nonneg; assumption. Qed.

Lemma checked_mul_success_product_range : forall x y,
  checked_mul_flag x y = 1 ->
  -2147483647 <= x*y <= 2147483647.
Proof.
  intros x y H. apply checked_mul_flag_success_iff in H.
  destruct H as [_ [_ H]]. apply Z.abs_le in H. exact H.
Qed.

Lemma checked_mul_min_rejected : forall x y,
  x = -2147483648 \/ y = -2147483648 -> checked_mul_flag x y = 0.
Proof. intros. apply checked_mul_flag_failure_iff. tauto. Qed.

Lemma checked_mul_zero_success : forall x y,
  x <> -2147483648 -> y <> -2147483648 ->
  (x = 0 \/ y = 0) -> checked_mul_flag x y = 1 /\ x*y = 0.
Proof.
  intros x y Hx Hy Hz. assert (x*y=0) by (destruct Hz; subst; ring).
  split; [apply checked_mul_flag_success_iff; rewrite H; simpl; intuition lia | exact H].
Qed.

Lemma checked_mul_one_success : forall x,
  -2147483647 <= x <= 2147483647 -> checked_mul_flag x 1 = 1.
Proof.
  intros x H. apply checked_mul_flag_success_iff.
  rewrite Z.mul_1_r. split; [lia|]. split; [lia|]. apply Z.abs_le. exact H.
Qed.

Lemma checked_mul_min_product_rejected : forall x y,
  x*y = -2147483648 -> checked_mul_flag x y = 0.
Proof. intros. apply checked_mul_flag_failure_iff. right; right. rewrite H. simpl. lia. Qed.
