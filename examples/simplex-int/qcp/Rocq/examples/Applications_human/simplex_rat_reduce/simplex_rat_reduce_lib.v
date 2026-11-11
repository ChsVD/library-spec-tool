From Coq Require Import ZArith Lia.
From SimpleC.EE.Applications_human.simplex_positive_gcd
  Require Export simplex_positive_gcd_lib.
Local Open Scope Z_scope.

(* Deterministic mathematical result.  Input bounds and ownership belong
   to the function contract, not this relation.  quot is truncation toward
   zero, matching the QCP integer-division interface also for negative N. *)
Definition simplex_rat_reduce_result (N D P Q : Z) : Prop :=
  P = Z.quot N (Z.gcd (Z.abs N) D) /\
  Q = Z.quot D (Z.gcd (Z.abs N) D).

(* Reference read: FME implement_lemma.v:293-353 and fme.c:207-209.
   Both FME quotients have strictly positive dividends.  We adapt its
   exact quotient/division argument to D>0 and any signed N, including 0.
   Gcd positivity/divisibility/zero boundaries are imported, not reproved. *)
Lemma simplex_rat_reduce_factor (N D : Z) :
  0 < D ->
  0 < Z.gcd (Z.abs N) D /\
  (Z.gcd (Z.abs N) D | N) /\ (Z.gcd (Z.abs N) D | D).
Proof.
  intros HD. split.
  - apply simplex_gcd_positive; [apply Z.abs_nonneg | lia | right; lia].
  - destruct (simplex_gcd_common_divisor (Z.abs N) D) as [HN HDiv].
    split; [now apply Z.divide_abs_r | exact HDiv].
Qed.

Lemma simplex_rat_reduce_exact (N D : Z) :
  0 < D ->
  N = Z.gcd (Z.abs N) D * Z.quot N (Z.gcd (Z.abs N) D) /\
  D = Z.gcd (Z.abs N) D * Z.quot D (Z.gcd (Z.abs N) D).
Proof.
  intros HD.
  destruct (simplex_rat_reduce_factor N D HD) as [Hg [HN HDiv]].
  split; apply Z.quot_exact; try lia;
    apply Z.rem_divide; assumption || lia.
Qed.

(* FME right quotient positivity with its x>0 premise removed. *)
Lemma simplex_rat_reduce_den_bounds (N D : Z) :
  0 < D -> 1 <= Z.quot D (Z.gcd (Z.abs N) D) <= D.
Proof.
  intros HD.
  destruct (simplex_rat_reduce_factor N D HD) as [Hg [HN HDiv]].
  assert (Hle : Z.gcd (Z.abs N) D <= D).
  { apply Z.divide_pos_le; assumption. }
  assert (Hp : 0 < Z.quot D (Z.gcd (Z.abs N) D)).
  { rewrite Z.quot_div_exact by (assumption || lia).
    apply Z.div_str_pos; lia. }
  pose proof (simplex_rat_reduce_exact N D HD) as [_ HE].
  split; nia.
Qed.

(* Explicit signed adaptation: positive, zero and negative numerator. *)
Lemma simplex_rat_reduce_num_sign (N D : Z) :
  0 < D ->
  (0 < N -> 0 < Z.quot N (Z.gcd (Z.abs N) D)) /\
  (N = 0 -> Z.quot N (Z.gcd (Z.abs N) D) = 0) /\
  (N < 0 -> Z.quot N (Z.gcd (Z.abs N) D) < 0).
Proof.
  intros HD.
  destruct (simplex_rat_reduce_factor N D HD) as [Hg [HN HDiv]].
  pose proof (simplex_rat_reduce_exact N D HD) as [HE _].
  split; [intros; nia |]. split; intros; nia.
Qed.

Lemma simplex_rat_reduce_num_bound (N D : Z) :
  0 < D -> Z.abs (Z.quot N (Z.gcd (Z.abs N) D)) <= Z.abs N.
Proof.
  intros HD.
  destruct (simplex_rat_reduce_factor N D HD) as [Hg _].
  pose proof (simplex_rat_reduce_exact N D HD) as [HE _].
  assert (HA : Z.abs N = Z.gcd (Z.abs N) D *
                Z.abs (Z.quot N (Z.gcd (Z.abs N) D))).
  { rewrite HE at 1. rewrite Z.abs_mul, Z.abs_eq by lia. reflexivity. }
  pose proof (Z.abs_nonneg (Z.quot N (Z.gcd (Z.abs N) D))). nia.
Qed.

Lemma simplex_rat_reduce_coprime (N D : Z) :
  0 < D ->
  Z.gcd (Z.abs (Z.quot N (Z.gcd (Z.abs N) D)))
        (Z.quot D (Z.gcd (Z.abs N) D)) = 1.
Proof.
  intros HD.
  destruct (simplex_rat_reduce_factor N D HD) as [Hg _].
  rewrite Z.gcd_abs_l.
  apply Z.gcd_quot_gcd; [lia | apply Z.gcd_abs_l].
Qed.

Lemma simplex_rat_reduce_value (N D : Z) :
  0 < D ->
  N * Z.quot D (Z.gcd (Z.abs N) D) =
  Z.quot N (Z.gcd (Z.abs N) D) * D.
Proof.
  intros HD. pose proof (simplex_rat_reduce_exact N D HD) as [HN HDiv].
  nia.
Qed.

Lemma simplex_rat_reduce_zero (D : Z) :
  0 < D -> simplex_rat_reduce_result 0 D 0 1.
Proof.
  intros HD. unfold simplex_rat_reduce_result.
  rewrite Z.abs_0, simplex_gcd_zero_left by lia.
  rewrite Z.quot_0_l, Z.quot_same by lia. auto.
Qed.

Lemma simplex_rat_reduce_already_reduced (N D : Z) :
  Z.gcd (Z.abs N) D = 1 -> simplex_rat_reduce_result N D N D.
Proof.
  intros H. unfold simplex_rat_reduce_result. rewrite H, !Z.quot_1_r. auto.
Qed.

Lemma simplex_rat_reduce_unique (N D P Q P' Q' : Z) :
  simplex_rat_reduce_result N D P Q ->
  simplex_rat_reduce_result N D P' Q' -> P = P' /\ Q = Q'.
Proof. unfold simplex_rat_reduce_result. intros [? ?] [? ?]; subst; auto. Qed.

(* This theorem exposes all properties required by callers, with a generic
   symmetric bound M rather than a machine-specific input predicate. *)
Lemma simplex_rat_reduce_properties (N D P Q M : Z) :
  -M <= N <= M -> 1 <= D <= M ->
  simplex_rat_reduce_result N D P Q ->
  -M <= P <= M /\ 1 <= Q <= M /\
  Z.gcd (Z.abs P) Q = 1 /\ N * Q = P * D /\
  (N = 0 -> P = 0 /\ Q = 1) /\
  (Z.gcd (Z.abs N) D = 1 -> P = N /\ Q = D).
Proof.
  intros HN HD [HP HQ]. subst P Q.
  pose proof (simplex_rat_reduce_den_bounds N D ltac:(lia)).
  pose proof (simplex_rat_reduce_num_bound N D ltac:(lia)).
  assert (HB : Z.abs N <= M) by (apply Z.abs_le; lia).
  assert (HBP : -M <= Z.quot N (Z.gcd (Z.abs N) D) <= M).
  { apply Z.abs_le. lia. }
  split; [exact HBP |]. split; [lia |].
  split; [apply simplex_rat_reduce_coprime; lia |].
  split; [apply simplex_rat_reduce_value; lia |]. split.
  - intros Hz. subst N. split; [reflexivity |]. simpl Z.abs.
    rewrite simplex_gcd_zero_left by lia. apply Z.quot_same; lia.
  - intros Hg. rewrite Hg, !Z.quot_1_r. auto.
Qed.
