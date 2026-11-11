Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.

Local Open Scope Z_scope.

(**
 * Montgomery representation over the integers.
 *
 * [p] is the modulus, [R] is the Montgomery radix, [x] and [y] are field
 * values, [T] is a value to be reduced, and [result] is a canonical residue.
 *)
Module Montgomery.

(** [mont p R x] is the canonical Montgomery representation of [x]. *)
Definition mont (p R x : Z) : Z :=
  (x * R) mod p.

(** * Elementary modular arithmetic *)

Lemma multiple_mod_zero :
  forall p k,
    p <> 0 ->
    (k * p) mod p = 0.
Proof.
  intros p k Hp.
  apply Z.mod_mul.
  exact Hp.
Qed.

Lemma equation_implies_congruence :
  forall p left right k,
    p <> 0 ->
    left = right + k * p ->
    (left - right) mod p = 0.
Proof.
  intros p left right k Hp Heq.
  replace (left - right) with (k * p) by lia.
  apply multiple_mod_zero.
  exact Hp.
Qed.

Lemma canonical_congruent_equal :
  forall p x y,
    0 < p ->
    0 <= x < p ->
    0 <= y < p ->
    (x - y) mod p = 0 ->
    x = y.
Proof.
  intros p x y Hp Hx Hy Hmod.
  apply Z.mod_divide in Hmod; [| lia].
  destruct Hmod as [k Hk].
  destruct (Z.eq_dec k 0) as [Hk_zero | Hk_nonzero].
  - subst k.
    lia.
  - destruct (Z_lt_ge_dec k 0) as [Hk_negative | Hk_positive].
    + assert (Hproduct : p * k <= -p).
      {
        replace (-p) with (p * (-1)) by ring.
        apply Z.mul_le_mono_nonneg_l; lia.
      }
      lia.
    + assert (Hproduct : p <= p * k).
      {
        replace p with (p * 1) at 1 by ring.
        apply Z.mul_le_mono_nonneg_l; lia.
      }
      lia.
Qed.

Lemma congruent_values_have_equal_remainders :
  forall p x y,
    p <> 0 ->
    (x - y) mod p = 0 ->
    x mod p = y mod p.
Proof.
  intros p x y Hp Hmod.
  apply Z.mod_divide in Hmod; [| exact Hp].
  destruct Hmod as [k Hk].
  assert (Hx : x = y + p * k) by lia.
  rewrite Hx.
  replace (p * k) with (k * p) by ring.
  rewrite Z.add_mod by exact Hp.
  rewrite Z.mod_mul by exact Hp.
  rewrite Z.add_0_r.
  apply Z.mod_mod.
  exact Hp.
Qed.

Lemma subtract_multiple_preserves_modulo :
  forall p x k,
    p <> 0 ->
    (x - k * p) mod p = x mod p.
Proof.
  intros p x k Hp.
  rewrite Zminus_mod by exact Hp.
  rewrite Z.mod_mul by exact Hp.
  rewrite Z.sub_0_r.
  apply Z.mod_mod.
  exact Hp.
Qed.

(** * Montgomery representation *)

Lemma mont_range :
  forall p R x,
    0 < p ->
    0 <= mont p R x < p.
Proof.
  intros p R x Hp.
  unfold mont.
  apply Z.mod_pos_bound.
  exact Hp.
Qed.

Lemma mont_equation :
  forall p R x,
    p <> 0 ->
    exists q,
      x * R = mont p R x + q * p.
Proof.
  intros p R x Hp.
  exists ((x * R) / p).
  unfold mont.
  pose proof (Z.div_mod (x * R) p Hp) as Hdiv.
  nia.
Qed.

Lemma mont_congruence :
  forall p R x,
    p <> 0 ->
    (mont p R x - x * R) mod p = 0.
Proof.
  intros p R x Hp.
  destruct (mont_equation p R x Hp) as [q Hq].
  apply equation_implies_congruence with (k := -q); try assumption.
  nia.
Qed.

Lemma mont_unique :
  forall p R x result,
    0 < p ->
    0 <= result < p ->
    (result - x * R) mod p = 0 ->
    result = mont p R x.
Proof.
  intros p R x result Hp Hresult Hcongruence.
  pose proof (mont_range p R x Hp) as Hmont.
  pose proof (mont_congruence p R x ltac:(lia)) as Hmont_congruence.
  apply canonical_congruent_equal with (p := p); try assumption.
  apply Z.mod_divide; [lia |].
  apply Z.mod_divide in Hcongruence; [| lia].
  apply Z.mod_divide in Hmont_congruence; [| lia].
  destruct Hcongruence as [k Hk].
  destruct Hmont_congruence as [q Hq].
  exists (k - q).
  assert (Hresult_value : result = x * R + p * k) by lia.
  assert (Hmont_value : mont p R x = x * R + p * q) by lia.
  rewrite Hresult_value, Hmont_value.
  ring.
Qed.

Lemma mont_zero :
  forall p R,
    p <> 0 ->
    mont p R 0 = 0.
Proof.
  intros p R Hp.
  unfold mont.
  rewrite Z.mul_0_l.
  apply Z.mod_0_l.
  exact Hp.
Qed.

Lemma mont_one :
  forall p R,
    mont p R 1 = R mod p.
Proof.
  intros p R.
  unfold mont.
  replace (1 * R) with R by ring.
  reflexivity.
Qed.

Lemma mont_add :
  forall p R x y,
    p <> 0 ->
    mont p R (x + y) =
      (mont p R x + mont p R y) mod p.
Proof.
  intros p R x y Hp.
  unfold mont.
  replace ((x + y) * R) with (x * R + y * R) by ring.
  rewrite Z.add_mod by exact Hp.
  reflexivity.
Qed.

Lemma mont_sub :
  forall p R x y,
    p <> 0 ->
    mont p R (x - y) =
      (mont p R x - mont p R y) mod p.
Proof.
  intros p R x y Hp.
  unfold mont.
  replace ((x - y) * R) with (x * R - y * R) by ring.
  rewrite Zminus_mod by exact Hp.
  reflexivity.
Qed.

Lemma mont_mod :
  forall p R x,
    p <> 0 ->
    mont p R (x mod p) = mont p R x.
Proof.
  intros p R x Hp.
  unfold mont.
  apply Z.mul_mod_idemp_l.
  exact Hp.
Qed.

Lemma mont_neg :
  forall p R x,
    p <> 0 ->
    mont p R (-x) = (- mont p R x) mod p.
Proof.
  intros p R x Hp.
  replace (-x) with (0 - x) by ring.
  rewrite mont_sub by exact Hp.
  rewrite mont_zero by exact Hp.
  replace (0 - mont p R x) with (- mont p R x) by ring.
  reflexivity.
Qed.

Lemma mont_product_scaled :
  forall p R x y,
    p <> 0 ->
    (mont p R x * mont p R y) mod p =
      (mont p R (x * y) * R) mod p.
Proof.
  intros p R x y Hp.
  apply congruent_values_have_equal_remainders; try assumption.
  apply Z.mod_divide; [exact Hp |].
  destruct (mont_equation p R x Hp) as [qx Hx].
  destruct (mont_equation p R y Hp) as [qy Hy].
  destruct (mont_equation p R (x * y) Hp) as [qxy Hxy].
  exists (-x * R * qy - y * R * qx + qx * qy * p + qxy * R).
  assert (Hmx : mont p R x = x * R - qx * p) by lia.
  assert (Hmy : mont p R y = y * R - qy * p) by lia.
  assert (Hmxy : mont p R (x * y) = x * y * R - qxy * p) by lia.
  rewrite Hmx, Hmy, Hmxy.
  ring.
Qed.

(** * Montgomery reduction equations *)

Lemma reduction_congruence_from_equation :
  forall p R T result q,
    p <> 0 ->
    result * R = T + q * p ->
    (result * R - T) mod p = 0.
Proof.
  intros p R T result q Hp Heq.
  eapply equation_implies_congruence; eauto.
Qed.

Lemma reduction_numerator_multiple :
  forall p R p_prime T low high m m_high inverse_quotient,
    T = low + high * R ->
    low * p_prime = m + m_high * R ->
    p * p_prime + 1 = inverse_quotient * R ->
    T + m * p =
      (high + low * inverse_quotient - m_high * p) * R.
Proof.
  intros p R p_prime T low high m m_high inverse_quotient
    HT Hm Hinverse.
  assert (Hm_value : m = low * p_prime - m_high * R) by lia.
  rewrite HT, Hm_value.
  replace
    (low + high * R + (low * p_prime - m_high * R) * p)
    with (high * R + low * (p * p_prime + 1) - m_high * p * R)
    by ring.
  rewrite Hinverse.
  ring.
Qed.

Lemma reduction_quotient_bound :
  forall p R T q numerator quotient,
    0 < p ->
    0 < R ->
    0 <= T < p * R ->
    0 <= q < R ->
    numerator = T + q * p ->
    numerator = quotient * R ->
    0 <= quotient < 2 * p.
Proof.
  intros p R T q numerator quotient Hp HR HT Hq Hnum Hquot.
  nia.
Qed.

Lemma result_from_reduction :
  forall p R R_inv T result,
    0 < p ->
    0 <= result < p ->
    (R * R_inv - 1) mod p = 0 ->
    (result * R - T) mod p = 0 ->
    result = (T * R_inv) mod p.
Proof.
  intros p R R_inv T result Hp Hresult HRinv Hreduction.
  apply canonical_congruent_equal with (p := p).
  - exact Hp.
  - exact Hresult.
  - apply Z.mod_pos_bound; exact Hp.
  - apply Z.mod_divide; [lia |].
    apply Z.mod_divide in HRinv; [| lia].
    apply Z.mod_divide in Hreduction; [| lia].
    destruct HRinv as [a Ha].
    destruct Hreduction as [b Hb].
    exists (b * R_inv - result * a + (T * R_inv / p)).
    pose proof (Z.div_mod (T * R_inv) p ltac:(lia)) as Hdiv.
    nia.
Qed.

(** * Final conditional subtraction *)

Lemma subtraction_range :
  forall p value,
    0 < p ->
    p <= value < 2 * p ->
    0 <= value - p < p.
Proof.
  intros p value Hp Hvalue.
  lia.
Qed.

Lemma subtraction_preserves_congruence :
  forall p value,
    p <> 0 ->
    ((value - p) - value) mod p = 0.
Proof.
  intros p value Hp.
  replace ((value - p) - value) with ((-1) * p) by ring.
  apply multiple_mod_zero.
  exact Hp.
Qed.

(** * Montgomery multiplication and conversion *)

Lemma cancel_invertible_factor :
  forall p factor factor_inv left right,
    p <> 0 ->
    (factor * factor_inv - 1) mod p = 0 ->
    ((left - right) * factor) mod p = 0 ->
    (left - right) mod p = 0.
Proof.
  intros p factor factor_inv left right Hp Hinverse Hscaled.
  apply Z.mod_divide; [exact Hp |].
  apply Z.mod_divide in Hinverse; [| exact Hp].
  apply Z.mod_divide in Hscaled; [| exact Hp].
  destruct Hinverse as [a Ha].
  destruct Hscaled as [b Hb].
  exists (b * factor_inv - (left - right) * a).
  replace (left - right) with
    ((left - right) * factor * factor_inv -
     (left - right) * (factor * factor_inv - 1))
    at 1 by ring.
  rewrite Hb, Ha.
  ring.
Qed.

Lemma mont_injective_canonical :
  forall p R x y,
    0 < p ->
    rel_prime p R ->
    0 <= x < p ->
    0 <= y < p ->
    mont p R x = mont p R y ->
    x = y.
Proof.
  intros p R x y Hp Hcoprime Hx Hy Hequal.
  destruct (mont_equation p R x ltac:(lia)) as [qx Hqx].
  destruct (mont_equation p R y ltac:(lia)) as [qy Hqy].
  assert (Hscaled : (p | R * (x - y))).
  {
    exists (qx - qy).
    rewrite Z.mul_sub_distr_l.
    replace (R * x) with (x * R) by ring.
    replace (R * y) with (y * R) by ring.
    rewrite Hqx, Hqy, Hequal.
    ring.
  }
  pose proof (Gauss p R (x - y) Hscaled Hcoprime) as Hdifference.
  apply canonical_congruent_equal with (p := p); try assumption.
  apply Z.mod_divide; [lia | exact Hdifference].
Qed.

Lemma montgomery_multiplication :
  forall p R R_inv x y result,
    0 < p ->
    0 <= result < p ->
    (R * R_inv - 1) mod p = 0 ->
    (result * R - mont p R x * mont p R y) mod p = 0 ->
    result = mont p R (x * y).
Proof.
  intros p R R_inv x y result Hp Hresult HRinv Hreduction.
  pose proof (mont_range p R (x * y) Hp) as Hmont_range.
  destruct (mont_equation p R x ltac:(lia)) as [qx Hx].
  destruct (mont_equation p R y ltac:(lia)) as [qy Hy].
  destruct (mont_equation p R (x * y) ltac:(lia)) as [qxy Hxy].
  apply canonical_congruent_equal with (p := p); try assumption.
  eapply cancel_invertible_factor with
    (factor := R) (factor_inv := R_inv).
  - lia.
  - exact HRinv.
  - apply Z.mod_divide; [lia |].
    apply Z.mod_divide in Hreduction; [| lia].
    destruct Hreduction as [q Hq].
    exists
      (q - x * R * qy - y * R * qx + qx * qy * p + qxy * R).
    assert (Hmx : mont p R x = x * R - qx * p) by nia.
    assert (Hmy : mont p R y = y * R - qy * p) by nia.
    assert (Hmxy : mont p R (x * y) = x * y * R - qxy * p) by nia.
    assert (Hresult_eq :
      result * R = mont p R x * mont p R y + q * p) by nia.
    replace ((result - mont p R (x * y)) * R) with
      (result * R - mont p R (x * y) * R) at 1 by ring.
    rewrite Hresult_eq, Hmx, Hmy, Hmxy.
    ring.
Qed.

Lemma regular_to_montgomery :
  forall p R R_inv x result,
    0 < p ->
    0 <= result < p ->
    (R * R_inv - 1) mod p = 0 ->
    (result * R - x * ((R * R) mod p)) mod p = 0 ->
    result = mont p R x.
Proof.
  intros p R R_inv x result Hp Hresult HRinv Hreduction.
  pose proof (mont_range p R x Hp) as Hmont_range.
  destruct (mont_equation p R R ltac:(lia)) as [qR2 HR2].
  destruct (mont_equation p R x ltac:(lia)) as [qx Hx].
  apply canonical_congruent_equal with (p := p); try assumption.
  eapply cancel_invertible_factor with
    (factor := R) (factor_inv := R_inv).
  - lia.
  - exact HRinv.
  - apply Z.mod_divide; [lia |].
    apply Z.mod_divide in Hreduction; [| lia].
    destruct Hreduction as [q Hq].
    exists (q - x * qR2 + qx * R).
    unfold mont in HR2.
    assert (HR2_value : (R * R) mod p = R * R - qR2 * p) by lia.
    assert (Hmont_value : mont p R x = x * R - qx * p) by lia.
    assert (Hresult_eq :
      result * R = x * ((R * R) mod p) + q * p) by lia.
    replace ((result - mont p R x) * R) with
      (result * R - mont p R x * R) at 1 by ring.
    rewrite Hresult_eq, HR2_value, Hmont_value.
    ring.
Qed.

Lemma montgomery_to_regular :
  forall p R R_inv x result,
    0 < p ->
    0 <= x < p ->
    0 <= result < p ->
    (R * R_inv - 1) mod p = 0 ->
    (result * R - mont p R x) mod p = 0 ->
    result = x.
Proof.
  intros p R R_inv x result Hp Hx Hresult HRinv Hreduction.
  apply canonical_congruent_equal with (p := p); try assumption.
  eapply cancel_invertible_factor with
    (factor := R) (factor_inv := R_inv).
  - lia.
  - exact HRinv.
  - apply Z.mod_divide; [lia |].
    apply Z.mod_divide in Hreduction; [| lia].
    destruct Hreduction as [q Hq].
    destruct (mont_equation p R x ltac:(lia)) as [qx Hmont].
    exists (q - qx).
    assert (Hresult_eq : result * R = mont p R x + q * p) by nia.
    nia.
Qed.

(** * Inversion *)

Lemma montgomery_inverse :
  forall p R x x_inv result,
    0 < p ->
    0 <= result < p ->
    (x * x_inv - 1) mod p = 0 ->
    (x * result - R) mod p = 0 ->
    result = mont p R x_inv.
Proof.
  intros p R x x_inv result Hp Hresult Hinverse Hscaled_inverse.
  apply mont_unique; try assumption.
  apply Z.mod_divide; [lia |].
  apply Z.mod_divide in Hinverse; [| lia].
  apply Z.mod_divide in Hscaled_inverse; [| lia].
  destruct Hinverse as [a Ha].
  destruct Hscaled_inverse as [b Hb].
  exists (b * x_inv - result * a).
  nia.
Qed.

End Montgomery.
