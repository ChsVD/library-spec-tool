Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.setoid_ring.Ring.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import IntLib.
From SimpleC.EE.Applications_human.sm2.lib
  Require Import basicOp_lib montgomery.

Local Open Scope Z_scope.
Import ListNotations.

(**
 * Binary almost-inverse arithmetic for a 256-bit Montgomery radix.
 *
 * The development is parameterized by the odd prime modulus.  It describes
 * the two algorithm phases and proves the arithmetic transitions used by the
 * SM2 P and N instances.  Its fixed-width value relations are shared with the
 * lower-level SM2 representation and basic-operation libraries.
 *)

Section BinaryAlmostInverse.

(** * Parameters *)

Variable modulus : Z.
Hypothesis modulus_bounds : 0 < modulus < U256_MOD.
Hypothesis modulus_more_than_three_quarters :
  3 * 2 ^ 254 < modulus.
Hypothesis modulus_prime : prime modulus.
Hypothesis radix_coprime :
  Z.gcd modulus U256_MOD = 1.

Lemma montgomery_parameters_valid :
  0 < modulus < U256_MOD /\
  Z.gcd modulus U256_MOD = 1.
Proof.
  split.
  - exact modulus_bounds.
  - exact radix_coprime.
Qed.

Lemma modulus_nonzero_gcd_one :
  forall a,
    0 <= a < modulus ->
    a <> 0 ->
    Z.gcd a modulus = 1.
Proof.
  intros a Ha Ha0.
  apply Zgcd_1_rel_prime.
  apply rel_prime_le_prime.
  - exact modulus_prime.
  - lia.
Qed.

(** * Phase-state relations *)

Definition mont_inv_phase1_exit_carry
  (a r k carry : Z) : Prop :=
  0 < a < modulus /\
  0 <= r < U256_MOD /\
  0 <= carry <= 1 /\
  Z.gcd a modulus = 1 /\
  256 <= k <= 512 /\
  (a * (r + carry * U256_MOD) + 2 ^ k) mod modulus = 0 /\
  (carry = 0 -> 0 < r < 2 * modulus) /\
  (carry = 1 -> r < modulus).

(** Progress and termination bounds maintained while [v] is nonzero. *)
Definition mont_inv_phase1_progress
  (u v r s k : Z) : Prop :=
  0 < u /\
  0 <= r <= 2 ^ k /\
  0 <= s <= 2 ^ k /\
  (v <> 0 -> 0 < u * v < 2 ^ (512 - k)) /\
  (u = v -> 255 <= k).

(** Weighted-coefficient identity and bounds needed by the next transition. *)
Definition mont_inv_phase1_overflow_reach
  (u v r s carry : Z) : Prop :=
  r * v + s * u = modulus /\
  (v <> 0 ->
     carry = 0 /\
     r + s < U256_MOD /\
     ((Z.land u 1 = 0 \/
       (Z.land u 1 = 1 /\ Z.land v 1 = 1 /\ u > v)) ->
        2 * s < U256_MOD) /\
     ((Z.land u 1 = 1 /\
       (Z.land v 1 = 0 \/ (Z.land v 1 = 1 /\ u < v))) ->
        2 * r < U256_MOD)).

(** Complete invariant of the first binary almost-inverse phase. *)
Definition mont_inv_phase1_state
  (a u v r s k carry : Z) : Prop :=
  0 < a < modulus /\
  0 <= u < U256_MOD /\
  0 <= v < U256_MOD /\
  0 <= r < U256_MOD /\
  0 <= s < U256_MOD /\
  0 <= k <= 512 /\
  0 <= carry <= k /\
  Z.gcd a modulus = 1 /\
  Z.gcd u v = 1 /\
  mont_inv_phase1_progress u v r s k /\
  mont_inv_phase1_overflow_reach u v r s carry /\
  (a * (r + carry * U256_MOD) + u * 2 ^ k) mod modulus = 0 /\
  (a * s - v * 2 ^ k) mod modulus = 0 /\
  (v = 0 -> u = 1 /\ mont_inv_phase1_exit_carry a r k carry).

(** Residue immediately after phase I, before conditional normalization. *)
Definition mont_inv_post_loop_residue (a r k : Z) : Prop :=
  0 < a < modulus /\
  0 < r < 2 * modulus /\
  Z.gcd a modulus = 1 /\
  256 <= k <= 512 /\
  (a * r + 2 ^ k) mod modulus = 0.

(** Phase-I residue after reducing [r] to the canonical modulus range. *)
Definition mont_inv_post_loop_norm (a r k : Z) : Prop :=
  0 < a < modulus /\
  0 < r < modulus /\
  Z.gcd a modulus = 1 /\
  256 <= k <= 512 /\
  (a * r + 2 ^ k) mod modulus = 0.

(** Positive scaled inverse produced by the normalized phase-I result. *)
Definition mont_inv_phase1_result (a r k : Z) : Prop :=
  0 < a < modulus /\
  0 <= r < modulus /\
  Z.gcd a modulus = 1 /\
  256 <= k <= 512 /\
  (a * r) mod modulus = (2 ^ k) mod modulus.

(** Quotient and remainder selecting the phase-II one-hot multiplier. *)
Definition mont_inv_phase2_index (k0 i k : Z) : Prop :=
  256 <= k0 <= 512 /\
  k0 <> 256 /\
  i = (512 - k0) / 64 /\
  k = (512 - k0) mod 64.

(** * Post-loop normalization *)

Lemma pow2_mod_nonzero :
  forall k,
    0 <= k ->
    2 ^ k mod modulus <> 0.
Proof.
  intros k Hk Hmod.
  assert (Hdiv : (modulus | 2 ^ k)).
  {
    apply Z.mod_divide.
    - pose proof modulus_bounds. lia.
    - exact Hmod.
  }
  pose proof
    (Zpow_facts.prime_power_prime
       modulus 2 k Hk modulus_prime prime_2 Hdiv) as Heq.
  pose proof modulus_more_than_three_quarters as Hmodulus.
  assert (Hpow : 0 < 2 ^ 254) by (apply Z.pow_pos_nonneg; lia).
  lia.
Qed.

Lemma residue_sub_modulus_norm :
  forall a r s k,
    mont_inv_post_loop_residue a r k ->
    modulus <= r ->
    s = r - modulus ->
    mont_inv_post_loop_norm a s k.
Proof.
  intros a r s k Hres Hge Hs.
  unfold mont_inv_post_loop_residue in Hres.
  destruct Hres as (Ha & Hr & Hgcd & Hkrange & Hmod).
  assert (Hrneq : r <> modulus).
  {
    intros ->.
    replace (a * modulus + 2 ^ k)
      with (2 ^ k + a * modulus) in Hmod by ring.
    rewrite Z_mod_plus_full in Hmod.
    apply (pow2_mod_nonzero k); [lia | exact Hmod].
  }
  subst s.
  unfold mont_inv_post_loop_norm.
  repeat split; try assumption; try lia.
  replace (a * (r - modulus) + 2 ^ k)
    with ((a * r + 2 ^ k) + (-a) * modulus) by ring.
  rewrite Z_mod_plus_full.
  exact Hmod.
Qed.

Lemma residue_below_modulus_norm :
  forall a r k,
    mont_inv_post_loop_residue a r k ->
    r < modulus ->
    mont_inv_post_loop_norm a r k.
Proof.
  intros a r k Hres Hlt.
  unfold mont_inv_post_loop_residue in Hres.
  destruct Hres as (Ha & Hr & Hgcd & Hkrange & Hmod).
  unfold mont_inv_post_loop_norm.
  repeat split; try assumption; lia.
Qed.

Lemma norm_complement_result :
  forall a r s k,
    mont_inv_post_loop_norm a r k ->
    s = modulus - r ->
    mont_inv_phase1_result a s k.
Proof.
  intros a r s k Hnorm Hs.
  unfold mont_inv_post_loop_norm in Hnorm.
  destruct Hnorm as (Ha & Hr & Hgcd & Hkrange & Hmod).
  subst s.
  unfold mont_inv_phase1_result.
  repeat split; try assumption; try lia.
  replace (a * (modulus - r))
    with ((-a * r) + a * modulus) by ring.
  rewrite Z_mod_plus_full.
  assert (Hneg : (-(a * r + 2 ^ k)) mod modulus = 0).
  {
    apply Z_mod_zero_opp_full.
    exact Hmod.
  }
  replace (-a * r) with (2 ^ k + (-(a * r + 2 ^ k))) by ring.
  rewrite Z.add_mod, Hneg, Z.add_0_r.
  rewrite Z.mod_mod by (pose proof modulus_bounds; lia).
  all: pose proof modulus_bounds; lia.
Qed.

Lemma scaled_inverse_is_montgomery :
  forall a z quotient,
    0 <= a < modulus ->
    a <> 0 ->
    0 <= z < modulus ->
    a * z = U256_MOD + quotient * modulus ->
    exists a_inv,
      0 <= a_inv < modulus /\
      (a * a_inv) mod modulus = 1 /\
      z = Montgomery.mont modulus U256_MOD a_inv.
Proof.
  intros a z quotient Ha Ha0 Hz Hequation.
  pose proof (modulus_nonzero_gcd_one a Ha Ha0) as Hgcd.
  apply Zgcd_1_rel_prime in Hgcd.
  destruct (rel_prime_bezout a modulus Hgcd) as [u v Hbezout].
  set (a_inv := u mod modulus).
  pose proof modulus_bounds as Hn.
  assert (Hainv : 0 <= a_inv < modulus).
  {
    unfold a_inv.
    apply Z.mod_pos_bound.
    exact (proj1 Hn).
  }
  pose proof (Z.div_mod u modulus ltac:(lia)) as Hdiv.
  assert (Hainv_equation :
    a * a_inv =
      1 + (-(a * (u / modulus) + v)) * modulus).
  {
    unfold a_inv.
    clear - Hbezout Hdiv.
    nia.
  }
  assert (Hinverse : (a * a_inv) mod modulus = 1).
  {
    assert (Hmodulus_gt_one : 1 < modulus).
    {
      pose proof modulus_more_than_three_quarters as Hlarge.
      assert (Hpow : 0 < 2 ^ 254).
      {
        apply Z.pow_pos_nonneg; lia.
      }
      lia.
    }
    rewrite Hainv_equation.
    rewrite Z.add_mod by lia.
    rewrite Z.mod_mul by lia.
    rewrite Z.add_0_r.
    rewrite Z.mod_mod by lia.
    apply Z.mod_small.
    lia.
  }
  assert (Hscaled : (a * z - U256_MOD) mod modulus = 0).
  {
    replace (a * z - U256_MOD) with (quotient * modulus) by lia.
    apply Z.mod_mul.
    lia.
  }
  assert (Hzmont : z = Montgomery.mont modulus U256_MOD a_inv).
  {
    apply Montgomery.montgomery_inverse with (x := a).
    - exact (proj1 Hn).
    - exact Hz.
    - rewrite Hainv_equation.
      replace
        (1 + (-(a * (u / modulus) + v)) * modulus - 1)
        with ((-(a * (u / modulus) + v)) * modulus) by ring.
      apply Z.mod_mul.
      lia.
    - exact Hscaled.
  }
  exists a_inv.
  split.
  - exact Hainv.
  - split; assumption.
Qed.

(** * Phase II reconstruction *)

Lemma mont_inv_phase2_index_bounds :
  forall k0,
    256 <= k0 <= 512 ->
    k0 <> 256 ->
    mont_inv_phase2_index
      k0 ((512 - k0) / 64) ((512 - k0) mod 64) /\
    0 <= (512 - k0) / 64 < 4 /\
    0 <= (512 - k0) mod 64 < 64.
Proof.
  intros k0 Hbounds Hne.
  assert (Hmod : 0 <= (512 - k0) mod 64 < 64).
  { apply Z.mod_pos_bound. lia. }
  assert (Hdivlo : 0 <= (512 - k0) / 64).
  { apply Z.div_pos; lia. }
  assert (Hdivhi : (512 - k0) / 64 < 4).
  { apply Z.div_lt_upper_bound; lia. }
  split.
  - unfold mont_inv_phase2_index.
    split; [exact Hbounds |].
    split; [exact Hne |].
    split; reflexivity.
  - split; [split; assumption | exact Hmod].
Qed.

Lemma mont_inv_phase2_one_hot_value :
  forall k0 i k,
    mont_inv_phase2_index k0 i k ->
    0 <= i < 4 ->
    0 <= k < 64 ->
    0 <= 2 ^ (512 - k0) < modulus /\
    u64_list_value
      (replace_Znth i
        (unsigned_last_nbits (Z.shiftl 1 k) 64)
        (0 :: 0 :: 0 :: 0 :: nil)) =
      2 ^ (512 - k0).
Proof.
  intros k0 i k Hindex Hi Hk.
  unfold mont_inv_phase2_index in Hindex.
  destruct Hindex as [Hk0range [Hk0ne [Hi_eq Hk_eq]]].
  assert (Hexp : 512 - k0 = 64 * i + k).
  {
    pose proof (Z.div_mod (512 - k0) 64 ltac:(lia)) as Hdivmod.
    lia.
  }
  assert (Hshift :
    unsigned_last_nbits (Z.shiftl 1 k) 64 = 2 ^ k).
  {
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mul_1_l.
    apply unsigned_last_nbits_eq.
    unfold U64_MOD.
    split.
    - apply Z.pow_nonneg. lia.
    - apply Z.pow_lt_mono_r; lia.
  }
  assert (Hfactor : 2 ^ (512 - k0) = 2 ^ k * 2 ^ (64 * i)).
  {
    rewrite Hexp.
    rewrite Z.pow_add_r by lia.
    ring.
  }
  assert (Hpow_nonneg : 0 <= 2 ^ (512 - k0)).
  { apply Z.pow_nonneg. lia. }
  assert (Hconst : 2 ^ 255 < modulus).
  {
    pose proof modulus_more_than_three_quarters as Hmodulus.
    assert (Hpow : 0 < 2 ^ 254) by (apply Z.pow_pos_nonneg; lia).
    replace (2 ^ 255) with (2 * 2 ^ 254).
    - lia.
    - replace 255 with (Z.succ 254) by lia.
      rewrite Z.pow_succ_r by lia.
      ring.
  }
  assert (Hpow_le : 2 ^ (512 - k0) <= 2 ^ 255).
  { apply Z.pow_le_mono_r; lia. }
  split; [lia |].
  rewrite Hshift.
  unfold u64_list_value.
  rewrite limb_list_value_replace_Znth by (cbn; lia).
  assert (Hzero :
    limb_list_value U64_MOD (0 :: 0 :: 0 :: 0 :: nil) = 0).
  {
    change (u64_list_value (0 :: 0 :: 0 :: 0 :: nil) = 0).
    rewrite u64_list_value_four.
    cbv [u256_of_limbs].
    ring.
  }
  rewrite Hzero.
  assert (Hznth : Znth i (0 :: 0 :: 0 :: 0 :: nil) 0 = 0).
  {
    assert (Hi_cases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct Hi_cases as [-> | [-> | [-> | ->]]]; reflexivity.
  }
  rewrite Hznth.
  unfold limb_radix, U64_MOD.
  rewrite <- Z.pow_mul_r by lia.
  rewrite Hfactor.
  ring.
Qed.

Lemma mont_inv_phase2_product_equation :
  forall a r5 k0 t out kmul,
    0 <= out < modulus ->
    mont_inv_phase1_result a r5 k0 ->
    t = 2 ^ (512 - k0) ->
    out * U256_MOD = r5 * t + kmul * modulus ->
    exists kout,
      a * out = U256_MOD + kout * modulus.
Proof.
  intros a r5 k0 t out kmul Hout Hphase Ht Hproduct.
  unfold mont_inv_phase1_result in Hphase.
  destruct Hphase as [Ha [Hr5 [Hgcd [Hk0 Hphase_mod]]]].
  destruct montgomery_parameters_valid as [_ Hradix_gcd].
  assert (HN0 : modulus <> 0) by (pose proof modulus_bounds; lia).
  assert (Hphase_div : (modulus | a * r5 - 2 ^ k0)).
  {
    apply Z.mod_divide; [exact HN0 |].
    rewrite Zminus_mod, Hphase_mod, Z.sub_diag, Z.mod_0_l by exact HN0.
    reflexivity.
  }
  destruct Hphase_div as [q Hq].
  assert (Hpow : 2 ^ k0 * t = U256_MOD * U256_MOD).
  {
    rewrite Ht.
    unfold U256_MOD.
    rewrite <- Z.pow_add_r by lia.
    rewrite <- Z.pow_add_r by lia.
    f_equal.
    lia.
  }
  assert (Hscaled :
    (modulus | (a * out - U256_MOD) * U256_MOD)).
  {
    exists (t * q + a * kmul).
    replace ((a * out - U256_MOD) * U256_MOD)
      with (a * (out * U256_MOD) - U256_MOD * U256_MOD) by ring.
    rewrite Hproduct, <- Hpow.
    replace
      (a * (r5 * t + kmul * modulus) - 2 ^ k0 * t)
      with (t * (a * r5 - 2 ^ k0) + a * kmul * modulus) by ring.
    rewrite Hq.
    ring.
  }
  assert (Hcoprime : rel_prime modulus U256_MOD).
  {
    apply (proj1 (Zgcd_1_rel_prime _ _)).
    exact Hradix_gcd.
  }
  assert (Hresult_div : (modulus | a * out - U256_MOD)).
  {
    apply (Gauss modulus U256_MOD (a * out - U256_MOD)).
    - rewrite Z.mul_comm. exact Hscaled.
    - exact Hcoprime.
  }
  destruct Hresult_div as [kout Hkout].
  exists kout.
  lia.
Qed.

Lemma mont_inv_phase1_k256_equation :
  forall a r,
    mont_inv_phase1_result a r 256 ->
    exists kout,
      a * r = U256_MOD + kout * modulus.
Proof.
  intros a r Hphase.
  unfold mont_inv_phase1_result in Hphase.
  destruct Hphase as [Ha [Hr [Hgcd [Hk Hmod]]]].
  change ((a * r) mod modulus = U256_MOD mod modulus) in Hmod.
  assert (HN0 : modulus <> 0) by (pose proof modulus_bounds; lia).
  assert (Hdiv : (modulus | a * r - U256_MOD)).
  {
    apply Z.mod_divide; [exact HN0 |].
    rewrite Zminus_mod, Hmod, Z.sub_diag, Z.mod_0_l by exact HN0.
    reflexivity.
  }
  destruct Hdiv as [kout Hkout].
  exists kout.
  lia.
Qed.

(** * Phase I arithmetic *)

(** ** Low bits and halving *)

Lemma land_one_eq_mod_two :
  forall x, Z.land x 1 = x mod 2.
Proof.
  intros x.
  change (Z.land x 1 = x mod 2 ^ 1).
  apply Z.bits_inj'.
  intros n Hn.
  rewrite Z.land_spec, Z.testbit_mod_pow2 by lia.
  destruct n as [|p|p]; try lia.
  - cbn. apply Bool.andb_true_r.
  - destruct p; cbn; apply Bool.andb_false_r.
Qed.

Lemma gcd_halve_left :
  forall u v,
    Z.land u 1 = 0 ->
    Z.gcd u v = 1 ->
    Z.gcd (u / 2) v = 1.
Proof.
  intros u v Heven Hgcd.
  rewrite land_one_eq_mod_two in Heven.
  pose proof (Z.div_mod u 2 ltac:(lia)) as Hu.
  assert (Hd_u : (Z.gcd (u / 2) v | u)).
  {
    destruct (Z.gcd_divide_l (u / 2) v) as [z Hz].
    exists (2 * z).
    lia.
  }
  assert (Hd_one : (Z.gcd (u / 2) v | 1)).
  {
    rewrite <- Hgcd.
    apply Z.gcd_greatest.
    - exact Hd_u.
    - apply Z.gcd_divide_r.
  }
  apply Z.divide_1_r in Hd_one.
  pose proof (Z.gcd_nonneg (u / 2) v).
  lia.
Qed.

Lemma gcd_halve_right :
  forall u v,
    Z.land v 1 = 0 ->
    Z.gcd u v = 1 ->
    Z.gcd u (v / 2) = 1.
Proof.
  intros u v Heven Hgcd.
  rewrite Z.gcd_comm.
  apply gcd_halve_left.
  - exact Heven.
  - rewrite Z.gcd_comm.
    exact Hgcd.
Qed.

Local Lemma modulus_above_four_pow253 :
  4 * 2 ^ 253 < modulus.
Proof.
  pose proof modulus_more_than_three_quarters as Hbound.
  replace (2 ^ 254) with (2 * 2 ^ 253) in Hbound.
  - pose proof (Z.pow_pos_nonneg 2 253 ltac:(lia) ltac:(lia)).
    lia.
  - replace 254 with (Z.succ 253) by lia.
    rewrite Z.pow_succ_r by lia.
    reflexivity.
Qed.

Local Lemma positive_right_factor :
  forall x y,
    0 < x ->
    0 < x * y ->
    0 < y.
Proof.
  intros x y Hx Hxy.
  nia.
Qed.

Local Lemma even_half_facts :
  forall x,
    0 < x ->
    x mod 2 = 0 ->
    x = 2 * (x / 2) /\
    0 < x / 2.
Proof.
  intros x Hx Heven.
  pose proof (Z.div_mod x 2 ltac:(lia)) as Hdiv.
  lia.
Qed.

Local Lemma halve_product_bound :
  forall q v bound,
    0 < (2 * q) * v < 2 * bound ->
    0 < q * v < bound.
Proof.
  intros q v bound Hproduct.
  replace ((2 * q) * v) with (2 * (q * v)) in Hproduct by ring.
  lia.
Qed.

Local Lemma sub_halve_product_bound :
  forall q v bound,
    0 < q ->
    0 < v ->
    0 < (2 * q + v) * v < 2 * bound ->
    0 < q * v < bound.
Proof.
  intros q v bound Hq Hv Hproduct.
  assert (Hqv : 0 < q * v) by (apply Z.mul_pos_pos; assumption).
  assert (Hv2 : 0 <= v * v) by (apply Z.mul_nonneg_nonneg; lia).
  replace ((2 * q + v) * v) with (2 * (q * v) + v * v)
    in Hproduct by ring.
  lia.
Qed.

Local Lemma nonnegative_scale_lower_bound :
  forall x factor,
    0 <= x ->
    1 <= factor ->
    x <= x * factor.
Proof.
  intros x factor Hx Hfactor.
  nia.
Qed.

Local Lemma nonnegative_scale_mono :
  forall x lower upper,
    0 <= x ->
    lower <= upper ->
    x * lower <= x * upper.
Proof.
  intros x lower upper Hx Hle.
  apply Z.mul_le_mono_nonneg_l; assumption.
Qed.

Local Lemma halve_left_weighted_identity :
  forall r s q u v,
    u = 2 * q ->
    r * v + s * u = r * v + 2 * s * q.
Proof.
  intros r s q u v Hu.
  subst u.
  ring.
Qed.

Local Lemma halve_right_weighted_identity :
  forall r s q u v,
    v = 2 * q ->
    r * v + s * u = s * u + 2 * r * q.
Proof.
  intros r s q u v Hv.
  subst v.
  ring.
Qed.

Local Lemma halve_right_product_bound :
  forall u v q bound,
    v = 2 * q ->
    0 < u * v < 2 * bound ->
    0 < u * q < bound.
Proof.
  intros u v q bound Hv Hproduct.
  subst v.
  replace (u * (2 * q)) with (2 * (u * q)) in Hproduct by ring.
  lia.
Qed.

Local Lemma sub_halve_weighted_identity :
  forall r s q u v,
    u = 2 * q + v ->
    r * v + s * u = (r + s) * v + 2 * s * q.
Proof.
  intros r s q u v Hu.
  subst u.
  ring.
Qed.

Local Lemma halve_power_identity :
  forall x q power next_power,
    x = 2 * q ->
    next_power = 2 * power ->
    q * next_power = x * power.
Proof.
  intros x q power next_power Hx Hpower.
  subst x.
  subst next_power.
  ring.
Qed.

Local Lemma sub_halve_power_identity :
  forall u v q power next_power,
    u = 2 * q + v ->
    next_power = 2 * power ->
    q * next_power = (u - v) * power.
Proof.
  intros u v q power next_power Hu Hpower.
  subst u.
  subst next_power.
  ring.
Qed.

Local Lemma weighted_sum_bound :
  forall r s q v n bound,
    0 <= r ->
    0 <= s ->
    1 <= q ->
    1 <= v ->
    n = r * v + 2 * s * q ->
    n < bound ->
    r + 2 * s < bound.
Proof.
  intros r s q v n bound Hr Hs Hq Hv Hn Hbound.
  assert (Hrv : r <= r * v).
  { apply nonnegative_scale_lower_bound; assumption. }
  assert (Hsq : 2 * s <= 2 * s * q).
  { apply nonnegative_scale_lower_bound; lia. }
  lia.
Qed.

Local Lemma weighted_double_s_bound :
  forall r s q v n bound,
    0 <= r ->
    0 <= s ->
    2 <= q ->
    0 <= v ->
    n = r * v + 2 * s * q ->
    n < bound ->
    4 * s < bound.
Proof.
  intros r s q v n bound Hr Hs Hq Hv Hn Hbound.
  assert (Hrv : 0 <= r * v) by (apply Z.mul_nonneg_nonneg; assumption).
  assert (Hsq : 4 * s <= 2 * s * q).
  {
    replace (4 * s) with ((2 * s) * 2) by ring.
    apply nonnegative_scale_mono; lia.
  }
  lia.
Qed.

Local Lemma weighted_double_r_bound :
  forall r s q v n bound,
    0 <= r ->
    0 <= s ->
    0 <= q ->
    2 <= v ->
    n = r * v + 2 * s * q ->
    n < bound ->
    2 * r < bound.
Proof.
  intros r s q v n bound Hr Hs Hq Hv Hn Hbound.
  assert (Hrv : 2 * r <= r * v).
  {
    replace (2 * r) with (r * 2) by ring.
    apply nonnegative_scale_mono; lia.
  }
  assert (Hsq : 0 <= 2 * s * q).
  { apply Z.mul_nonneg_nonneg; [lia | exact Hq]. }
  lia.
Qed.

Local Lemma weighted_double_sum_bound :
  forall r s q v n bound,
    0 <= r ->
    0 <= s ->
    0 <= q ->
    3 <= v ->
    n = (r + s) * v + 2 * s * q ->
    n < bound ->
    2 * (r + s) < bound.
Proof.
  intros r s q v n bound Hr Hs Hq Hv Hn Hbound.
  assert (Hrv : 2 * (r + s) <= (r + s) * v).
  {
    replace (2 * (r + s)) with ((r + s) * 2) by ring.
    apply nonnegative_scale_mono; lia.
  }
  assert (Hsq : 0 <= 2 * s * q).
  { apply Z.mul_nonneg_nonneg; [lia | exact Hq]. }
  lia.
Qed.

Local Lemma gcd_sub_halve_left :
  forall u v,
    u mod 2 = 1 ->
    v mod 2 = 1 ->
    Z.gcd u v = 1 ->
    Z.gcd ((u - v) / 2) v = 1.
Proof.
  intros u v Huodd Hvodd Huvgcd.
  assert (Heven : (u - v) mod 2 = 0).
  {
    pose proof (Z.div_mod u 2 ltac:(lia)) as Hu.
    pose proof (Z.div_mod v 2 ltac:(lia)) as Hv.
    pose proof (Z.mod_pos_bound (u - v) 2 ltac:(lia)) as Hbound.
    pose proof (Z.div_mod (u - v) 2 ltac:(lia)) as Hdiff.
    lia.
  }
  apply gcd_halve_left.
  - rewrite land_one_eq_mod_two.
    exact Heven.
  - rewrite Z.gcd_comm.
    rewrite Z.gcd_sub_diag_r.
    rewrite Z.gcd_comm.
    exact Huvgcd.
Qed.

(** ** Phase I initialization *)

Lemma mont_inv_phase1_init :
  forall a,
    0 < a < modulus ->
    Z.gcd a modulus = 1 ->
    mont_inv_phase1_state a modulus a 0 1 0 0.
Proof.
  intros a Ha Hgcd.
  pose proof modulus_bounds as Hn.
  unfold mont_inv_phase1_state,
    mont_inv_phase1_progress,
    mont_inv_phase1_overflow_reach,
    mont_inv_phase1_exit_carry.
  rewrite !land_one_eq_mod_two.
  split; [exact Ha |].
  split; [lia |].
  split; [lia |].
  split; [unfold U256_MOD; lia |].
  split; [unfold U256_MOD; lia |].
  split; [lia |].
  split; [lia |].
  split; [exact Hgcd |].
  split; [rewrite Z.gcd_comm; exact Hgcd |].
  split.
  - split; [lia |].
    split; [lia |].
    split; [lia |].
    split.
    + intros Ha0.
      assert (Hsq : modulus * modulus < 2 ^ 512).
      {
        replace (2 ^ 512) with (U256_MOD * U256_MOD).
        - eapply Z.lt_trans.
          + apply Z.mul_lt_mono_pos_r.
            exact (proj1 Hn).
            exact (proj2 Hn).
          + apply Z.mul_lt_mono_pos_l.
            unfold U256_MOD; lia.
            exact (proj2 Hn).
        - unfold U256_MOD.
          rewrite <- Z.pow_add_r by lia.
          reflexivity.
      }
      split.
      * apply Z.mul_pos_pos.
        -- exact (proj1 Hn).
        -- exact (proj1 Ha).
      * eapply Z.lt_trans.
        -- apply Z.mul_lt_mono_pos_l.
           ++ exact (proj1 Hn).
           ++ exact (proj2 Ha).
        -- exact Hsq.
    + intros Heq. lia.
  - split.
    + split; [ring |].
      intros Ha0.
      split; [lia |].
      split; [unfold U256_MOD; lia |].
      split; intros; unfold U256_MOD; lia.
    + split.
      * replace
          (a * (0 + 0 * U256_MOD) + modulus * 2 ^ 0)
          with modulus by ring.
        apply Z.mod_same.
        lia.
      * split.
        -- replace (a * 1 - a * 2 ^ 0) with 0 by ring.
           apply Zmod_0_l.
        -- intros Ha0. lia.
Qed.

Lemma mont_inv_phase1_init_nonzero :
  forall a,
    0 <= a < modulus ->
    a <> 0 ->
    mont_inv_phase1_state a modulus a 0 1 0 0.
Proof.
  intros a Ha Ha0.
  apply mont_inv_phase1_init.
  - lia.
  - apply modulus_nonzero_gcd_one; assumption.
Qed.

(** ** Phase I even transitions *)

Lemma mont_inv_phase1_halve_u :
  forall a u v r s k carry y,
    mont_inv_phase1_state a u v r s k carry ->
    v <> 0 ->
    Z.land u 1 = 0 ->
    y = 2 * s ->
    mont_inv_phase1_state
      a (u / 2) v r y (unsigned_last_nbits (k + 1) 64) carry.
Proof.
  intros a u v r s k carry y Hstate Hv0 Hueven Hy2s.
  unfold mont_inv_phase1_state in Hstate.
  destruct Hstate as
    (Ha & Hu & Hv & Hr & Hs & Hk & Hcarry & Hagcd & Huvgcd &
     Hprogress & Hoverflow & Hmodu & Hmodv & Hexit).
  unfold mont_inv_phase1_progress in Hprogress.
  destruct Hprogress as (Hupos & Hrpow & Hspow & Hprod & Hequal).
  unfold mont_inv_phase1_overflow_reach in Hoverflow.
  rewrite !land_one_eq_mod_two in Hoverflow.
  rewrite land_one_eq_mod_two in Hueven.
  destruct Hoverflow as [Hbez Hoverflow].
  specialize (Hoverflow Hv0).
  destruct Hoverflow as (Hcarry0 & Hrs & Hdouble_s & Hdouble_r).
  assert (H2s : 2 * s < U256_MOD).
  {
    apply Hdouble_s.
    left.
    exact Hueven.
  }
  subst y.
  assert (Hklt : k < 512).
  {
    specialize (Hprod Hv0).
    destruct Hprod as [Hprod0 Hprod1].
    destruct Hk as [Hk0 Hk1].
    assert (k < 512 \/ k = 512) by lia.
    destruct H as [H | H]; [exact H |].
    subst k. cbn in Hprod1. lia.
  }
  assert (Hknorm : unsigned_last_nbits (k + 1) 64 = k + 1).
  {
    apply unsigned_last_nbits_eq.
    split; [lia |].
    assert (Hpow10 : 513 < 2 ^ 10) by (change (513 < 1024); lia).
    assert (Hpowmono : 2 ^ 10 <= 2 ^ 64).
    { apply Z.pow_le_mono_r; lia. }
    lia.
  }
  rewrite Hknorm.
  destruct (even_half_facts u Hupos Hueven) as [Hueq Huhalfpos].
  assert (Hvgpos : 0 < v).
  {
    apply (positive_right_factor u v Hupos).
    exact (proj1 (Hprod Hv0)).
  }
  assert (Hgcdhalf : Z.gcd (u / 2) v = 1).
  {
    apply gcd_halve_left.
    - rewrite land_one_eq_mod_two. exact Hueven.
    - exact Huvgcd.
  }
  assert (Hpow_succ : 2 ^ (k + 1) = 2 * 2 ^ k).
  {
    replace (k + 1) with (Z.succ k) by lia.
    rewrite Z.pow_succ_r by lia.
    reflexivity.
  }
  assert (Hbez_half :
    modulus = r * v + 2 * s * (u / 2)).
  {
    rewrite <- Hbez.
    apply halve_left_weighted_identity.
    exact Hueq.
  }
  unfold mont_inv_phase1_state.
  split; [exact Ha |].
  split; [lia |].
  split; [exact Hv |].
  split; [exact Hr |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [exact Hagcd |].
  split; [exact Hgcdhalf |].
  split.
  - unfold mont_inv_phase1_progress.
    split; [exact Huhalfpos |].
    split; [rewrite Hpow_succ; lia |].
    split; [rewrite Hpow_succ; lia |].
    split.
    + intros _.
      specialize (Hprod Hv0).
      replace (512 - k) with (Z.succ (512 - (k + 1))) in Hprod by lia.
      rewrite Z.pow_succ_r in Hprod by lia.
      apply halve_product_bound.
      rewrite <- Hueq.
      exact Hprod.
    + intros Heq.
      assert (Hvdiv : (v | 1)).
      {
        rewrite <- Hgcdhalf, Heq.
        apply Z.gcd_greatest; apply Z.divide_refl.
      }
      apply Z.divide_1_r in Hvdiv.
      assert (Hvone : v = 1) by lia.
      assert (Huone : u = 2) by lia.
      assert (Hpowbound : k < 255 -> 2 ^ k <= 2 ^ 254).
      { intros Hsmallk. apply Z.pow_le_mono_r; lia. }
      pose proof modulus_more_than_three_quarters as Hconstant.
      destruct (Z_lt_ge_dec k 255); [| lia].
      specialize (Hpowbound l).
      rewrite Heq, Hvone in Hbez_half.
      replace (r * 1 + 2 * s * 1) with (r + 2 * s) in Hbez_half by ring.
      lia.
  - split.
    + unfold mont_inv_phase1_overflow_reach.
      rewrite !land_one_eq_mod_two.
      split; [symmetry; exact Hbez_half |].
      intros _.
      split; [exact Hcarry0 |].
      split.
      {
        eapply weighted_sum_bound with
          (q := u / 2) (v := v) (n := modulus).
        - exact (proj1 Hr).
        - exact (proj1 Hs).
        - lia.
        - lia.
        - exact Hbez_half.
        - exact (proj2 modulus_bounds).
      }
      split.
      * intros Hcase.
        assert (Hq2 : 2 <= u / 2).
        {
          destruct Hcase as [Hqeven | (Hqodd & Hvodd & Hqgt)].
          - assert (u / 2 <> 1).
            { intros Heq1. rewrite Heq1 in Hqeven. cbn in Hqeven. discriminate. }
            lia.
          - lia.
        }
        replace (2 * (2 * s)) with (4 * s) by ring.
        eapply weighted_double_s_bound with
          (r := r) (q := u / 2) (v := v) (n := modulus).
        -- exact (proj1 Hr).
        -- exact (proj1 Hs).
        -- exact Hq2.
        -- lia.
        -- exact Hbez_half.
        -- exact (proj2 modulus_bounds).
      * intros (_ & Hcase).
        assert (Hv2 : 2 <= v).
        {
          destruct Hcase as [Hveven | (Hvodd & Hqlt)].
          - assert (v <> 1).
            { intros Heq1. subst. cbn in Hveven. discriminate. }
            lia.
          - lia.
        }
        eapply weighted_double_r_bound with
          (s := s) (q := u / 2) (v := v) (n := modulus).
        -- exact (proj1 Hr).
        -- exact (proj1 Hs).
        -- lia.
        -- exact Hv2.
        -- exact Hbez_half.
        -- exact (proj2 modulus_bounds).
    + split.
      * replace
          (a * (r + carry * U256_MOD) + (u / 2) * 2 ^ (k + 1))
          with (a * (r + carry * U256_MOD) + u * 2 ^ k)
          by (rewrite (halve_power_identity u (u / 2) (2 ^ k)
                (2 ^ (k + 1)) Hueq Hpow_succ); reflexivity).
        exact Hmodu.
      * split.
        -- replace (a * (2 * s) - v * 2 ^ (k + 1))
             with (2 * (a * s - v * 2 ^ k)) by
             (rewrite Hpow_succ; ring).
           rewrite Z.mul_mod by (pose proof modulus_bounds; lia).
           rewrite Hmodv.
           rewrite Z.mul_0_r.
           apply Zmod_0_l.
        -- intros Hvzero. contradiction.
Qed.

Lemma mont_inv_phase1_halve_v :
  forall a u v r s k carry y,
    mont_inv_phase1_state a u v r s k carry ->
    v <> 0 ->
    Z.land u 1 = 1 ->
    Z.land v 1 = 0 ->
    y = 2 * r ->
    mont_inv_phase1_state
      a u (v / 2) y s (unsigned_last_nbits (k + 1) 64) carry.
Proof.
  intros a u v r s k carry y Hstate Hv0 Huodd Hveven Hy2r.
  unfold mont_inv_phase1_state in Hstate.
  destruct Hstate as
    (Ha & Hu & Hv & Hr & Hs & Hk & Hcarry & Hagcd & Huvgcd &
     Hprogress & Hoverflow & Hmodu & Hmodv & Hexit).
  unfold mont_inv_phase1_progress in Hprogress.
  destruct Hprogress as (Hupos & Hrpow & Hspow & Hprod & Hequal).
  unfold mont_inv_phase1_overflow_reach in Hoverflow.
  rewrite !land_one_eq_mod_two in Hoverflow.
  rewrite !land_one_eq_mod_two in Huodd, Hveven.
  destruct Hoverflow as [Hbez Hoverflow].
  specialize (Hoverflow Hv0).
  destruct Hoverflow as (Hcarry0 & Hrs & Hdouble_s & Hdouble_r).
  assert (H2r : 2 * r < U256_MOD).
  {
    apply Hdouble_r.
    split; [exact Huodd |].
    left.
    exact Hveven.
  }
  subst y.
  assert (Hklt : k < 512).
  {
    specialize (Hprod Hv0).
    destruct Hprod as [Hprod0 Hprod1].
    destruct Hk as [Hk0 Hk1].
    assert (k < 512 \/ k = 512) by lia.
    destruct H as [H | H]; [exact H |].
    subst k. cbn in Hprod1. lia.
  }
  assert (Hknorm : unsigned_last_nbits (k + 1) 64 = k + 1).
  {
    apply unsigned_last_nbits_eq.
    split; [lia |].
    assert (Hpow10 : 513 < 2 ^ 10) by (change (513 < 1024); lia).
    assert (Hpowmono : 2 ^ 10 <= 2 ^ 64).
    { apply Z.pow_le_mono_r; lia. }
    lia.
  }
  rewrite Hknorm.
  assert (Hvgpos : 0 < v) by lia.
  destruct (even_half_facts v Hvgpos Hveven) as [Hveq Hvhalfpos].
  assert (Hgcdhalf : Z.gcd u (v / 2) = 1).
  {
    apply gcd_halve_right.
    - rewrite land_one_eq_mod_two. exact Hveven.
    - exact Huvgcd.
  }
  assert (Hpow_succ : 2 ^ (k + 1) = 2 * 2 ^ k).
  {
    replace (k + 1) with (Z.succ k) by lia.
    rewrite Z.pow_succ_r by lia.
    reflexivity.
  }
  assert (Hbez_half :
    modulus = s * u + 2 * r * (v / 2)).
  {
    rewrite <- Hbez.
    apply halve_right_weighted_identity.
    exact Hveq.
  }
  unfold mont_inv_phase1_state.
  split; [exact Ha |].
  split; [exact Hu |].
  split; [lia |].
  split; [lia |].
  split; [exact Hs |].
  split; [lia |].
  split; [lia |].
  split; [exact Hagcd |].
  split; [exact Hgcdhalf |].
  split.
  - unfold mont_inv_phase1_progress.
    split; [exact Hupos |].
    split; [rewrite Hpow_succ; lia |].
    split; [rewrite Hpow_succ; lia |].
    split.
    + intros _.
      specialize (Hprod Hv0).
      replace (512 - k) with (Z.succ (512 - (k + 1))) in Hprod by lia.
      rewrite Z.pow_succ_r in Hprod by lia.
      eapply halve_right_product_bound.
      * exact Hveq.
      * exact Hprod.
    + intros Heq.
      assert (Hudiv : (u | 1)).
      {
        rewrite <- Hgcdhalf, Heq.
        apply Z.gcd_greatest; apply Z.divide_refl.
      }
      apply Z.divide_1_r in Hudiv.
      assert (Huone : u = 1) by lia.
      assert (Hvone : v = 2) by lia.
      assert (Hpowbound : k < 255 -> 2 ^ k <= 2 ^ 254).
      { intros Hsmallk. apply Z.pow_le_mono_r; lia. }
      pose proof modulus_more_than_three_quarters as Hconstant.
      destruct (Z_lt_ge_dec k 255); [| lia].
      specialize (Hpowbound l).
      rewrite <- Heq, Huone in Hbez_half.
      replace (s * 1 + 2 * r * 1) with (s + 2 * r) in Hbez_half by ring.
      lia.
  - split.
    + unfold mont_inv_phase1_overflow_reach.
      rewrite !land_one_eq_mod_two.
      split.
      {
        symmetry.
        rewrite Hbez_half.
        ring.
      }
      intros Hq0.
      split; [exact Hcarry0 |].
      split.
      {
        replace (2 * r + s) with (s + 2 * r) by ring.
        eapply weighted_sum_bound with
          (r := s) (s := r) (q := v / 2) (v := u)
          (n := modulus).
        - exact (proj1 Hs).
        - exact (proj1 Hr).
        - lia.
        - lia.
        - exact Hbez_half.
        - exact (proj2 modulus_bounds).
      }
      split.
      * intros Hcase.
        assert (Hu2 : 2 <= u).
        {
          destruct Hcase as [Hueven | (Huodd' & Hqodd & Hugt)].
          - rewrite Huodd in Hueven. discriminate.
          - lia.
        }
        eapply weighted_double_r_bound with
          (r := s) (s := r) (q := v / 2) (v := u)
          (n := modulus).
        -- exact (proj1 Hs).
        -- exact (proj1 Hr).
        -- lia.
        -- exact Hu2.
        -- exact Hbez_half.
        -- exact (proj2 modulus_bounds).
      * intros (_ & Hcase).
        assert (Hq2 : 2 <= v / 2).
        {
          destruct Hcase as [Hqeven | (Hqodd & Hult)].
          - assert (v / 2 <> 1).
            { intros Heq1. rewrite Heq1 in Hqeven. cbn in Hqeven. discriminate. }
            lia.
          - lia.
        }
        replace (2 * (2 * r)) with (4 * r) by ring.
        eapply weighted_double_s_bound with
          (r := s) (s := r) (q := v / 2) (v := u)
          (n := modulus).
        -- exact (proj1 Hs).
        -- exact (proj1 Hr).
        -- exact Hq2.
        -- lia.
        -- exact Hbez_half.
        -- exact (proj2 modulus_bounds).
    + split.
      * replace
          (a * (2 * r + carry * U256_MOD) + u * 2 ^ (k + 1))
          with (2 * (a * (r + carry * U256_MOD) + u * 2 ^ k))
          by (rewrite Hcarry0, Hpow_succ; ring).
        rewrite Z.mul_mod by (pose proof modulus_bounds; lia).
        rewrite Hmodu.
        rewrite Z.mul_0_r.
        apply Zmod_0_l.
      * split.
        -- replace (a * s - (v / 2) * 2 ^ (k + 1))
             with (a * s - v * 2 ^ k) by
             (rewrite (halve_power_identity v (v / 2) (2 ^ k)
                (2 ^ (k + 1)) Hveq Hpow_succ); reflexivity).
           exact Hmodv.
        -- intros Hvhalf0. lia.
Qed.

(** ** Phase I odd transitions *)

Lemma mont_inv_phase1_sub_halve_u :
  forall a u v r s k carry,
    mont_inv_phase1_state a u v r s k carry ->
    v <> 0 ->
    Z.land u 1 = 1 ->
    Z.land v 1 = 1 ->
    u > v ->
    mont_inv_phase1_state
      a ((u - v) / 2) v (r + s) (2 * s)
      (unsigned_last_nbits (k + 1) 64) carry.
Proof.
  intros a u v r s k carry Hstate Hv0 Huodd Hvodd Huv.
  unfold mont_inv_phase1_state in Hstate.
  destruct Hstate as
    (Ha & Hu & Hv & Hr & Hs & Hk & Hcarry & Hagcd & Huvgcd &
     Hprogress & Hoverflow & Hmodu & Hmodv & Hexit).
  unfold mont_inv_phase1_progress in Hprogress.
  destruct Hprogress as (Hupos & Hrpow & Hspow & Hprod & Hequal).
  specialize (Hprod Hv0).
  unfold mont_inv_phase1_overflow_reach in Hoverflow.
  rewrite !land_one_eq_mod_two in Hoverflow.
  rewrite !land_one_eq_mod_two in Huodd, Hvodd.
  destruct Hoverflow as [Hbez Hoverflow].
  specialize (Hoverflow Hv0).
  destruct Hoverflow as (Hcarry0 & Hrs & Hdouble_s & Hdouble_r).
  assert (Hvgpos : 0 < v) by lia.
  assert (Hklt : k < 512).
  {
    destruct Hprod as [Hprod0 Hprod1].
    destruct Hk as [Hk0 Hk1].
    assert (k < 512 \/ k = 512) by lia.
    destruct H as [H | H]; [exact H |].
    subst k. cbn in Hprod1. lia.
  }
  assert (Hknorm : unsigned_last_nbits (k + 1) 64 = k + 1).
  {
    apply unsigned_last_nbits_eq.
    split; [lia |].
    assert (Hpow10 : 513 < 2 ^ 10) by (change (513 < 1024); lia).
    assert (Hpowmono : 2 ^ 10 <= 2 ^ 64).
    { apply Z.pow_le_mono_r; lia. }
    lia.
  }
  pose proof (Z.div_mod u 2 ltac:(lia)) as Hudiv.
  pose proof (Z.div_mod v 2 ltac:(lia)) as Hvdiv.
  pose proof (Z.div_mod (u - v) 2 ltac:(lia)) as Hdiffdiv.
  pose proof (Z.mod_pos_bound (u - v) 2 ltac:(lia)) as Hdiffbound.
  assert (Hdiffmod : (u - v) mod 2 = 0) by lia.
  assert (Hdiff : u - v = 2 * ((u - v) / 2)) by lia.
  assert (Hudecomp : u = 2 * ((u - v) / 2) + v) by lia.
  assert (Hqpos : 0 < (u - v) / 2) by lia.
  assert (Hgcdnew : Z.gcd ((u - v) / 2) v = 1).
  {
    apply gcd_sub_halve_left; assumption.
  }
  assert (Hpow_succ : 2 ^ (k + 1) = 2 * 2 ^ k).
  {
    replace (k + 1) with (Z.succ k) by lia.
    rewrite Z.pow_succ_r by lia.
    ring.
  }
  assert (Hbez_sub :
    modulus = (r + s) * v + 2 * s * ((u - v) / 2)).
  {
    rewrite <- Hbez.
    apply sub_halve_weighted_identity.
    exact Hudecomp.
  }
  rewrite Hknorm.
  unfold mont_inv_phase1_state.
  split; [exact Ha |].
  split; [lia |].
  split; [exact Hv |].
  split; [lia |].
  split.
  {
    assert (H2s : 2 * s < U256_MOD).
    { apply Hdouble_s. right. repeat split; assumption. }
    lia.
  }
  split; [lia |].
  split; [lia |].
  split; [exact Hagcd |].
  split; [exact Hgcdnew |].
  split.
  - unfold mont_inv_phase1_progress.
    split; [exact Hqpos |].
    split; [rewrite Hpow_succ; lia |].
    split; [rewrite Hpow_succ; lia |].
    split.
    + intros Hqv0.
      replace (512 - k) with (Z.succ (512 - (k + 1))) in Hprod by lia.
      rewrite Z.pow_succ_r in Hprod by lia.
      apply sub_halve_product_bound.
      * exact Hqpos.
      * exact Hvgpos.
      * rewrite <- Hudecomp.
        exact Hprod.
    + intros Hqeq.
      assert (Hvone : v = 1).
      {
        assert (Hvdiv1 : (v | 1)).
        {
          rewrite <- Hgcdnew, Hqeq.
          apply Z.gcd_greatest; apply Z.divide_refl.
        }
        apply Z.divide_1_r in Hvdiv1.
        lia.
      }
      assert (Hqone : (u - v) / 2 = 1) by lia.
      assert (Hu3 : u = 3) by lia.
      pose proof modulus_above_four_pow253 as Hconstant.
      destruct (Z_lt_ge_dec k 254) as [Hsmall | Hlarge]; [|lia].
      assert (Hpowbound : 2 ^ k <= 2 ^ 253).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hqeq, Hvone in Hbez_sub.
      replace ((r + s) * 1 + 2 * s * 1)
        with (r + 3 * s) in Hbez_sub by ring.
      lia.
  - split.
    + unfold mont_inv_phase1_overflow_reach.
      rewrite !land_one_eq_mod_two.
      split; [symmetry; exact Hbez_sub |].
      intros Hqv0.
      split; [exact Hcarry0 |].
      split.
      {
        change (r + s + 2 * s < U256_MOD).
        eapply weighted_sum_bound with
          (r := r + s) (s := s) (q := (u - v) / 2) (v := v)
          (n := modulus).
        - lia.
        - exact (proj1 Hs).
        - lia.
        - lia.
        - exact Hbez_sub.
        - exact (proj2 modulus_bounds).
      }
      split.
      * intros Hcase.
        assert (Hq2 : 2 <= (u - v) / 2).
        {
          destruct Hcase as [Hqeven | (Hqodd & Hvodd' & Hqgt)].
          - assert ((u - v) / 2 <> 1).
            { intros Heq. rewrite Heq in Hqeven. discriminate. }
            lia.
          - lia.
        }
        replace (2 * (2 * s)) with (4 * s) by ring.
        eapply weighted_double_s_bound with
          (r := r + s) (q := (u - v) / 2) (v := v)
          (n := modulus).
        -- lia.
        -- exact (proj1 Hs).
        -- exact Hq2.
        -- lia.
        -- exact Hbez_sub.
        -- exact (proj2 modulus_bounds).
      * intros (Hqodd & Hcase).
        destruct Hcase as [Hveven | (Hvodd' & Hqlt)].
        { rewrite Hvodd in Hveven. discriminate. }
        assert (Hv3 : 3 <= v).
        {
          pose proof (Z.div_mod v 2 ltac:(lia)).
          pose proof (Z.mod_pos_bound v 2 ltac:(lia)).
          lia.
        }
        eapply weighted_double_sum_bound with
          (q := (u - v) / 2) (v := v) (n := modulus).
        -- exact (proj1 Hr).
        -- exact (proj1 Hs).
        -- lia.
        -- exact Hv3.
        -- exact Hbez_sub.
        -- exact (proj2 modulus_bounds).
    + split.
      * replace
          (a * (r + s + carry * U256_MOD) +
             (u - v) / 2 * 2 ^ (k + 1))
          with
          ((a * (r + carry * U256_MOD) + u * 2 ^ k) +
             (a * s - v * 2 ^ k))
          by (rewrite Hcarry0;
              rewrite (sub_halve_power_identity u v ((u - v) / 2)
                (2 ^ k) (2 ^ (k + 1)) Hudecomp Hpow_succ);
              ring).
        rewrite Z.add_mod by (pose proof modulus_bounds; lia).
        rewrite Hmodu, Hmodv.
        reflexivity.
      * split.
        -- replace (a * (2 * s) - v * 2 ^ (k + 1))
             with (2 * (a * s - v * 2 ^ k))
             by (rewrite Hpow_succ; ring).
           rewrite Z.mul_mod by (pose proof modulus_bounds; lia).
           rewrite Hmodv.
           rewrite Z.mul_0_r.
           apply Zmod_0_l.
        -- intros Hzero. lia.
Qed.

Local Lemma gcd_sub_halve_right :
  forall u v,
    Z.land u 1 = 1 ->
    Z.land v 1 = 1 ->
    Z.gcd u v = 1 ->
    Z.gcd u ((v - u) / 2) = 1.
Proof.
  intros u v Huodd Hvodd Huvgcd.
  rewrite Z.gcd_comm.
  apply gcd_sub_halve_left.
  - rewrite land_one_eq_mod_two in Hvodd.
    exact Hvodd.
  - rewrite land_one_eq_mod_two in Huodd.
    exact Huodd.
  - rewrite Z.gcd_comm.
    exact Huvgcd.
Qed.

Local Lemma mont_inv_phase1_sub_halve_v_strict :
  forall a u v r s k carry y out,
    mont_inv_phase1_state a u v r s k carry ->
    v <> 0 ->
    Z.land u 1 = 1 ->
    Z.land v 1 = 1 ->
    u < v ->
    u256_shl_result r y out ->
    mont_inv_phase1_state
      a u ((v - u) / 2) y (r + s)
      (unsigned_last_nbits (k + 1) 64)
      (unsigned_last_nbits (carry + out) 8).
Proof.
  intros a u v r s k carry y out Hstate Hv0 Huodd Hvodd Huv Hshift.
  unfold mont_inv_phase1_state in Hstate.
  destruct Hstate as
    (Ha & Hu & Hv & Hr & Hs & Hk & Hcarry & Hagcd & Huvgcd &
     Hprogress & Hoverflow & Hmodu & Hmodv & Hexit).
  unfold mont_inv_phase1_progress in Hprogress.
  destruct Hprogress as (Hupos & Hrpow & Hspow & Hprod & Hequal).
  specialize (Hprod Hv0).
  unfold mont_inv_phase1_overflow_reach in Hoverflow.
  rewrite !land_one_eq_mod_two in Hoverflow.
  destruct Hoverflow as [Hbez Hoverflow].
  specialize (Hoverflow Hv0).
  destruct Hoverflow as (Hcarry0 & Hrs & Hdouble_s & Hdouble_r).
  assert (H2r : 2 * r < U256_MOD).
  {
    apply Hdouble_r.
    split.
    - rewrite <- land_one_eq_mod_two. exact Huodd.
    - right. split.
      + rewrite <- land_one_eq_mod_two. exact Hvodd.
      + exact Huv.
  }
  destruct (u256_shl_result_no_overflow r y out Hshift H2r)
    as [Hy2r Hout0].
  subst y out.
  assert (Hvgpos : 0 < v) by lia.
  assert (Hklt : k < 512).
  {
    destruct Hprod as [Hprod0 Hprod1].
    destruct Hk as [Hk0 Hk1].
    destruct (Z.eq_dec k 512) as [Heq512 | Hneq512]; [|lia].
    subst k. cbn in Hprod1. lia.
  }
  assert (Hknorm : unsigned_last_nbits (k + 1) 64 = k + 1).
  {
    apply unsigned_last_nbits_eq.
    split; [lia |].
    assert (Hpow10 : 513 < 2 ^ 10) by (change (513 < 1024); lia).
    assert (Hpowmono : 2 ^ 10 <= 2 ^ 64).
    { apply Z.pow_le_mono_r; lia. }
    lia.
  }
  assert (Hcarrynorm : unsigned_last_nbits (carry + 0) 8 = 0).
  { rewrite Hcarry0. reflexivity. }
  rewrite land_one_eq_mod_two in Huodd, Hvodd.
  pose proof (Z.div_mod u 2 ltac:(lia)) as Hudiv.
  pose proof (Z.div_mod v 2 ltac:(lia)) as Hvdiv.
  pose proof (Z.div_mod (v - u) 2 ltac:(lia)) as Hdiffdiv.
  pose proof (Z.mod_pos_bound (v - u) 2 ltac:(lia)) as Hdiffbound.
  assert (Hdiffmod : (v - u) mod 2 = 0) by lia.
  assert (Hdiff : v - u = 2 * ((v - u) / 2)) by lia.
  assert (Hvdecomp : v = 2 * ((v - u) / 2) + u) by lia.
  assert (Hqpos : 0 < (v - u) / 2) by lia.
  assert (Hgcdnew : Z.gcd u ((v - u) / 2) = 1).
  {
    apply gcd_sub_halve_right.
    - rewrite land_one_eq_mod_two. exact Huodd.
    - rewrite land_one_eq_mod_two. exact Hvodd.
    - exact Huvgcd.
  }
  assert (Hpow_succ : 2 ^ (k + 1) = 2 * 2 ^ k).
  {
    replace (k + 1) with (Z.succ k) by lia.
    rewrite Z.pow_succ_r by lia.
    reflexivity.
  }
  assert (Hbez_sub :
    modulus = (2 * r) * ((v - u) / 2) + (r + s) * u).
  {
    replace v with (2 * ((v - u) / 2) + u) in Hbez by
      (symmetry; exact Hvdecomp).
    rewrite <- Hbez.
    ring.
  }
  rewrite Hknorm, Hcarrynorm.
  unfold mont_inv_phase1_state.
  split; [exact Ha |].
  split; [exact Hu |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [exact Hagcd |].
  split; [exact Hgcdnew |].
  split.
  - unfold mont_inv_phase1_progress.
    split; [exact Hupos |].
    split; [rewrite Hpow_succ; lia |].
    split; [rewrite Hpow_succ; lia |].
    split.
    + intros _.
      replace (512 - k) with (Z.succ (512 - (k + 1))) in Hprod by lia.
      rewrite Z.pow_succ_r in Hprod by lia.
      assert (Huq : 0 < u * ((v - u) / 2)).
      { apply Z.mul_pos_pos; assumption. }
      rewrite Hvdecomp in Hprod.
      assert (Husq : 0 <= u * u) by
        (apply Z.mul_nonneg_nonneg; lia).
      replace (u * (2 * ((v - u) / 2) + u))
        with (2 * (u * ((v - u) / 2)) + u * u) in Hprod by ring.
      lia.
    + intros Heq.
      assert (Huone : u = 1).
      {
        assert (Hgcduu : Z.gcd u u = 1).
        { replace u with ((v - u) / 2) at 2 by
            (symmetry; exact Heq).
          exact Hgcdnew. }
        rewrite Z.gcd_diag, Z.abs_eq in Hgcduu by lia.
        exact Hgcduu.
      }
      assert (Hqone : (v - u) / 2 = 1) by lia.
      assert (Hvthree : v = 3) by lia.
      destruct (Z_lt_ge_dec k 254) as [Hsmall | Hlarge]; [|lia].
      assert (Hpowbound : 2 ^ k <= 2 ^ 253).
      { apply Z.pow_le_mono_r; lia. }
      pose proof modulus_above_four_pow253 as Hconstant.
      assert (Hbez_small : 3 * r + s = modulus).
      { rewrite Huone, Hvthree in Hbez. lia. }
      lia.
  - split.
    + unfold mont_inv_phase1_overflow_reach.
      rewrite !land_one_eq_mod_two.
      split; [symmetry; exact Hbez_sub |].
      intros Hq0.
      split; [reflexivity |].
      split.
      {
        replace (2 * r + (r + s)) with (r + s + 2 * r) by ring.
        eapply weighted_sum_bound with
          (r := r + s) (s := r) (q := (v - u) / 2) (v := u)
          (n := modulus).
        - lia.
        - exact (proj1 Hr).
        - lia.
        - lia.
        - rewrite Hbez_sub. ring.
        - exact (proj2 modulus_bounds).
      }
      split.
      * intros Hcase.
        destruct Hcase as [Hueven | (Huodd' & Hqodd & Hugt)].
        { rewrite Huodd in Hueven. discriminate. }
        assert (Hu3 : 3 <= u).
        {
          pose proof (Z.div_mod u 2 ltac:(lia)) as Hdivu.
          pose proof (Z.mod_pos_bound u 2 ltac:(lia)) as Hmodu2.
          lia.
        }
        replace (2 * (r + s)) with (2 * (s + r)) by ring.
        eapply weighted_double_sum_bound with
          (r := s) (s := r) (q := (v - u) / 2) (v := u)
          (n := modulus).
        -- exact (proj1 Hs).
        -- exact (proj1 Hr).
        -- lia.
        -- exact Hu3.
        -- rewrite Hbez_sub. ring.
        -- exact (proj2 modulus_bounds).
      * intros (_ & Hcase).
        assert (Hq2 : 2 <= (v - u) / 2).
        {
          destruct Hcase as [Hqeven | (Hqodd & Hult)].
          - assert ((v - u) / 2 <> 1).
            { intros Heq1. rewrite Heq1 in Hqeven. discriminate. }
            lia.
          - lia.
        }
        change (2 * (2 * r) < U256_MOD).
        replace (2 * (2 * r)) with (4 * r) by ring.
        eapply weighted_double_s_bound with
          (r := r + s) (s := r) (q := (v - u) / 2) (v := u)
          (n := modulus).
        -- lia.
        -- exact (proj1 Hr).
        -- exact Hq2.
        -- lia.
        -- rewrite Hbez_sub. ring.
        -- exact (proj2 modulus_bounds).
    + split.
      * replace
          (a * (2 * r + 0 * U256_MOD) + u * 2 ^ (k + 1))
          with (2 * (a * (r + carry * U256_MOD) + u * 2 ^ k))
          by (rewrite Hcarry0, Hpow_succ; ring).
        rewrite Z.mul_mod by (pose proof modulus_bounds; lia).
        rewrite Hmodu.
        rewrite Z.mul_0_r.
        apply Zmod_0_l.
      * split.
        -- replace
             (a * (r + s) - (v - u) / 2 * 2 ^ (k + 1))
             with
             ((a * (r + carry * U256_MOD) + u * 2 ^ k) +
                (a * s - v * 2 ^ k))
             by (rewrite Hcarry0, Hpow_succ;
                 replace ((v - u) / 2 * (2 * 2 ^ k))
                   with ((2 * ((v - u) / 2)) * 2 ^ k) by ring;
                 rewrite <- Hdiff;
                 ring).
           rewrite Z.add_mod by (pose proof modulus_bounds; lia).
           rewrite Hmodu, Hmodv.
           reflexivity.
        -- intros Hzero. lia.
Qed.

Local Lemma mont_inv_phase1_sub_halve_v_equal :
  forall a u r s k carry y out,
    mont_inv_phase1_state a u u r s k carry ->
    u <> 0 ->
    u256_shl_result r y out ->
    mont_inv_phase1_state
      a u ((u - u) / 2) y (r + s)
      (unsigned_last_nbits (k + 1) 64)
      (unsigned_last_nbits (carry + out) 8).
Proof.
  intros a u r s k carry y out Hstate Hu0 Hshift.
  replace ((u - u) / 2) with 0 by
    (replace (u - u) with 0 by ring; reflexivity).
  unfold mont_inv_phase1_state in Hstate.
  destruct Hstate as
    (Ha & Hu & Hv & Hr & Hs & Hk & Hcarry & Hagcd & Huugcd &
     Hprogress & Hoverflow & Hmodu & Hmodv & Hexit).
  unfold mont_inv_phase1_progress in Hprogress.
  destruct Hprogress as (Hupos & Hrpow & Hspow & Hprod & Hequal).
  specialize (Hprod Hu0).
  specialize (Hequal eq_refl).
  unfold mont_inv_phase1_overflow_reach in Hoverflow.
  destruct Hoverflow as [Hbez Hoverflow].
  specialize (Hoverflow Hu0).
  destruct Hoverflow as (Hcarry0 & Hrs & Hdouble_s & Hdouble_r).
  unfold u256_shl_result in Hshift.
  destruct Hshift as (Hrx & Hy & Hout & Hshift).
  assert (Huone : u = 1).
  {
    rewrite Z.gcd_diag, Z.abs_eq in Huugcd by lia.
    exact Huugcd.
  }
  subst u.
  assert (Hbez' : r + s = modulus) by nia.
  assert (Hklt : k < 512).
  {
    destruct Hprod as [Hprod0 Hprod1].
    destruct Hk as [Hk0 Hk1].
    destruct (Z.eq_dec k 512) as [Heq512 | Hneq512]; [|lia].
    subst k. cbn in Hprod1. lia.
  }
  assert (Hknorm : unsigned_last_nbits (k + 1) 64 = k + 1).
  {
    apply unsigned_last_nbits_eq.
    split; [lia |].
    assert (Hpow10 : 513 < 2 ^ 10) by (change (513 < 1024); lia).
    assert (Hpowmono : 2 ^ 10 <= 2 ^ 64).
    { apply Z.pow_le_mono_r; lia. }
    lia.
  }
  assert (Houtnorm : unsigned_last_nbits (carry + out) 8 = out).
  {
    rewrite Hcarry0.
    apply unsigned_last_nbits_eq.
    change (0 <= out < 2 ^ 8).
    cbn. lia.
  }
  assert (Hpow_succ : 2 ^ (k + 1) = 2 * 2 ^ k).
  {
    replace (k + 1) with (Z.succ k) by lia.
    rewrite Z.pow_succ_r by lia.
    reflexivity.
  }
  assert (Hrpos : 0 < r).
  {
    destruct (Z.eq_dec r 0) as [Hr0 | Hr0]; [|lia].
    subst r.
    assert (Hpowmod : 2 ^ k mod modulus = 0).
    {
      rewrite Hcarry0 in Hmodu.
      replace (a * (0 + 0 * U256_MOD) + 1 * 2 ^ k)
        with (2 ^ k) in Hmodu by ring.
      exact Hmodu.
    }
    assert (Hdiv : (modulus | 2 ^ k)).
    { apply Z.mod_divide in Hpowmod; [exact Hpowmod | lia]. }
    pose proof
      (prime_power_prime modulus 2 k (proj1 Hk) modulus_prime prime_2 Hdiv)
      as Heq2.
    pose proof modulus_more_than_three_quarters as Hmodulus.
    assert (Hpow : 0 < 2 ^ 254) by (apply Z.pow_pos_nonneg; lia).
    lia.
  }
  assert (HN_lt_U : modulus < U256_MOD).
  { exact (proj2 modulus_bounds). }
  assert (HU_lt_2N : U256_MOD < 2 * modulus).
  {
    pose proof modulus_more_than_three_quarters as Hthree.
    assert (Hpowpos : 0 < 2 ^ 254) by
      (apply Z.pow_pos_nonneg; lia).
    replace U256_MOD with (4 * 2 ^ 254).
    - lia.
    - unfold U256_MOD.
      replace 256 with (2 + 254) by lia.
      rewrite Z.pow_add_r by lia.
      cbn. ring.
  }
  assert (Hnewmod :
    (a * (y + out * U256_MOD) + 2 ^ (k + 1)) mod modulus = 0).
  {
    replace (a * (y + out * U256_MOD) + 2 ^ (k + 1))
      with (2 * (a * (r + carry * U256_MOD) + 2 ^ k))
      by (rewrite Hcarry0, Hpow_succ; nia).
    rewrite Z.mul_mod by lia.
    replace (a * (r + carry * U256_MOD) + 2 ^ k)
      with (a * (r + carry * U256_MOD) + 1 * 2 ^ k) by ring.
    rewrite Hmodu.
    rewrite Z.mul_0_r.
    apply Zmod_0_l.
  }
  rewrite Hknorm, Houtnorm.
  unfold mont_inv_phase1_state.
  split; [exact Ha |].
  split; [lia |].
  split; [lia |].
  split; [exact Hy |].
  split; [rewrite Hbez'; split; lia |].
  split; [lia |].
  split; [lia |].
  split; [exact Hagcd |].
  split; [reflexivity |].
  split.
  - unfold mont_inv_phase1_progress.
    split; [lia |].
    split; [rewrite Hpow_succ; lia |].
    split.
    + assert (HN256 : modulus < 2 ^ 256).
      { change (modulus < U256_MOD). exact HN_lt_U. }
      assert (Hpowmono : 2 ^ 256 <= 2 ^ (k + 1)).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hbez'. lia.
    + split; [intros Hzero; contradiction |].
      intros Heq. discriminate.
  - split.
    + unfold mont_inv_phase1_overflow_reach.
      split; [rewrite Hbez'; ring |].
      intros Hzero. contradiction.
    + split.
      * replace
          (a * (y + out * U256_MOD) + 1 * 2 ^ (k + 1))
          with (a * (y + out * U256_MOD) + 2 ^ (k + 1)) by ring.
        exact Hnewmod.
      * split.
        -- rewrite Hbez'.
           replace (a * modulus - 0 * 2 ^ (k + 1))
             with (a * modulus) by ring.
           apply Z.mod_mul. lia.
        -- intros _. split; [reflexivity |].
           unfold mont_inv_phase1_exit_carry.
           split; [exact Ha |].
           split; [exact Hy |].
           split; [exact Hout |].
           split; [exact Hagcd |].
           split; [lia |].
           split; [exact Hnewmod |].
           split.
           ++ intros Hout0. lia.
           ++ intros Hout1. lia.
Qed.

Lemma mont_inv_phase1_sub_halve_v :
  forall a u v r s k carry y out,
    mont_inv_phase1_state a u v r s k carry ->
    v <> 0 ->
    Z.land u 1 = 1 ->
    Z.land v 1 = 1 ->
    u <= v ->
    u256_shl_result r y out ->
    mont_inv_phase1_state
      a u ((v - u) / 2) y (r + s)
      (unsigned_last_nbits (k + 1) 64)
      (unsigned_last_nbits (carry + out) 8).
Proof.
  intros a u v r s k carry y out Hstate Hv0 Huodd Hvodd Huv Hshift.
  destruct (Z.eq_dec u v) as [Heq | Hneq].
  - subst v.
    apply mont_inv_phase1_sub_halve_v_equal; assumption.
  - apply mont_inv_phase1_sub_halve_v_strict; try assumption; lia.
Qed.


End BinaryAlmostInverse.
