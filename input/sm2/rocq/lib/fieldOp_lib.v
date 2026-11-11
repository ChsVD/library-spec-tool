Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.setoid_ring.Ring.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.Applications_human.sm2.lib
  Require Export basicOp_lib.
From SimpleC.EE.Applications_human.sm2.lib
  Require Import montgomery.
From SimpleC.EE.Applications_human.sm2.lib
  Require Import almost_inverse sm2_primality.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Import Snaive_C_Rules.
Local Open Scope sac.

(** * SM2 Montgomery operations *)

Lemma unscale_inverse_product_mod_one :
  forall modulus a scaled result quotient1 quotient2,
    1 < modulus ->
    Z.gcd modulus U256_MOD = 1 ->
    a * scaled = U256_MOD + quotient1 * modulus ->
    result * U256_MOD = scaled + quotient2 * modulus ->
    (a * result) mod modulus = 1.
Proof.
  intros modulus a scaled result quotient1 quotient2
    Hmodulus Hgcd Hscaled Hunscale.
  assert (Hcoprime : rel_prime modulus U256_MOD).
  {
    apply (proj1 (Zgcd_1_rel_prime _ _)).
    exact Hgcd.
  }
  assert (Hproduct :
    (modulus | (a * result - 1) * U256_MOD)).
  {
    exists (quotient1 + a * quotient2).
    replace ((a * result - 1) * U256_MOD) with
      (a * (result * U256_MOD) - U256_MOD) by ring.
    rewrite Hunscale.
    replace
      (a * (scaled + quotient2 * modulus) - U256_MOD)
      with
      ((a * scaled - U256_MOD) +
       a * quotient2 * modulus) by ring.
    rewrite Hscaled.
    ring.
  }
  assert (Hdivides : (modulus | a * result - 1)).
  {
    apply (Gauss modulus U256_MOD (a * result - 1));
      [| exact Hcoprime].
    rewrite Z.mul_comm.
    exact Hproduct.
  }
  destruct Hdivides as [quotient Hquotient].
  symmetry.
  apply (Zmod_unique (a * result) modulus quotient 1).
  - lia.
  - rewrite Z.mul_comm.
    lia.
Qed.

Lemma mul_sub_modulus_mod :
  forall modulus multiplier value offset,
    (multiplier * (value - modulus) + offset) mod modulus =
    (multiplier * value + offset) mod modulus.
Proof.
  intros modulus multiplier value offset.
  replace (multiplier * (value - modulus) + offset) with
    ((multiplier * value + offset) + (- multiplier) * modulus) by ring.
  apply Z_mod_plus_full.
Qed.

Lemma sm2p_montgomery_radix_coprime :
  Z.gcd U256_MOD SM2_P_Z = 1.
Proof.
  apply Zgcd_1_rel_prime.
  apply rel_prime_sym.
  exact sm2_p_radix_rel_prime.
Qed.

Lemma sm2p_montgomery_radix_inverse :
  exists radix_inverse,
    (U256_MOD * radix_inverse - 1) mod SM2_P_Z = 0.
Proof.
  pose proof sm2p_montgomery_radix_coprime as Hgcd.
  apply Zgcd_1_rel_prime in Hgcd.
  destruct (rel_prime_bezout U256_MOD SM2_P_Z Hgcd)
    as [radix_inverse modulus_coefficient Hbezout].
  exists radix_inverse.
  apply Z.mod_divide.
  - pose proof sm2_p_montgomery_bounds. lia.
  - exists (-modulus_coefficient).
    nia.
Qed.

Lemma sm2p_montgomery_mul_from_equation :
  forall x y result quotient,
    0 <= result < SM2_P_Z ->
    result * U256_MOD = mont_p x * mont_p y + quotient * SM2_P_Z ->
    result = mont_p (x * y).
Proof.
  intros x y result quotient Hresult Hequation.
  destruct sm2p_montgomery_radix_inverse as [radix_inverse Hinverse].
  unfold mont_p.
  eapply Montgomery.montgomery_multiplication
    with (R_inv := radix_inverse); try eassumption.
  - pose proof sm2_p_montgomery_bounds. lia.
  - apply Montgomery.equation_implies_congruence with (k := quotient).
    + pose proof sm2_p_montgomery_bounds. lia.
    + exact Hequation.
Qed.

Lemma sm2p_regular_to_montgomery_from_equation :
  forall x result quotient,
    0 <= result < SM2_P_Z ->
    result * U256_MOD = x * SM2_H_Z + quotient * SM2_P_Z ->
    result = mont_p x.
Proof.
  intros x result quotient Hresult Hequation.
  destruct sm2p_montgomery_radix_inverse as [radix_inverse Hinverse].
  rewrite sm2_h_is_r2 in Hequation.
  unfold mont_p.
  eapply Montgomery.regular_to_montgomery
    with (R_inv := radix_inverse); try eassumption.
  - pose proof sm2_p_montgomery_bounds. lia.
  - apply Montgomery.equation_implies_congruence with (k := quotient).
    + pose proof sm2_p_montgomery_bounds. lia.
    + exact Hequation.
Qed.

Lemma sm2p_montgomery_to_regular_from_equation :
  forall x result quotient,
    0 <= x < SM2_P_Z ->
    0 <= result < SM2_P_Z ->
    result * U256_MOD = mont_p x + quotient * SM2_P_Z ->
    result = x.
Proof.
  intros x result quotient Hx Hresult Hequation.
  destruct sm2p_montgomery_radix_inverse as [radix_inverse Hinverse].
  unfold mont_p in *.
  eapply Montgomery.montgomery_to_regular
    with (R_inv := radix_inverse); try eassumption.
  - pose proof sm2_p_montgomery_bounds. lia.
  - apply Montgomery.equation_implies_congruence with (k := quotient).
    + pose proof sm2_p_montgomery_bounds. lia.
    + exact Hequation.
Qed.

(** * Modulus facts used by binary inversion *)

Lemma sm2_p_more_than_three_quarters :
  3 * 2 ^ 254 < SM2_P_Z.
Proof. vm_compute; reflexivity. Qed.

Lemma sm2_p_more_than_half :
  U256_MOD < 2 * SM2_P_Z.
Proof. exact (proj2 sm2_p_montgomery_bounds). Qed.

Lemma sm2_n_more_than_three_quarters :
  3 * 2 ^ 254 < SM2_N_Z.
Proof. vm_compute; reflexivity. Qed.

Lemma land_one_eq_mod_two :
  forall x, Z.land x 1 = x mod 2.
Proof.
  exact
    SimpleC.EE.Applications_human.sm2.lib.almost_inverse.land_one_eq_mod_two.
Qed.

Definition sm2n_mont_inv_phase1_exit_carry
  (a r k carry : Z) : Prop :=
  0 < a < SM2_N_Z /\
  0 <= r < U256_MOD /\
  0 <= carry <= 1 /\
  Z.gcd a SM2_N_Z = 1 /\
  256 <= k <= 512 /\
  (a * (r + carry * U256_MOD) + 2 ^ k) mod SM2_N_Z = 0 /\
  (carry = 0 -> 0 < r < 2 * SM2_N_Z) /\
  (carry = 1 -> r < SM2_N_Z).

Local Definition sm2n_mont_inv_phase1_progress
  (u v r s k : Z) : Prop :=
  0 < u /\
  0 <= r <= 2 ^ k /\
  0 <= s <= 2 ^ k /\
  (v <> 0 -> 0 < u * v < 2 ^ (512 - k)) /\
  (u = v -> 255 <= k).

Local Definition sm2n_mont_inv_phase1_overflow_reach
  (u v r s carry : Z) : Prop :=
  r * v + s * u = SM2_N_Z /\
  (v <> 0 ->
     carry = 0 /\
     r + s < U256_MOD /\
     ((Z.land u 1 = 0 \/
       (Z.land u 1 = 1 /\ Z.land v 1 = 1 /\ u > v)) ->
        2 * s < U256_MOD) /\
     ((Z.land u 1 = 1 /\
       (Z.land v 1 = 0 \/ (Z.land v 1 = 1 /\ u < v))) ->
        2 * r < U256_MOD)).

Definition sm2n_mont_inv_phase1_state
  (a u v r s k carry : Z) : Prop :=
  0 < a < SM2_N_Z /\
  0 <= u < U256_MOD /\
  0 <= v < U256_MOD /\
  0 <= r < U256_MOD /\
  0 <= s < U256_MOD /\
  0 <= k <= 512 /\
  0 <= carry <= k /\
  Z.gcd a SM2_N_Z = 1 /\
  Z.gcd u v = 1 /\
  sm2n_mont_inv_phase1_progress u v r s k /\
  sm2n_mont_inv_phase1_overflow_reach u v r s carry /\
  (a * (r + carry * U256_MOD) + u * 2 ^ k) mod SM2_N_Z = 0 /\
  (a * s - v * 2 ^ k) mod SM2_N_Z = 0 /\
  (v = 0 -> u = 1 /\ sm2n_mont_inv_phase1_exit_carry a r k carry).

Definition sm2n_mont_inv_post_loop_residue (a r k : Z) : Prop :=
  0 < a < SM2_N_Z /\
  0 < r < 2 * SM2_N_Z /\
  Z.gcd a SM2_N_Z = 1 /\
  256 <= k <= 512 /\
  (a * r + 2 ^ k) mod SM2_N_Z = 0.

Definition sm2n_mont_inv_post_loop_norm (a r k : Z) : Prop :=
  0 < a < SM2_N_Z /\
  0 < r < SM2_N_Z /\
  Z.gcd a SM2_N_Z = 1 /\
  256 <= k <= 512 /\
  (a * r + 2 ^ k) mod SM2_N_Z = 0.

Definition sm2n_mont_inv_phase1_result (a r k : Z) : Prop :=
  0 < a < SM2_N_Z /\
  0 <= r < SM2_N_Z /\
  Z.gcd a SM2_N_Z = 1 /\
  256 <= k <= 512 /\
  (a * r) mod SM2_N_Z = (2 ^ k) mod SM2_N_Z.

Definition sm2n_mont_inv_phase2_index (k0 i k : Z) : Prop :=
  256 <= k0 <= 512 /\
  k0 <> 256 /\
  i = (512 - k0) / 64 /\
  k = (512 - k0) mod 64.

Definition sm2p_mont_inv_phase1_exit_carry
  (a r k carry : Z) : Prop :=
  0 < a < SM2_P_Z /\
  0 <= r < U256_MOD /\
  0 <= carry <= 1 /\
  Z.gcd a SM2_P_Z = 1 /\
  256 <= k <= 512 /\
  (a * (r + carry * U256_MOD) + 2 ^ k) mod SM2_P_Z = 0 /\
  (carry = 0 -> 0 < r < 2 * SM2_P_Z) /\
  (carry = 1 -> r < SM2_P_Z).

Local Definition sm2p_mont_inv_phase1_progress
  (u v r s k : Z) : Prop :=
  0 < u /\
  0 <= r <= 2 ^ k /\
  0 <= s <= 2 ^ k /\
  (v <> 0 -> 0 < u * v < 2 ^ (512 - k)) /\
  (u = v -> 255 <= k).

Local Definition sm2p_mont_inv_phase1_overflow_reach
  (u v r s carry : Z) : Prop :=
  r * v + s * u = SM2_P_Z /\
  (v <> 0 ->
     carry = 0 /\
     r + s < U256_MOD /\
     ((Z.land u 1 = 0 \/
       (Z.land u 1 = 1 /\ Z.land v 1 = 1 /\ u > v)) ->
        2 * s < U256_MOD) /\
     ((Z.land u 1 = 1 /\
       (Z.land v 1 = 0 \/ (Z.land v 1 = 1 /\ u < v))) ->
        2 * r < U256_MOD)).

Definition sm2p_mont_inv_phase1_state
  (a u v r s k carry : Z) : Prop :=
  0 < a < SM2_P_Z /\
  0 <= u < U256_MOD /\
  0 <= v < U256_MOD /\
  0 <= r < U256_MOD /\
  0 <= s < U256_MOD /\
  0 <= k <= 512 /\
  0 <= carry <= k /\
  Z.gcd a SM2_P_Z = 1 /\
  Z.gcd u v = 1 /\
  sm2p_mont_inv_phase1_progress u v r s k /\
  sm2p_mont_inv_phase1_overflow_reach u v r s carry /\
  (a * (r + carry * U256_MOD) + u * 2 ^ k) mod SM2_P_Z = 0 /\
  (a * s - v * 2 ^ k) mod SM2_P_Z = 0 /\
  (v = 0 -> u = 1 /\ sm2p_mont_inv_phase1_exit_carry a r k carry).

Definition sm2p_mont_inv_post_loop_residue (a r k : Z) : Prop :=
  0 < a < SM2_P_Z /\
  0 < r < 2 * SM2_P_Z /\
  Z.gcd a SM2_P_Z = 1 /\
  256 <= k <= 512 /\
  (a * r + 2 ^ k) mod SM2_P_Z = 0.

Definition sm2p_mont_inv_post_loop_norm (a r k : Z) : Prop :=
  0 < a < SM2_P_Z /\
  0 < r < SM2_P_Z /\
  Z.gcd a SM2_P_Z = 1 /\
  256 <= k <= 512 /\
  (a * r + 2 ^ k) mod SM2_P_Z = 0.

Definition sm2p_mont_inv_phase1_result (a r k : Z) : Prop :=
  0 < a < SM2_P_Z /\
  0 <= r < SM2_P_Z /\
  Z.gcd a SM2_P_Z = 1 /\
  256 <= k <= 512 /\
  (a * r) mod SM2_P_Z = (2 ^ k) mod SM2_P_Z.

Definition sm2p_mont_inv_phase2_index (k0 i k : Z) : Prop :=
  256 <= k0 <= 512 /\
  k0 <> 256 /\
  i = (512 - k0) / 64 /\
  k = (512 - k0) mod 64.

(** * Binary inversion modulo the group order *)

Lemma sm2n_pow2_mod_nonzero :
  forall k, 0 <= k -> 2 ^ k mod SM2_N_Z <> 0.
Proof.
  apply (pow2_mod_nonzero SM2_N_Z).
  - exact sm2_n_bounds.
  - exact sm2_n_more_than_three_quarters.
  - exact sm2_n_prime.
Qed.

Lemma sm2n_residue_sub_modulus_norm :
  forall a r s k,
    sm2n_mont_inv_post_loop_residue a r k ->
    SM2_N_Z <= r ->
    s = r - SM2_N_Z ->
    sm2n_mont_inv_post_loop_norm a s k.
Proof.
  intros a r s k Hres Hge Hs.
  change (mont_inv_post_loop_residue SM2_N_Z a r k) in Hres.
  change (mont_inv_post_loop_norm SM2_N_Z a s k).
  eapply (residue_sub_modulus_norm SM2_N_Z).
  - exact sm2_n_bounds.
  - exact sm2_n_more_than_three_quarters.
  - exact sm2_n_prime.
  - exact Hres.
  - exact Hge.
  - exact Hs.
Qed.

Lemma sm2n_residue_below_modulus_norm :
  forall a r k,
    sm2n_mont_inv_post_loop_residue a r k ->
    r < SM2_N_Z ->
    sm2n_mont_inv_post_loop_norm a r k.
Proof.
  intros a r k Hres Hlt.
  change (mont_inv_post_loop_residue SM2_N_Z a r k) in Hres.
  change (mont_inv_post_loop_norm SM2_N_Z a r k).
  eapply (residue_below_modulus_norm SM2_N_Z); eassumption.
Qed.

Lemma sm2n_norm_complement_result :
  forall a r s k,
    sm2n_mont_inv_post_loop_norm a r k ->
    s = SM2_N_Z - r ->
    sm2n_mont_inv_phase1_result a s k.
Proof.
  intros a r s k Hnorm Hs.
  change (mont_inv_post_loop_norm SM2_N_Z a r k) in Hnorm.
  change (mont_inv_phase1_result SM2_N_Z a s k).
  eapply (norm_complement_result SM2_N_Z).
  - exact sm2_n_bounds.
  - exact Hnorm.
  - exact Hs.
Qed.

Lemma sm2n_scaled_inverse_is_montgomery :
  forall a z quotient,
    0 <= a < SM2_N_Z ->
    a <> 0 ->
    0 <= z < SM2_N_Z ->
    a * z = U256_MOD + quotient * SM2_N_Z ->
    exists a_inv,
      0 <= a_inv < SM2_N_Z /\
      (a * a_inv) mod SM2_N_Z = 1 /\
      z = mont_n a_inv.
Proof.
  intros a z quotient Ha Ha0 Hz Hequation.
  change
    (exists a_inv,
      0 <= a_inv < SM2_N_Z /\
      (a * a_inv) mod SM2_N_Z = 1 /\
      z = Montgomery.mont SM2_N_Z U256_MOD a_inv).
  eapply (scaled_inverse_is_montgomery SM2_N_Z).
  - exact sm2_n_bounds.
  - exact sm2_n_more_than_three_quarters.
  - exact sm2_n_prime.
  - exact Ha.
  - exact Ha0.
  - exact Hz.
  - exact Hequation.
Qed.

Lemma sm2n_mont_inv_phase2_index_bounds :
  forall k0,
    256 <= k0 <= 512 ->
    k0 <> 256 ->
    sm2n_mont_inv_phase2_index
      k0 ((512 - k0) / 64) ((512 - k0) mod 64) /\
    0 <= (512 - k0) / 64 < 4 /\
    0 <= (512 - k0) mod 64 < 64.
Proof. exact mont_inv_phase2_index_bounds. Qed.

Lemma sm2n_mont_inv_phase2_one_hot_value :
  forall k0 i k,
    sm2n_mont_inv_phase2_index k0 i k ->
    0 <= i < 4 ->
    0 <= k < 64 ->
    0 <= 2 ^ (512 - k0) < SM2_N_Z /\
    u64_list_value
      (replace_Znth i
        (unsigned_last_nbits (Z.shiftl 1 k) 64)
        (0 :: 0 :: 0 :: 0 :: nil)) =
      2 ^ (512 - k0).
Proof.
  intros k0 i k Hindex Hi Hk.
  change (mont_inv_phase2_index k0 i k) in Hindex.
  eapply (mont_inv_phase2_one_hot_value SM2_N_Z).
  - exact sm2_n_more_than_three_quarters.
  - exact Hindex.
  - exact Hi.
  - exact Hk.
Qed.

Lemma sm2n_mont_inv_phase2_product_equation :
  forall a r5 k0 t out kmul,
    0 <= out < SM2_N_Z ->
    sm2n_mont_inv_phase1_result a r5 k0 ->
    t = 2 ^ (512 - k0) ->
    out * U256_MOD = r5 * t + kmul * SM2_N_Z ->
    exists kout, a * out = U256_MOD + kout * SM2_N_Z.
Proof.
  intros a r5 k0 t out kmul Hout Hphase Ht Hproduct.
  change (mont_inv_phase1_result SM2_N_Z a r5 k0) in Hphase.
  eapply (mont_inv_phase2_product_equation SM2_N_Z).
  - exact sm2_n_bounds.
  - exact (proj2 sm2n_montgomery_parameters_valid).
  - exact Hout.
  - exact Hphase.
  - exact Ht.
  - exact Hproduct.
Qed.

Lemma sm2n_mont_inv_phase1_k256_equation :
  forall a r,
    sm2n_mont_inv_phase1_result a r 256 ->
    exists kout, a * r = U256_MOD + kout * SM2_N_Z.
Proof.
  intros a r Hphase.
  change (mont_inv_phase1_result SM2_N_Z a r 256) in Hphase.
  eapply (mont_inv_phase1_k256_equation SM2_N_Z).
  - exact sm2_n_bounds.
  - exact Hphase.
Qed.

Lemma sm2n_mont_inv_phase1_init :
  forall a,
    0 < a < SM2_N_Z ->
    Z.gcd a SM2_N_Z = 1 ->
    sm2n_mont_inv_phase1_state a SM2_N_Z a 0 1 0 0.
Proof.
  intros a Ha Hgcd.
  change (mont_inv_phase1_state SM2_N_Z a SM2_N_Z a 0 1 0 0).
  eapply (mont_inv_phase1_init SM2_N_Z).
  - exact sm2_n_bounds.
  - exact Ha.
  - exact Hgcd.
Qed.

Lemma sm2n_mont_inv_phase1_init_nonzero :
  forall a,
    0 <= a < SM2_N_Z ->
    a <> 0 ->
    sm2n_mont_inv_phase1_state a SM2_N_Z a 0 1 0 0.
Proof.
  intros a Ha Ha0.
  change (mont_inv_phase1_state SM2_N_Z a SM2_N_Z a 0 1 0 0).
  eapply (mont_inv_phase1_init_nonzero SM2_N_Z).
  - exact sm2_n_bounds.
  - exact sm2_n_prime.
  - exact Ha.
  - exact Ha0.
Qed.

Lemma sm2n_mont_inv_phase1_halve_u :
  forall a u v r s k carry y,
    sm2n_mont_inv_phase1_state a u v r s k carry ->
    v <> 0 ->
    Z.land u 1 = 0 ->
    y = 2 * s ->
    sm2n_mont_inv_phase1_state
      a (u / 2) v r y (unsigned_last_nbits (k + 1) 64) carry.
Proof.
  intros a u v r s k carry y Hstate Hv0 Heven Hy.
  change (mont_inv_phase1_state SM2_N_Z a u v r s k carry) in Hstate.
  change
    (mont_inv_phase1_state SM2_N_Z a (u / 2) v r y
      (unsigned_last_nbits (k + 1) 64) carry).
  eapply (mont_inv_phase1_halve_u SM2_N_Z).
  - exact sm2_n_bounds.
  - exact sm2_n_more_than_three_quarters.
  - exact Hstate.
  - exact Hv0.
  - exact Heven.
  - exact Hy.
Qed.

Lemma sm2n_mont_inv_phase1_halve_v :
  forall a u v r s k carry y,
    sm2n_mont_inv_phase1_state a u v r s k carry ->
    v <> 0 ->
    Z.land u 1 = 1 ->
    Z.land v 1 = 0 ->
    y = 2 * r ->
    sm2n_mont_inv_phase1_state
      a u (v / 2) y s (unsigned_last_nbits (k + 1) 64) carry.
Proof.
  intros a u v r s k carry y Hstate Hv0 Huodd Hveven Hy.
  change (mont_inv_phase1_state SM2_N_Z a u v r s k carry) in Hstate.
  change
    (mont_inv_phase1_state SM2_N_Z a u (v / 2) y s
      (unsigned_last_nbits (k + 1) 64) carry).
  eapply (mont_inv_phase1_halve_v SM2_N_Z).
  - exact sm2_n_bounds.
  - exact sm2_n_more_than_three_quarters.
  - exact Hstate.
  - exact Hv0.
  - exact Huodd.
  - exact Hveven.
  - exact Hy.
Qed.

Lemma sm2n_mont_inv_phase1_sub_halve_u :
  forall a u v r s k carry,
    sm2n_mont_inv_phase1_state a u v r s k carry ->
    v <> 0 ->
    Z.land u 1 = 1 ->
    Z.land v 1 = 1 ->
    u > v ->
    sm2n_mont_inv_phase1_state
      a ((u - v) / 2) v (r + s) (2 * s)
      (unsigned_last_nbits (k + 1) 64) carry.
Proof.
  intros a u v r s k carry Hstate Hv0 Huodd Hvodd Huv.
  change (mont_inv_phase1_state SM2_N_Z a u v r s k carry) in Hstate.
  change
    (mont_inv_phase1_state SM2_N_Z a ((u - v) / 2) v (r + s) (2 * s)
      (unsigned_last_nbits (k + 1) 64) carry).
  eapply (mont_inv_phase1_sub_halve_u SM2_N_Z).
  - exact sm2_n_bounds.
  - exact sm2_n_more_than_three_quarters.
  - exact Hstate.
  - exact Hv0.
  - exact Huodd.
  - exact Hvodd.
  - exact Huv.
Qed.

Lemma sm2n_mont_inv_phase1_sub_halve_v :
  forall a u v r s k carry y out,
    sm2n_mont_inv_phase1_state a u v r s k carry ->
    v <> 0 ->
    Z.land u 1 = 1 ->
    Z.land v 1 = 1 ->
    u <= v ->
    u256_shl_result r y out ->
    sm2n_mont_inv_phase1_state
      a u ((v - u) / 2) y (r + s)
      (unsigned_last_nbits (k + 1) 64)
      (unsigned_last_nbits (carry + out) 8).
Proof.
  intros a u v r s k carry y out Hstate Hv0 Huodd Hvodd Huv Hshift.
  change (mont_inv_phase1_state SM2_N_Z a u v r s k carry) in Hstate.
  change
    (mont_inv_phase1_state SM2_N_Z a u ((v - u) / 2) y (r + s)
      (unsigned_last_nbits (k + 1) 64)
      (unsigned_last_nbits (carry + out) 8)).
  eapply (mont_inv_phase1_sub_halve_v SM2_N_Z).
  - exact sm2_n_bounds.
  - exact sm2_n_more_than_three_quarters.
  - exact sm2_n_prime.
  - exact Hstate.
  - exact Hv0.
  - exact Huodd.
  - exact Hvodd.
  - exact Huv.
  - exact Hshift.
Qed.

(** * Binary inversion modulo the prime field *)

Lemma sm2p_pow2_mod_nonzero :
  forall k,
    0 <= k ->
    2 ^ k mod SM2_P_Z <> 0.
Proof.
  apply (pow2_mod_nonzero SM2_P_Z).
  - exact (proj1 sm2_p_montgomery_bounds).
  - exact sm2_p_more_than_three_quarters.
  - exact sm2_p_prime.
Qed.

Lemma sm2p_residue_sub_modulus_norm :
  forall a r s k,
    sm2p_mont_inv_post_loop_residue a r k ->
    SM2_P_Z <= r ->
    s = r - SM2_P_Z ->
    sm2p_mont_inv_post_loop_norm a s k.
Proof.
  intros a r s k Hres Hge Hs.
  change (mont_inv_post_loop_residue SM2_P_Z a r k) in Hres.
  change (mont_inv_post_loop_norm SM2_P_Z a s k).
  eapply (residue_sub_modulus_norm SM2_P_Z).
  - exact (proj1 sm2_p_montgomery_bounds).
  - exact sm2_p_more_than_three_quarters.
  - exact sm2_p_prime.
  - exact Hres.
  - exact Hge.
  - exact Hs.
Qed.

Lemma sm2p_residue_below_modulus_norm :
  forall a r k,
    sm2p_mont_inv_post_loop_residue a r k ->
    r < SM2_P_Z ->
    sm2p_mont_inv_post_loop_norm a r k.
Proof.
  intros a r k Hres Hlt.
  change (mont_inv_post_loop_residue SM2_P_Z a r k) in Hres.
  change (mont_inv_post_loop_norm SM2_P_Z a r k).
  eapply (residue_below_modulus_norm SM2_P_Z); eassumption.
Qed.

Lemma sm2p_norm_complement_result :
  forall a r s k,
    sm2p_mont_inv_post_loop_norm a r k ->
    s = SM2_P_Z - r ->
    sm2p_mont_inv_phase1_result a s k.
Proof.
  intros a r s k Hnorm Hs.
  change (mont_inv_post_loop_norm SM2_P_Z a r k) in Hnorm.
  change (mont_inv_phase1_result SM2_P_Z a s k).
  eapply (norm_complement_result SM2_P_Z).
  - exact (proj1 sm2_p_montgomery_bounds).
  - exact Hnorm.
  - exact Hs.
Qed.

Lemma sm2p_scaled_inverse_is_montgomery :
  forall a z quotient,
    0 <= a < SM2_P_Z ->
    a <> 0 ->
    0 <= z < SM2_P_Z ->
    a * z = U256_MOD + quotient * SM2_P_Z ->
    exists a_inv,
      0 <= a_inv < SM2_P_Z /\
      (a * a_inv) mod SM2_P_Z = 1 /\
      z = mont_p a_inv.
Proof.
  intros a z quotient Ha Ha0 Hz Hequation.
  change
    (exists a_inv,
      0 <= a_inv < SM2_P_Z /\
      (a * a_inv) mod SM2_P_Z = 1 /\
      z = Montgomery.mont SM2_P_Z U256_MOD a_inv).
  eapply (scaled_inverse_is_montgomery SM2_P_Z).
  - exact (proj1 sm2_p_montgomery_bounds).
  - exact sm2_p_more_than_three_quarters.
  - exact sm2_p_prime.
  - exact Ha.
  - exact Ha0.
  - exact Hz.
  - exact Hequation.
Qed.

Lemma sm2p_mont_inv_phase2_index_bounds :
  forall k0,
    256 <= k0 <= 512 ->
    k0 <> 256 ->
    sm2p_mont_inv_phase2_index
      k0 ((512 - k0) / 64) ((512 - k0) mod 64) /\
    0 <= (512 - k0) / 64 < 4 /\
    0 <= (512 - k0) mod 64 < 64.
Proof. exact mont_inv_phase2_index_bounds. Qed.

Lemma sm2p_mont_inv_phase2_one_hot_value :
  forall k0 i k,
    sm2p_mont_inv_phase2_index k0 i k ->
    0 <= i < 4 ->
    0 <= k < 64 ->
    0 <= 2 ^ (512 - k0) < SM2_P_Z /\
    u64_list_value
      (replace_Znth i
        (unsigned_last_nbits (Z.shiftl 1 k) 64)
        (0 :: 0 :: 0 :: 0 :: nil)) =
      2 ^ (512 - k0).
Proof.
  intros k0 i k Hindex Hi Hk.
  change (mont_inv_phase2_index k0 i k) in Hindex.
  eapply (mont_inv_phase2_one_hot_value SM2_P_Z).
  - exact sm2_p_more_than_three_quarters.
  - exact Hindex.
  - exact Hi.
  - exact Hk.
Qed.

Lemma sm2p_mont_inv_phase2_product_equation :
  forall a r5 k0 t out kmul,
    0 <= out < SM2_P_Z ->
    sm2p_mont_inv_phase1_result a r5 k0 ->
    t = 2 ^ (512 - k0) ->
    out * U256_MOD = r5 * t + kmul * SM2_P_Z ->
    exists kout,
      a * out = U256_MOD + kout * SM2_P_Z.
Proof.
  intros a r5 k0 t out kmul Hout Hphase Ht Hproduct.
  change (mont_inv_phase1_result SM2_P_Z a r5 k0) in Hphase.
  eapply (mont_inv_phase2_product_equation SM2_P_Z).
  - exact (proj1 sm2_p_montgomery_bounds).
  - rewrite Z.gcd_comm.
    exact sm2p_montgomery_radix_coprime.
  - exact Hout.
  - exact Hphase.
  - exact Ht.
  - exact Hproduct.
Qed.

Lemma sm2p_mont_inv_phase1_k256_equation :
  forall a r,
    sm2p_mont_inv_phase1_result a r 256 ->
    exists kout,
      a * r = U256_MOD + kout * SM2_P_Z.
Proof.
  intros a r Hphase.
  change (mont_inv_phase1_result SM2_P_Z a r 256) in Hphase.
  eapply (mont_inv_phase1_k256_equation SM2_P_Z).
  - exact (proj1 sm2_p_montgomery_bounds).
  - exact Hphase.
Qed.

Lemma sm2p_mont_inv_phase1_init :
  forall a,
    0 < a < SM2_P_Z ->
    Z.gcd a SM2_P_Z = 1 ->
    sm2p_mont_inv_phase1_state a SM2_P_Z a 0 1 0 0.
Proof.
  intros a Ha Hgcd.
  change (mont_inv_phase1_state SM2_P_Z a SM2_P_Z a 0 1 0 0).
  eapply (mont_inv_phase1_init SM2_P_Z).
  - exact (proj1 sm2_p_montgomery_bounds).
  - exact Ha.
  - exact Hgcd.
Qed.

Lemma sm2p_mont_inv_phase1_init_nonzero :
  forall a,
    0 <= a < SM2_P_Z ->
    a <> 0 ->
    sm2p_mont_inv_phase1_state a SM2_P_Z a 0 1 0 0.
Proof.
  intros a Ha Ha0.
  change (mont_inv_phase1_state SM2_P_Z a SM2_P_Z a 0 1 0 0).
  eapply (mont_inv_phase1_init_nonzero SM2_P_Z).
  - exact (proj1 sm2_p_montgomery_bounds).
  - exact sm2_p_prime.
  - exact Ha.
  - exact Ha0.
Qed.

Lemma sm2p_mont_inv_phase1_halve_u :
  forall a u v r s k carry y,
    sm2p_mont_inv_phase1_state a u v r s k carry ->
    v <> 0 ->
    Z.land u 1 = 0 ->
    y = 2 * s ->
    sm2p_mont_inv_phase1_state
      a (u / 2) v r y (unsigned_last_nbits (k + 1) 64) carry.
Proof.
  intros a u v r s k carry y Hstate Hv0 Heven Hy.
  change (mont_inv_phase1_state SM2_P_Z a u v r s k carry) in Hstate.
  change
    (mont_inv_phase1_state SM2_P_Z a (u / 2) v r y
      (unsigned_last_nbits (k + 1) 64) carry).
  eapply (mont_inv_phase1_halve_u SM2_P_Z).
  - exact (proj1 sm2_p_montgomery_bounds).
  - exact sm2_p_more_than_three_quarters.
  - exact Hstate.
  - exact Hv0.
  - exact Heven.
  - exact Hy.
Qed.

Lemma sm2p_mont_inv_phase1_halve_v :
  forall a u v r s k carry y,
    sm2p_mont_inv_phase1_state a u v r s k carry ->
    v <> 0 ->
    Z.land u 1 = 1 ->
    Z.land v 1 = 0 ->
    y = 2 * r ->
    sm2p_mont_inv_phase1_state
      a u (v / 2) y s (unsigned_last_nbits (k + 1) 64) carry.
Proof.
  intros a u v r s k carry y Hstate Hv0 Huodd Hveven Hy.
  change (mont_inv_phase1_state SM2_P_Z a u v r s k carry) in Hstate.
  change
    (mont_inv_phase1_state SM2_P_Z a u (v / 2) y s
      (unsigned_last_nbits (k + 1) 64) carry).
  eapply (mont_inv_phase1_halve_v SM2_P_Z).
  - exact (proj1 sm2_p_montgomery_bounds).
  - exact sm2_p_more_than_three_quarters.
  - exact Hstate.
  - exact Hv0.
  - exact Huodd.
  - exact Hveven.
  - exact Hy.
Qed.

Lemma sm2p_mont_inv_phase1_sub_halve_u :
  forall a u v r s k carry,
    sm2p_mont_inv_phase1_state a u v r s k carry ->
    v <> 0 ->
    Z.land u 1 = 1 ->
    Z.land v 1 = 1 ->
    u > v ->
    sm2p_mont_inv_phase1_state
      a ((u - v) / 2) v (r + s) (2 * s)
      (unsigned_last_nbits (k + 1) 64) carry.
Proof.
  intros a u v r s k carry Hstate Hv0 Huodd Hvodd Huv.
  change (mont_inv_phase1_state SM2_P_Z a u v r s k carry) in Hstate.
  change
    (mont_inv_phase1_state SM2_P_Z a ((u - v) / 2) v (r + s) (2 * s)
      (unsigned_last_nbits (k + 1) 64) carry).
  eapply (mont_inv_phase1_sub_halve_u SM2_P_Z).
  - exact (proj1 sm2_p_montgomery_bounds).
  - exact sm2_p_more_than_three_quarters.
  - exact Hstate.
  - exact Hv0.
  - exact Huodd.
  - exact Hvodd.
  - exact Huv.
Qed.

Lemma sm2p_mont_inv_phase1_sub_halve_v :
  forall a u v r s k carry y out,
    sm2p_mont_inv_phase1_state a u v r s k carry ->
    v <> 0 ->
    Z.land u 1 = 1 ->
    Z.land v 1 = 1 ->
    u <= v ->
    u256_shl_result r y out ->
    sm2p_mont_inv_phase1_state
      a u ((v - u) / 2) y (r + s)
      (unsigned_last_nbits (k + 1) 64)
      (unsigned_last_nbits (carry + out) 8).
Proof.
  intros a u v r s k carry y out Hstate Hv0 Huodd Hvodd Huv Hshift.
  change (mont_inv_phase1_state SM2_P_Z a u v r s k carry) in Hstate.
  change
    (mont_inv_phase1_state SM2_P_Z a u ((v - u) / 2) y (r + s)
      (unsigned_last_nbits (k + 1) 64)
      (unsigned_last_nbits (carry + out) 8)).
  eapply (mont_inv_phase1_sub_halve_v SM2_P_Z).
  - exact (proj1 sm2_p_montgomery_bounds).
  - exact sm2_p_more_than_three_quarters.
  - exact sm2_p_prime.
  - exact Hstate.
  - exact Hv0.
  - exact Huodd.
  - exact Hvodd.
  - exact Huv.
  - exact Hshift.
Qed.

Lemma sm2n_double_reduction_result :
  forall x y intermediate result k1 k2,
    0 <= result < SM2_N_Z ->
    intermediate * U256_MOD = x * y + k1 * SM2_N_Z ->
    result * U256_MOD = intermediate * SM2_NH_Z + k2 * SM2_N_Z ->
    result = Zmod (x * y) SM2_N_Z.
Proof.
  intros x y intermediate result k1 k2 Hresult Hfirst Hsecond.
  pose proof sm2_n_bounds as Hmodulus.
  destruct sm2n_montgomery_parameters_valid as [_ Hgcd].
  assert (Hcoprime : rel_prime SM2_N_Z U256_MOD).
  {
    apply (proj1 (Zgcd_1_rel_prime _ _)).
    exact Hgcd.
  }
  assert (Hnh_divides :
    (SM2_N_Z | SM2_NH_Z - U256_MOD * U256_MOD)).
  {
    apply Zmod_divide; [lia |].
    rewrite Zminus_mod, sm2_nh_is_r2, Z.mod_mod,
      Z.sub_diag, Z.mod_0_l by lia.
    reflexivity.
  }
  destruct Hnh_divides as [qnh Hqnh].
  assert (Hscaled :
    (SM2_N_Z | (result - x * y) * U256_MOD)).
  {
    exists (k2 + intermediate * qnh + U256_MOD * k1).
    replace ((result - x * y) * U256_MOD) with
      ((result * U256_MOD - intermediate * SM2_NH_Z) +
       intermediate * (SM2_NH_Z - U256_MOD * U256_MOD) +
       U256_MOD * (intermediate * U256_MOD - x * y)) by ring.
    rewrite Hsecond, Hqnh, Hfirst.
    ring.
  }
  assert (Hdivides : (SM2_N_Z | result - x * y)).
  {
    apply (Gauss SM2_N_Z U256_MOD (result - x * y));
      [| exact Hcoprime].
    rewrite Z.mul_comm.
    exact Hscaled.
  }
  destruct Hdivides as [q Hq].
  apply Z.mod_unique with (q := -q); [lia |].
  nia.
Qed.

(** * Prime-field halving *)

Definition fp_div2 (x : Z) : Z :=
  if Z.even x then x / 2 else (x + SM2_P_Z) / 2.

Definition fp_div2_adjusted (x : Z) : Z :=
  if Z.even x then x else x + SM2_P_Z.

Lemma fp_div2_adjusted_twice :
  forall x, fp_div2_adjusted x = 2 * fp_div2 x.
Proof.
  intros x.
  assert (Hpodd : Z.Odd SM2_P_Z).
  { rewrite <- Z.odd_spec. cbv [SM2_P_Z]. reflexivity. }
  unfold fp_div2_adjusted, fp_div2.
  destruct (Z.even x) eqn:Heven.
  - apply Z.even_spec in Heven.
    destruct Heven as [k Hk].
    rewrite Hk, Z.mul_comm, Z.div_mul by lia.
    ring.
  - assert (Hodd : Z.odd x = true).
    { rewrite <- Z.negb_even, Heven. reflexivity. }
    apply Z.odd_spec in Hodd.
    destruct Hodd as [k Hk].
    destruct Hpodd as [kp Hkp].
    rewrite Hk, Hkp.
    replace (2 * k + 1 + (2 * kp + 1)) with (2 * (k + kp + 1)) by ring.
    rewrite Z.mul_comm, Z.div_mul by lia.
    ring.
Qed.

Lemma fp_div2_bounds :
  forall x,
    0 <= x < SM2_P_Z ->
    0 <= fp_div2 x < SM2_P_Z.
Proof.
  intros x Hx.
  pose proof sm2_p_montgomery_bounds as Hp.
  unfold fp_div2.
  destruct (Z.even x).
  - split.
    + apply Z.div_pos; lia.
    + apply Z.div_lt_upper_bound; lia.
  - split.
    + apply Z.div_pos; lia.
    + apply Z.div_lt_upper_bound; lia.
Qed.

Lemma u256_low_bit :
  forall x0 x1 x2 x3,
    Z.land (u256_of_limbs x0 x1 x2 x3) 1 = Z.land x0 1.
Proof.
  intros x0 x1 x2 x3.
  assert (Hdecomp :
    u256_of_limbs x0 x1 x2 x3 =
      x0 + U64_MOD * (x1 + x2 * U64_MOD + x3 * U64_MOD ^ 2)).
  { unfold u256_of_limbs. ring. }
  rewrite Hdecomp.
  set (q := x1 + x2 * U64_MOD + x3 * U64_MOD ^ 2).
  replace (U64_MOD * q) with (2 * (2 ^ 63 * q)) by
    (unfold U64_MOD; ring).
  replace 1 with (Z.ones 1) by reflexivity.
  rewrite !Z.land_ones by lia.
  change ((x0 + 2 * (2 ^ 63 * q)) mod 2 = x0 mod 2).
  rewrite Z.add_mod by lia.
  replace ((2 * (2 ^ 63 * q)) mod 2) with 0.
  2:{ replace (2 * (2 ^ 63 * q)) with ((2 ^ 63 * q) * 2) by ring.
      symmetry; apply Z.mod_mul; lia. }
  rewrite Z.add_0_r, Z.mod_mod by lia.
  reflexivity.
Qed.

Lemma fp_div2_adjusted_odd :
  forall x x0 x1 x2 x3,
    x = u256_of_limbs x0 x1 x2 x3 ->
    Z.land x0 1 <> 0 ->
    fp_div2_adjusted x = x + SM2_P_Z.
Proof.
  intros x x0 x1 x2 x3 Hx Hodd.
  unfold fp_div2_adjusted.
  destruct (Z.even x) eqn:Heven; [|reflexivity].
  exfalso.
  apply Z.even_spec in Heven.
  destruct Heven as [k Hk].
  apply Hodd.
  rewrite <- (u256_low_bit x0 x1 x2 x3), <- Hx, Hk.
  replace 1 with (Z.ones 1) by reflexivity.
  rewrite Z.land_ones by lia.
  change ((2 * k) mod 2 = 0).
  rewrite Z.mul_comm.
  apply Z.mod_mul; lia.
Qed.

Lemma fp_div2_adjusted_even :
  forall x x0 x1 x2 x3,
    x = u256_of_limbs x0 x1 x2 x3 ->
    Z.land x0 1 = 0 ->
    fp_div2_adjusted x = x.
Proof.
  intros x x0 x1 x2 x3 Hx Heven_low.
  unfold fp_div2_adjusted.
  destruct (Z.even x) eqn:Heven; [reflexivity|].
  exfalso.
  assert (Hodd : Z.odd x = true).
  { rewrite <- Z.negb_even, Heven. reflexivity. }
  apply Z.odd_spec in Hodd.
  destruct Hodd as [k Hk].
  assert (Hland : Z.land x 1 = 1).
  {
    rewrite Hk.
    replace 1 with (Z.ones 1) by reflexivity.
    rewrite Z.land_ones by lia.
    change ((2 * k + 1) mod 2 = 1).
    rewrite Z.add_mod, Z.mul_mod by lia.
    cbn; reflexivity.
  }
  rewrite Hx, u256_low_bit, Heven_low in Hland.
  discriminate.
Qed.

Lemma add_sm2_p_carry_chain :
  forall x x0 x1 x2 x3 y0 y1 y2 y3 c1 c2 c3 c4,
    x = u256_of_limbs x0 x1 x2 x3 ->
    x0 + SM2_P_LIMB_0 = y0 + c1 * U64_MOD ->
    x1 + SM2_P_LIMB_1 + c1 = y1 + c2 * U64_MOD ->
    x2 + SM2_P_LIMB_2 + c2 = y2 + c3 * U64_MOD ->
    x3 + SM2_P_LIMB_3 + c3 = y3 + c4 * U64_MOD ->
    x + SM2_P_Z = u256_of_limbs y0 y1 y2 y3 + c4 * U256_MOD.
Proof.
  intros x x0 x1 x2 x3 y0 y1 y2 y3 c1 c2 c3 c4
    Hx H0 H1 H2 H3.
  pose proof (u256_add_carry_chain
    x0 x1 x2 x3
    SM2_P_LIMB_0 SM2_P_LIMB_1 SM2_P_LIMB_2 SM2_P_LIMB_3
    y0 y1 y2 y3 c1 c2 c3 c4 H0 H1 H2 H3) as Hsum.
  destruct sm2_p_limbs as [_ [_ [_ [_ Hp]]]].
  rewrite <- Hx, <- Hp in Hsum.
  exact Hsum.
Qed.

Lemma u256_shift_right_one :
  forall x0 x1 x2 x3,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    0 <= x3 < U64_MOD ->
    u256_of_limbs
      (Z.lor (Z.shiftr x0 1)
        (unsigned_last_nbits (Z.shiftl x1 63) 64))
      (Z.lor (Z.shiftr x1 1)
        (unsigned_last_nbits (Z.shiftl x2 63) 64))
      (Z.lor (Z.shiftr x2 1)
        (unsigned_last_nbits (Z.shiftl x3 63) 64))
      (Z.shiftr x3 1) =
    u256_of_limbs x0 x1 x2 x3 / 2.
Proof.
  intros x0 x1 x2 x3 H0 H1 H2 H3.
  replace 63 with (64 - 1) by lia.
  rewrite
    (u64_rshift_lor_add__u256_shift x0 x1 1 H0 ltac:(lia)),
    (u64_rshift_lor_add__u256_shift x1 x2 1 H1 ltac:(lia)),
    (u64_rshift_lor_add__u256_shift x2 x3 1 H2 ltac:(lia)).
  rewrite
    (unsigned_last_nbits_shiftl_high__u256_shift x1 1 H1 ltac:(lia)),
    (unsigned_last_nbits_shiftl_high__u256_shift x2 1 H2 ltac:(lia)),
    (unsigned_last_nbits_shiftl_high__u256_shift x3 1 H3 ltac:(lia)).
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  apply Z.div_unique with (r := x0 mod 2).
  - pose proof (Z.mod_pos_bound x0 2 ltac:(lia)); lia.
  - pose proof (Z.div_mod x0 2 ltac:(lia)) as D0.
    pose proof (Z.div_mod x1 2 ltac:(lia)) as D1.
    pose proof (Z.div_mod x2 2 ltac:(lia)) as D2.
    pose proof (Z.div_mod x3 2 ltac:(lia)) as D3.
    unfold u256_of_limbs, U64_MOD.
    ring_simplify.
    lia.
Qed.

Lemma u256_shift_right_one_with_carry :
  forall x0 x1 x2 x3,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    0 <= x3 < U64_MOD ->
    u256_of_limbs
      (Z.lor (Z.shiftr x0 1)
        (unsigned_last_nbits (Z.shiftl x1 63) 64))
      (Z.lor (Z.shiftr x1 1)
        (unsigned_last_nbits (Z.shiftl x2 63) 64))
      (Z.lor (Z.shiftr x2 1)
        (unsigned_last_nbits (Z.shiftl x3 63) 64))
      (Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63)) =
    (u256_of_limbs x0 x1 x2 x3 + U256_MOD) / 2.
Proof.
  intros x0 x1 x2 x3 H0 H1 H2 H3.
  assert (Htop :
    Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63) = Z.shiftr x3 1 + 2 ^ 63).
  {
    replace 63 with (64 - 1) by lia.
    rewrite <- (unsigned_last_nbits_eq (Z.shiftl 1 (64 - 1)) 64)
      by (rewrite Z.shiftl_mul_pow2 by lia; split; lia).
    rewrite
      (u64_rshift_lor_add__u256_shift x3 1 1 H3 ltac:(lia)),
      (unsigned_last_nbits_shiftl_high__u256_shift 1 1
        ltac:(unfold U64_MOD; lia) ltac:(lia)).
    reflexivity.
  }
  rewrite Htop.
  replace
    (u256_of_limbs
      (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits (Z.shiftl x1 63) 64))
      (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits (Z.shiftl x2 63) 64))
      (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits (Z.shiftl x3 63) 64))
      (Z.shiftr x3 1 + 2 ^ 63))
    with
    (u256_of_limbs
      (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits (Z.shiftl x1 63) 64))
      (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits (Z.shiftl x2 63) 64))
      (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits (Z.shiftl x3 63) 64))
      (Z.shiftr x3 1) + 2 ^ 63 * U64_MOD ^ 3)
    by (unfold u256_of_limbs; ring).
  rewrite u256_shift_right_one by assumption.
  apply Z.div_unique with (r := u256_of_limbs x0 x1 x2 x3 mod 2).
  - pose proof (Z.mod_pos_bound (u256_of_limbs x0 x1 x2 x3) 2 ltac:(lia)); lia.
  - pose proof (Z.div_mod (u256_of_limbs x0 x1 x2 x3) 2 ltac:(lia)) as Hdm.
    unfold U64_MOD, U256_MOD.
    ring_simplify.
    lia.
Qed.

Lemma u64_shift_join_range :
  forall low high,
    0 <= low < U64_MOD ->
    0 <= high < U64_MOD ->
    0 <= Z.lor (Z.shiftr low 1)
      (unsigned_last_nbits (Z.shiftl high 63) 64) < U64_MOD.
Proof.
  intros low high Hlow Hhigh.
  replace 63 with (64 - 1) by lia.
  rewrite (u64_rshift_lor_add__u256_shift low high 1 Hlow ltac:(lia)).
  rewrite (unsigned_last_nbits_shiftl_high__u256_shift high 1 Hhigh ltac:(lia)).
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound high 2 ltac:(lia)) as Hmod.
  unfold U64_MOD in Hlow.
  assert (Hdiv : 0 <= low / 2 < 2 ^ 63).
  { split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  unfold U64_MOD in *.
  change (0 <= low / 2 < 9223372036854775808) in Hdiv.
  change (0 <= low / 2 + (high mod 2) * 9223372036854775808 <
    18446744073709551616).
  lia.
Qed.

Lemma u64_shift_top_carry_range :
  forall high,
    0 <= high < U64_MOD ->
    0 <= Z.lor (Z.shiftr high 1) (Z.shiftl 1 63) < U64_MOD.
Proof.
  intros high Hhigh.
  replace (Z.shiftl 1 63) with
    (unsigned_last_nbits (Z.shiftl 1 63) 64).
  2:{ unfold unsigned_last_nbits; rewrite Z.shiftl_mul_pow2 by lia;
      unfold U64_MOD; reflexivity. }
  replace 63 with (64 - 1) by lia.
  rewrite (u64_rshift_lor_add__u256_shift high 1 1 Hhigh ltac:(lia)).
  rewrite (unsigned_last_nbits_shiftl_high__u256_shift 1 1
    ltac:(unfold U64_MOD; lia) ltac:(lia)).
  rewrite Z.shiftr_div_pow2 by lia.
  unfold U64_MOD in Hhigh.
  assert (Hdiv : 0 <= high / 2 < 2 ^ 63).
  { split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  unfold U64_MOD in *.
  change (0 <= high / 2 < 9223372036854775808) in Hdiv.
  change (0 <= high / 2 + 9223372036854775808 < 18446744073709551616).
  lia.
Qed.

Lemma fp_div2_odd_with_carry :
  forall x x0 x1 x2 x3 y0 y1 y2 y3 c1 c2 c3 c4,
    x = u256_of_limbs x0 x1 x2 x3 ->
    Z.land x0 1 <> 0 ->
    0 <= y0 < U64_MOD ->
    0 <= y1 < U64_MOD ->
    0 <= y2 < U64_MOD ->
    0 <= y3 < U64_MOD ->
    0 <= c4 <= 1 ->
    x0 + SM2_P_LIMB_0 = y0 + c1 * U64_MOD ->
    x1 + SM2_P_LIMB_1 + c1 = y1 + c2 * U64_MOD ->
    x2 + SM2_P_LIMB_2 + c2 = y2 + c3 * U64_MOD ->
    x3 + SM2_P_LIMB_3 + c3 = y3 + c4 * U64_MOD ->
    c4 <> 0 ->
    fp_div2 x =
      u256_of_limbs
        (Z.lor (Z.shiftr y0 1) (unsigned_last_nbits (Z.shiftl y1 63) 64))
        (Z.lor (Z.shiftr y1 1) (unsigned_last_nbits (Z.shiftl y2 63) 64))
        (Z.lor (Z.shiftr y2 1) (unsigned_last_nbits (Z.shiftl y3 63) 64))
        (Z.lor (Z.shiftr y3 1) (Z.shiftl 1 63)).
Proof.
  intros x x0 x1 x2 x3 y0 y1 y2 y3 c1 c2 c3 c4
    Hx Hodd Hy0 Hy1 Hy2 Hy3 Hc4 H0 H1 H2 H3 Hcarry.
  assert (Hc4one : c4 = 1) by lia.
  pose proof (add_sm2_p_carry_chain
    x x0 x1 x2 x3 y0 y1 y2 y3 c1 c2 c3 c4
    Hx H0 H1 H2 H3) as Hadd.
  rewrite Hc4one, Z.mul_1_l in Hadd.
  pose proof (fp_div2_adjusted_odd x x0 x1 x2 x3 Hx Hodd) as Hadj.
  pose proof (u256_shift_right_one_with_carry y0 y1 y2 y3
    Hy0 Hy1 Hy2 Hy3) as Hshift.
  pose proof (fp_div2_adjusted_twice x) as Htwice.
  rewrite Hadd in Hadj.
  rewrite Htwice in Hadj.
  rewrite Hshift.
  rewrite <- Hadj.
  rewrite Z.mul_comm, Z.div_mul by lia.
  reflexivity.
Qed.

Lemma fp_div2_odd_without_carry :
  forall x x0 x1 x2 x3 y0 y1 y2 y3 c1 c2 c3 c4,
    x = u256_of_limbs x0 x1 x2 x3 ->
    Z.land x0 1 <> 0 ->
    0 <= y0 < U64_MOD ->
    0 <= y1 < U64_MOD ->
    0 <= y2 < U64_MOD ->
    0 <= y3 < U64_MOD ->
    x0 + SM2_P_LIMB_0 = y0 + c1 * U64_MOD ->
    x1 + SM2_P_LIMB_1 + c1 = y1 + c2 * U64_MOD ->
    x2 + SM2_P_LIMB_2 + c2 = y2 + c3 * U64_MOD ->
    x3 + SM2_P_LIMB_3 + c3 = y3 + c4 * U64_MOD ->
    c4 = 0 ->
    fp_div2 x =
      u256_of_limbs
        (Z.lor (Z.shiftr y0 1) (unsigned_last_nbits (Z.shiftl y1 63) 64))
        (Z.lor (Z.shiftr y1 1) (unsigned_last_nbits (Z.shiftl y2 63) 64))
        (Z.lor (Z.shiftr y2 1) (unsigned_last_nbits (Z.shiftl y3 63) 64))
        (Z.shiftr y3 1).
Proof.
  intros x x0 x1 x2 x3 y0 y1 y2 y3 c1 c2 c3 c4
    Hx Hodd Hy0 Hy1 Hy2 Hy3 H0 H1 H2 H3 Hc4.
  pose proof (add_sm2_p_carry_chain
    x x0 x1 x2 x3 y0 y1 y2 y3 c1 c2 c3 c4
    Hx H0 H1 H2 H3) as Hadd.
  rewrite Hc4, Z.mul_0_l, Z.add_0_r in Hadd.
  pose proof (fp_div2_adjusted_odd x x0 x1 x2 x3 Hx Hodd) as Hadj.
  pose proof (u256_shift_right_one y0 y1 y2 y3 Hy0 Hy1 Hy2 Hy3) as Hshift.
  pose proof (fp_div2_adjusted_twice x) as Htwice.
  rewrite Hadd in Hadj.
  rewrite Htwice in Hadj.
  rewrite Hshift.
  rewrite <- Hadj.
  rewrite Z.mul_comm, Z.div_mul by lia.
  reflexivity.
Qed.

Lemma fp_div2_even :
  forall x x0 x1 x2 x3,
    x = u256_of_limbs x0 x1 x2 x3 ->
    Z.land x0 1 = 0 ->
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    0 <= x3 < U64_MOD ->
    fp_div2 x =
      u256_of_limbs
        (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits (Z.shiftl x1 63) 64))
        (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits (Z.shiftl x2 63) 64))
        (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits (Z.shiftl x3 63) 64))
        (Z.shiftr x3 1).
Proof.
  intros x x0 x1 x2 x3 Hx Heven H0 H1 H2 H3.
  pose proof (fp_div2_adjusted_even x x0 x1 x2 x3 Hx Heven) as Hadj.
  pose proof (u256_shift_right_one x0 x1 x2 x3 H0 H1 H2 H3) as Hshift.
  pose proof (fp_div2_adjusted_twice x) as Htwice.
  rewrite Htwice in Hadj.
  rewrite Hshift.
  rewrite <- Hx.
  apply Z.div_unique with (r := 0); lia.
Qed.

(** * Group-order reduction facts *)

Lemma sm2_n_more_than_half :
  U256_MOD < 2 * SM2_N_Z.
Proof.
  cbv [SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
       u256_of_limbs U32_MOD U64_MOD U256_MOD].
  lia.
Qed.

Lemma sm2_n_reduce_u256_once :
  forall x,
    0 <= x < U256_MOD ->
    x mod SM2_N_Z = if Z.ltb x SM2_N_Z then x else x - SM2_N_Z.
Proof.
  intros x Hx.
  pose proof sm2_n_bounds as HN.
  pose proof sm2_n_more_than_half as Hhalf.
  destruct (Z.ltb x SM2_N_Z) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    rewrite Z.mod_small; lia.
  - apply Z.ltb_ge in Hlt.
    replace x with ((x - SM2_N_Z) + 1 * SM2_N_Z) at 1 by ring.
    rewrite Z.mod_add by lia.
    rewrite Z.mod_small; lia.
Qed.

(** * Solinas reduction *)

Definition SOLINAS_MINUS_MAX : Z := 4 * (U32_MOD - 1).

Lemma solinas_minus_product_bound :
  forall minus,
    0 <= minus ->
    minus <= SOLINAS_MINUS_MAX ->
    minus * U64_MOD < SM2_P_Z.
Proof.
  intros minus Hminus0 Hminusmax.
  eapply Z.le_lt_trans with (m := SOLINAS_MINUS_MAX * U64_MOD).
  - apply Z.mul_le_mono_nonneg_r.
    + unfold U64_MOD. lia.
    + exact Hminusmax.
  - cbv [SOLINAS_MINUS_MAX U32_MOD U64_MOD SM2_P_Z].
    lia.
Qed.

Lemma solinas_minus_expr_value :
  forall h8 h9 h13 h14,
    0 <= h8 < U32_MOD ->
    0 <= h9 < U32_MOD ->
    0 <= h13 < U32_MOD ->
    0 <= h14 < U32_MOD ->
    let minus :=
      unsigned_last_nbits
        (unsigned_last_nbits
          (unsigned_last_nbits (h8 + h9) 64 + h13) 64 + h14) 64 in
    minus = h8 + h9 + h13 + h14 /\
    0 <= minus <= SOLINAS_MINUS_MAX.
Proof.
  intros h8 h9 h13 h14 Hh8 Hh9 Hh13 Hh14.
  cbn zeta.
  assert (H89 : 0 <= h8 + h9 < U64_MOD).
  { unfold U32_MOD, U64_MOD in *; lia. }
  rewrite (unsigned_last_nbits_u64_small (h8 + h9) H89).
  assert (H8913 : 0 <= h8 + h9 + h13 < U64_MOD).
  { unfold U32_MOD, U64_MOD in *; lia. }
  rewrite (unsigned_last_nbits_u64_small (h8 + h9 + h13) H8913).
  assert (Hsum : 0 <= h8 + h9 + h13 + h14 < U64_MOD).
  { unfold U32_MOD, U64_MOD in *; lia. }
  rewrite (unsigned_last_nbits_u64_small
    (h8 + h9 + h13 + h14) Hsum).
  unfold SOLINAS_MINUS_MAX, U32_MOD in *.
  lia.
Qed.

Lemma solinas_finish_no_first_carry :
  forall T low high SD acc carry minus Khigh S out7 payload S2,
    T = low + high * U256_MOD ->
    high * U256_MOD =
      SD + acc * U256_MOD - minus * U64_MOD + Khigh * SM2_P_Z ->
    low + SD = S + carry * U256_MOD ->
    out7 = acc + carry ->
    payload = out7 * SM2_RHOP_Z ->
    payload + S = S2 ->
    T = S2 - minus * U64_MOD + (Khigh + out7) * SM2_P_Z.
Proof.
  intros T low high SD acc carry minus Khigh S out7 payload S2
    HT Hhigh Hlow Hout7 Hpayload Hsum.
  unfold SM2_RHOP_Z in Hpayload.
  nia.
Qed.

Lemma solinas_second_add_carry_zero :
  forall out7 payload S S2 S3 carry2,
    0 <= out7 <= 13 ->
    0 <= S < U256_MOD ->
    0 <= S2 < U256_MOD ->
    0 <= S3 < U256_MOD ->
    0 <= carry2 <= 1 ->
    payload = out7 * SM2_RHOP_Z ->
    payload + S = S2 + U256_MOD ->
    SM2_RHOP_Z + S2 = S3 + carry2 * U256_MOD ->
    carry2 = 0.
Proof.
  intros out7 payload S S2 S3 carry2
    Hout7 HS HS2 HS3 Hcarry2 Hpayload Hsum Hadd.
  assert (Hrho14 : 14 * SM2_RHOP_Z < U256_MOD).
  { cbv [SM2_RHOP_Z SM2_P_Z U256_MOD]. lia. }
  nia.
Qed.

Lemma solinas_finish_first_carry :
  forall T low high SD acc carry minus Khigh
    S out7 payload S2 S3,
    T = low + high * U256_MOD ->
    high * U256_MOD =
      SD + acc * U256_MOD - minus * U64_MOD + Khigh * SM2_P_Z ->
    low + SD = S + carry * U256_MOD ->
    out7 = acc + carry ->
    payload = out7 * SM2_RHOP_Z ->
    payload + S = S2 + U256_MOD ->
    SM2_RHOP_Z + S2 = S3 ->
    T =
      S3 - minus * U64_MOD +
      (Khigh + out7 + 1) * SM2_P_Z.
Proof.
  intros T low high SD acc carry minus Khigh
    S out7 payload S2 S3
    HT Hhigh Hlow Hout7 Hpayload Hsum Hadd.
  unfold SM2_RHOP_Z in Hpayload, Hadd.
  nia.
Qed.

Lemma solinas_carry_normalized :
  forall out7 payload S S2 carry,
    0 <= out7 <= 13 ->
    0 <= S < U256_MOD ->
    0 <= S2 < U256_MOD ->
    0 <= carry <= 1 ->
    payload = out7 * SM2_RHOP_Z ->
    payload + S = S2 + carry * U256_MOD ->
    0 <= S2 + carry * SM2_RHOP_Z < U256_MOD.
Proof.
  intros out7 payload S S2 carry
    Hout7 HS HS2 Hcarry Hpayload Hsum.
  assert (Hrho0 : 0 < SM2_RHOP_Z).
  { cbv [SM2_RHOP_Z SM2_P_Z U256_MOD]. lia. }
  assert (Hrho14 : 14 * SM2_RHOP_Z < U256_MOD).
  { cbv [SM2_RHOP_Z SM2_P_Z U256_MOD]. lia. }
  destruct (Z.eq_dec carry 0) as [Hzero | Hnonzero].
  - subst carry. lia.
  - assert (carry = 1) by lia.
    subst carry.
    nia.
Qed.

Lemma solinas_finish_normalized :
  forall T low high SD acc carry minus Khigh S out7 payload S2,
    T = low + high * U256_MOD ->
    high * U256_MOD =
      SD + acc * U256_MOD - minus * U64_MOD + Khigh * SM2_P_Z ->
    low + SD = S + carry * U256_MOD ->
    out7 = acc + carry ->
    payload = out7 * SM2_RHOP_Z ->
    forall carry2,
      payload + S = S2 + carry2 * U256_MOD ->
      T =
        (S2 + carry2 * SM2_RHOP_Z) - minus * U64_MOD +
        (Khigh + out7 + carry2) * SM2_P_Z.
Proof.
  intros T low high SD acc carry minus Khigh S out7 payload S2
    HT Hhigh Hlow Hout7 Hpayload carry2 Hsum.
  unfold SM2_RHOP_Z in Hpayload |- *.
  nia.
Qed.

Lemma solinas_mixed_high_decomposition :
  forall words limbs T,
    Zlength words = 16 ->
    u32_list_bounded words ->
    u32_list_value words = T ->
    Zlength limbs = 8 ->
    u64_list_bounded limbs ->
    u64_list_value limbs = T ->
    T =
      u256_of_limbs
        (Znth 0 limbs 0) (Znth 1 limbs 0)
        (Znth 2 limbs 0) (Znth 3 limbs 0) +
      u256_of_limbs
        (Znth 8 words 0 + Znth 9 words 0 * U32_MOD)
        (Znth 10 words 0 + Znth 11 words 0 * U32_MOD)
        (Znth 12 words 0 + Znth 13 words 0 * U32_MOD)
        (Znth 14 words 0 + Znth 15 words 0 * U32_MOD) * U256_MOD.
Proof.
  intros words limbs T
    Hwords_len Hwords_bounded Hwords_value
    Hlimbs_len Hlimbs_bounded Hlimbs_value.
  pose proof
    (u64_list_value_len8_decompose limbs Hlimbs_len) as Hlimbs_decomp.
  pose proof
    (u32_list_value_len16_decompose words Hwords_len) as Hwords_decomp.
  pose proof (Hlimbs_bounded 0 ltac:(lia)) as Hl0.
  pose proof (Hlimbs_bounded 1 ltac:(lia)) as Hl1.
  pose proof (Hlimbs_bounded 2 ltac:(lia)) as Hl2.
  pose proof (Hlimbs_bounded 3 ltac:(lia)) as Hl3.
  pose proof (Hwords_bounded 0 ltac:(lia)) as Hw0.
  pose proof (Hwords_bounded 1 ltac:(lia)) as Hw1.
  pose proof (Hwords_bounded 2 ltac:(lia)) as Hw2.
  pose proof (Hwords_bounded 3 ltac:(lia)) as Hw3.
  pose proof (Hwords_bounded 4 ltac:(lia)) as Hw4.
  pose proof (Hwords_bounded 5 ltac:(lia)) as Hw5.
  pose proof (Hwords_bounded 6 ltac:(lia)) as Hw6.
  pose proof (Hwords_bounded 7 ltac:(lia)) as Hw7.
  pose proof
    (u32_pair_range
      (Znth 0 words 0) (Znth 1 words 0) Hw0 Hw1) as Hp0.
  pose proof
    (u32_pair_range
      (Znth 2 words 0) (Znth 3 words 0) Hw2 Hw3) as Hp1.
  pose proof
    (u32_pair_range
      (Znth 4 words 0) (Znth 5 words 0) Hw4 Hw5) as Hp2.
  pose proof
    (u32_pair_range
      (Znth 6 words 0) (Znth 7 words 0) Hw6 Hw7) as Hp3.
  pose proof
    (u256_of_limbs_range
      (Znth 0 limbs 0) (Znth 1 limbs 0)
      (Znth 2 limbs 0) (Znth 3 limbs 0)
      Hl0 Hl1 Hl2 Hl3) as Hlow_limbs.
  pose proof
    (u256_of_limbs_range
      (Znth 0 words 0 + Znth 1 words 0 * U32_MOD)
      (Znth 2 words 0 + Znth 3 words 0 * U32_MOD)
      (Znth 4 words 0 + Znth 5 words 0 * U32_MOD)
      (Znth 6 words 0 + Znth 7 words 0 * U32_MOD)
      Hp0 Hp1 Hp2 Hp3) as Hlow_words.
  assert (Heq :
    u256_of_limbs
      (Znth 0 limbs 0) (Znth 1 limbs 0)
      (Znth 2 limbs 0) (Znth 3 limbs 0) +
      U256_MOD *
      u256_of_limbs
        (Znth 4 limbs 0) (Znth 5 limbs 0)
        (Znth 6 limbs 0) (Znth 7 limbs 0) =
    u256_of_limbs
      (Znth 0 words 0 + Znth 1 words 0 * U32_MOD)
      (Znth 2 words 0 + Znth 3 words 0 * U32_MOD)
      (Znth 4 words 0 + Znth 5 words 0 * U32_MOD)
      (Znth 6 words 0 + Znth 7 words 0 * U32_MOD) +
      U256_MOD *
      u256_of_limbs
        (Znth 8 words 0 + Znth 9 words 0 * U32_MOD)
        (Znth 10 words 0 + Znth 11 words 0 * U32_MOD)
        (Znth 12 words 0 + Znth 13 words 0 * U32_MOD)
        (Znth 14 words 0 + Znth 15 words 0 * U32_MOD)).
  {
    transitivity T.
    - rewrite <- Hlimbs_value, Hlimbs_decomp. ring.
    - rewrite <- Hwords_value, Hwords_decomp. ring.
  }
  pose proof
    (radix_step_unique
      U256_MOD
      (u256_of_limbs
        (Znth 0 limbs 0) (Znth 1 limbs 0)
        (Znth 2 limbs 0) (Znth 3 limbs 0))
      (u256_of_limbs
        (Znth 4 limbs 0) (Znth 5 limbs 0)
        (Znth 6 limbs 0) (Znth 7 limbs 0))
      (u256_of_limbs
        (Znth 0 words 0 + Znth 1 words 0 * U32_MOD)
        (Znth 2 words 0 + Znth 3 words 0 * U32_MOD)
        (Znth 4 words 0 + Znth 5 words 0 * U32_MOD)
        (Znth 6 words 0 + Znth 7 words 0 * U32_MOD))
      (u256_of_limbs
        (Znth 8 words 0 + Znth 9 words 0 * U32_MOD)
        (Znth 10 words 0 + Znth 11 words 0 * U32_MOD)
        (Znth 12 words 0 + Znth 13 words 0 * U32_MOD)
        (Znth 14 words 0 + Znth 15 words 0 * U32_MOD))
      ltac:(unfold U256_MOD; lia)
      Hlow_limbs Hlow_words Heq) as [_ Hhigh].
  rewrite <- Hlimbs_value, Hlimbs_decomp.
  rewrite Hhigh.
  reflexivity.
Qed.

Lemma solinas_inverse_add_value :
  forall s0 s1 s2 s3 minus out1 out2 out3 c1 c2 c3 Sred,
    0 <= minus < U64_MOD ->
    Sred = u256_of_limbs s0 s1 s2 s3 ->
    s1 + unsigned_last_nbits (Z.lnot minus) 64 + 1 =
      out1 + c1 * U64_MOD ->
    s2 + UINT64_MAX + c1 = out2 + c2 * U64_MOD ->
    s3 + UINT64_MAX + c2 = out3 + c3 * U64_MOD ->
    u256_of_limbs s0 out1 out2 out3 =
      Sred - minus * U64_MOD + (1 - c3) * U256_MOD.
Proof.
  intros s0 s1 s2 s3 minus out1 out2 out3 c1 c2 c3 Sred
    Hminus HSred E1 E2 E3.
  pose proof (unsigned_lnot_u64 minus Hminus) as Hinv.
  assert (E0 : s0 + 0 = s0 + 0 * U64_MOD) by ring.
  rewrite Hinv in E1.
  replace UINT64_MAX with (U64_MOD - 1) in E2 by reflexivity.
  replace UINT64_MAX with (U64_MOD - 1) in E3 by reflexivity.
  pose proof
    (u256_add_carry_chain
      s0 s1 s2 s3
      0 (U64_MOD - minus) (U64_MOD - 1) (U64_MOD - 1)
      s0 out1 out2 out3
      0 c1 c2 c3 E0 ltac:(lia) E2 E3)
    as Hchain.
  assert (Haddend :
    u256_of_limbs
      0 (U64_MOD - minus) (U64_MOD - 1) (U64_MOD - 1) =
      U256_MOD - minus * U64_MOD).
  {
    cbv [u256_of_limbs U64_MOD U256_MOD].
    ring.
  }
  rewrite <- HSred, Haddend in Hchain.
  lia.
Qed.

Lemma solinas_payload_encoding :
  forall acc,
    0 <= acc <= 13 ->
    0 <= acc * SM2_RHOP_Z < U256_MOD /\
    acc * SM2_RHOP_Z =
      u256_of_limbs
        acc
        (unsigned_last_nbits
          (unsigned_last_nbits (Z.shiftl acc 32) 64 - acc) 64)
        0
        (unsigned_last_nbits (Z.shiftl acc 32) 64).
Proof.
  intros acc Hacc.
  assert (Hshift :
    unsigned_last_nbits (Z.shiftl acc 32) 64 = acc * U32_MOD).
  {
    rewrite Z.shiftl_mul_pow2 by lia.
    unfold U32_MOD.
    rewrite unsigned_last_nbits_eq.
    - ring.
    - unfold U64_MOD.
      nia.
  }
  assert (Hdiff :
    unsigned_last_nbits
      (unsigned_last_nbits (Z.shiftl acc 32) 64 - acc) 64 =
    acc * (U32_MOD - 1)).
  {
    rewrite Hshift.
    replace (acc * U32_MOD - acc) with (acc * (U32_MOD - 1))
      by ring.
    rewrite unsigned_last_nbits_eq.
    - reflexivity.
    - unfold U32_MOD, U64_MOD.
      nia.
  }
  rewrite Hdiff, Hshift.
  pose proof sm2_rhop_limbs as Hrho.
  destruct Hrho as [_ [_ [_ [_ Hrho]]]].
  rewrite Hrho.
  split.
  - cbv [SM2_RHOP0_Z SM2_RHOP1_Z SM2_RHOP2_Z SM2_RHOP3_Z
         u256_of_limbs U64_MOD U32_MOD U256_MOD].
    nia.
  - cbv [SM2_RHOP0_Z SM2_RHOP1_Z SM2_RHOP2_Z SM2_RHOP3_Z
         u256_of_limbs U64_MOD U32_MOD].
    ring.
Qed.

Lemma solinas_payload_cells_pack :
  forall p acc,
    0 <= acc <= 13 ->
    (((((&((p) # "u32" ->ₛ "v") +
        (0 * sizeof(UINT64))) # UInt64 |-> acc) **
      ((&((p) # "u32" ->ₛ "v") +
        (1 * sizeof(UINT64))) # UInt64 |->
        unsigned_last_nbits
          (unsigned_last_nbits (Z.shiftl acc 32) 64 - acc) 64)) **
      ((&((p) # "u32" ->ₛ "v") +
        (2 * sizeof(UINT64))) # UInt64 |-> 0)) **
      ((&((p) # "u32" ->ₛ "v") +
        (3 * sizeof(UINT64))) # UInt64 |->
        unsigned_last_nbits (Z.shiftl acc 32) 64))
    |-- store_u256 p (acc * SM2_RHOP_Z).
Proof.
  intros p acc Hacc.
  pose proof (solinas_payload_encoding acc Hacc) as [_ Hvalue].
  pose proof
    (unsigned_Lastnbits_range
      (unsigned_last_nbits (Z.shiftl acc 32) 64 - acc) 64
      ltac:(lia)) as Hmiddle.
  pose proof
    (unsigned_Lastnbits_range (Z.shiftl acc 32) 64 ltac:(lia))
    as Hhigh.
  unfold store_u256, store_u256_limbs.
  Exists
    acc
    (unsigned_last_nbits
      (unsigned_last_nbits (Z.shiftl acc 32) 64 - acc) 64)
    0
    (unsigned_last_nbits (Z.shiftl acc 32) 64).
  apply split_pure_and_spatial_goals.
  - entailer!.
  - split_pures; dump_pre_spatial; try assumption;
      unfold U64_MOD in *; lia.
Qed.

Lemma solinas_high_stage_from_carries :
  forall h8 h9 h10 h11 h12 h13 h14 h15
         d0 d1 d2 d3mid d3 acc c0 c1 c2 c3 c4 c5,
    0 <= h8 < U32_MOD ->
    0 <= h9 < U32_MOD ->
    0 <= h10 < U32_MOD ->
    0 <= h11 < U32_MOD ->
    0 <= h12 < U32_MOD ->
    0 <= h13 < U32_MOD ->
    0 <= h14 < U32_MOD ->
    0 <= h15 < U32_MOD ->
    0 <= d0 < U64_MOD ->
    0 <= d1 < U64_MOD ->
    0 <= d2 < U64_MOD ->
    0 <= d3mid < U64_MOD ->
    0 <= d3 < U64_MOD ->
    0 <= acc < U64_MOD ->
    0 <= c0 <= 1 ->
    0 <= c1 <= 1 ->
    0 <= c2 <= 1 ->
    0 <= c3 <= 1 ->
    0 <= c4 <= 1 ->
    0 <= c5 <= 1 ->
    let b0 :=
      h8 + h9 + h10 + h11 + h12 + 2 * h13 + 2 * h14 + 2 * h15 in
    let b1 :=
      h9 + h10 + h11 + h12 + h13 + 2 * h14 + 2 * h15 in
    let b3 :=
      h8 + h11 + h12 + 2 * h13 + h14 + h15 in
    let b5 :=
      h10 + h13 + h14 + 2 * h15 in
    let r2 :=
      h9 + h12 + h13 + 2 * h14 + h15 in
    let r3 :=
      h11 + h14 + h15 in
    let b7 :=
      h8 + h9 + h10 + h11 + 2 * h12 + 2 * h13 +
        2 * h14 + 3 * h15 in
    r2 + (mulx32_hi b3 + mulx32_lo b5 * U32_MOD) =
      d2 + c0 * U64_MOD ->
    r3 + mulx32_hi b5 + c0 =
      d3mid + c1 * U64_MOD ->
    b0 + mulx32_lo b1 * U32_MOD =
      d0 + c2 * U64_MOD ->
    mulx32_hi b1 + mulx32_lo b3 * U32_MOD + c2 =
      d1 + c3 * U64_MOD ->
    d3mid + mulx32_lo b7 * U32_MOD =
      d3 + c4 * U64_MOD ->
    mulx32_hi b7 + c4 =
      acc + c5 * U64_MOD ->
    exists Khigh,
      0 <= u256_of_limbs d0 d1 d2 d3 < U256_MOD /\
      0 <= acc <= 12 /\
      0 <= h8 + h9 + h13 + h14 <= SOLINAS_MINUS_MAX /\
      (h8 + h9 * U32_MOD +
       (h10 + h11 * U32_MOD) * U64_MOD +
       (h12 + h13 * U32_MOD) * U64_MOD * U64_MOD +
       (h14 + h15 * U32_MOD) *
         U64_MOD * U64_MOD * U64_MOD) * U256_MOD =
      u256_of_limbs d0 d1 d2 d3 +
        acc * U256_MOD -
        (h8 + h9 + h13 + h14) * U64_MOD +
        Khigh * SM2_P_Z.
Proof.
  intros h8 h9 h10 h11 h12 h13 h14 h15
    d0 d1 d2 d3mid d3 acc c0 c1 c2 c3 c4 c5
    Hh8 Hh9 Hh10 Hh11 Hh12 Hh13 Hh14 Hh15
    Hd0 Hd1 Hd2 Hd3mid Hd3 Hacc
    Hc0 Hc1 Hc2 Hc3 Hc4 Hc5.
  cbn zeta.
  intros E2 E3 E0 E1 E3low Eacc.
  set (b0 :=
    h8 + h9 + h10 + h11 + h12 + 2 * h13 + 2 * h14 + 2 * h15)
    in *.
  set (b1 :=
    h9 + h10 + h11 + h12 + h13 + 2 * h14 + 2 * h15)
    in *.
  set (b3 := h8 + h11 + h12 + 2 * h13 + h14 + h15) in *.
  set (b5 := h10 + h13 + h14 + 2 * h15) in *.
  set (b7 :=
    h8 + h9 + h10 + h11 + 2 * h12 + 2 * h13 +
      2 * h14 + 3 * h15) in *.
  assert (Hb0 : 0 <= b0 < U64_MOD).
  { subst b0; unfold U32_MOD, U64_MOD in *; lia. }
  assert (Hb1 : 0 <= b1 < U64_MOD).
  { subst b1; unfold U32_MOD, U64_MOD in *; lia. }
  assert (Hb3 : 0 <= b3 < U64_MOD).
  { subst b3; unfold U32_MOD, U64_MOD in *; lia. }
  assert (Hb5 : 0 <= b5 < U64_MOD).
  { subst b5; unfold U32_MOD, U64_MOD in *; lia. }
  assert (Hb7 : 0 <= b7 < U64_MOD).
  { subst b7; unfold U32_MOD, U64_MOD in *; lia. }
  pose proof (u64_split_32 b0 Hb0) as Hb0split.
  pose proof (u64_split_32 b1 Hb1) as Hb1split.
  pose proof (u64_split_32 b3 Hb3) as Hb3split.
  pose proof (u64_split_32 b5 Hb5) as Hb5split.
  pose proof (u64_split_32 b7 Hb7) as Hb7split.
  destruct Hb0split as [Hb0eq [Hb0lo Hb0hi]].
  destruct Hb1split as [Hb1eq [Hb1lo Hb1hi]].
  destruct Hb3split as [Hb3eq [Hb3lo Hb3hi]].
  destruct Hb5split as [Hb5eq [Hb5lo Hb5hi]].
  destruct Hb7split as [Hb7eq [Hb7lo Hb7hi]].
  assert (Hc1zero : c1 = 0).
  { unfold U32_MOD, U64_MOD in *; lia. }
  assert (Hc3zero : c3 = 0).
  { unfold U32_MOD, U64_MOD in *; lia. }
  assert (Hc5zero : c5 = 0).
  { unfold U32_MOD, U64_MOD in *; lia. }
  assert (Haccsmall : 0 <= acc <= 12).
  { unfold U32_MOD, U64_MOD in *; lia. }
  exists
    (h8 +
     h9 * (U32_MOD + 1) +
     h10 * (U32_MOD ^ 2 + U32_MOD + 1) +
     h11 * (U32_MOD ^ 3 + U32_MOD ^ 2 + U32_MOD + 1) +
     h12 * (U32_MOD ^ 4 + U32_MOD ^ 3 + U32_MOD ^ 2 +
       U32_MOD + 1) +
     h13 * (U32_MOD ^ 5 + U32_MOD ^ 4 + U32_MOD ^ 3 +
       U32_MOD ^ 2 + U32_MOD + 2) +
     h14 * (U32_MOD ^ 6 + U32_MOD ^ 5 + U32_MOD ^ 4 +
       U32_MOD ^ 3 + U32_MOD ^ 2 + 2 * U32_MOD + 2) +
     h15 * (U32_MOD ^ 7 + U32_MOD ^ 6 + U32_MOD ^ 5 +
       U32_MOD ^ 4 + U32_MOD ^ 3 + 2 * U32_MOD ^ 2 +
       2 * U32_MOD + 2)).
  split.
  - apply u256_of_limbs_range; assumption.
  - split.
    + exact Haccsmall.
    + split.
      * unfold SOLINAS_MINUS_MAX, U32_MOD in *; lia.
      * subst b0 b1 b3 b5 b7.
        unfold mulx32_lo, mulx32_hi in *.
        cbv [u256_of_limbs U32_MOD U64_MOD U256_MOD SM2_P_Z] in *.
        lia.
Qed.

(** Proof support for the four-limb addition and conditional reduction in
    [add_mod_p]. *)
Lemma add_mod_n_sub_carry_chain :
  forall t0 t1 t2 t3 d0 d1 d2 d3 c1 c2 c3 c4,
    t0 + unsigned_last_nbits (Z.lnot SM2_N0_Z) 64 + 1 =
      d0 + c1 * U64_MOD ->
    t1 + unsigned_last_nbits (Z.lnot SM2_N1_Z) 64 + c1 =
      d1 + c2 * U64_MOD ->
    t2 + unsigned_last_nbits (Z.lnot SM2_N2_Z) 64 + c2 =
      d2 + c3 * U64_MOD ->
    t3 + unsigned_last_nbits (Z.lnot SM2_N3_Z) 64 + c3 =
      d3 + c4 * U64_MOD ->
    u256_of_limbs t0 t1 t2 t3 + U256_MOD - SM2_N_Z =
      u256_of_limbs d0 d1 d2 d3 + c4 * U256_MOD.
Proof.
  intros t0 t1 t2 t3 d0 d1 d2 d3 c1 c2 c3 c4 H0 H1 H2 H3.
  pose proof sm2_n_limbs as (HN0 & HN1 & HN2 & HN3).
  rewrite (unsigned_lnot_u64 SM2_N0_Z HN0) in H0.
  rewrite (unsigned_lnot_u64 SM2_N1_Z HN1) in H1.
  rewrite (unsigned_lnot_u64 SM2_N2_Z HN2) in H2.
  rewrite (unsigned_lnot_u64 SM2_N3_Z HN3) in H3.
  cbv [u256_of_limbs U64_MOD U256_MOD SM2_N_Z
       SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z U32_MOD] in *.
  lia.
Qed.

Lemma add_mod_n_no_reduction_arithmetic :
  forall A B T D carry borrow,
    0 <= A < SM2_N_Z ->
    0 <= B < SM2_N_Z ->
    0 <= T < U256_MOD ->
    0 <= D < U256_MOD ->
    0 <= carry <= 1 ->
    0 <= borrow <= 1 ->
    A + B = T + carry * U256_MOD ->
    T + U256_MOD - SM2_N_Z = D + borrow * U256_MOD ->
    Z.lor carry borrow = 0 ->
    Zmod (A + B) SM2_N_Z = T /\
    Zmod (A + B) U256_MOD = T.
Proof.
  intros A B T D carry borrow HA HB HT HD Hcarry Hborrow Hadd Hsub Hlor.
  apply Z.lor_eq_0_iff in Hlor.
  destruct Hlor as [-> ->].
  cbn in Hadd.
  rewrite Hadd.
  replace (T + 0) with T by lia.
  split; apply Z.mod_small; lia.
Qed.

Lemma add_mod_n_reduction_arithmetic :
  forall A B T D carry borrow,
    0 <= A < SM2_N_Z ->
    0 <= B < SM2_N_Z ->
    0 <= T < U256_MOD ->
    0 <= D < U256_MOD ->
    0 <= carry <= 1 ->
    0 <= borrow <= 1 ->
    A + B = T + carry * U256_MOD ->
    T + U256_MOD - SM2_N_Z = D + borrow * U256_MOD ->
    Z.lor carry borrow <> 0 ->
    Zmod (A + B) SM2_N_Z = D /\
    Zmod (A + B) U256_MOD = T.
Proof.
  intros A B T D carry borrow HA HB HT HD Hcarry Hborrow Hadd Hsub Hlor.
  assert (Hcarry_cases : carry = 0 \/ carry = 1) by lia.
  assert (Hborrow_cases : borrow = 0 \/ borrow = 1) by lia.
  destruct Hcarry_cases as [-> | ->];
    destruct Hborrow_cases as [-> | ->].
  - exfalso. apply Hlor. reflexivity.
  - split.
    + symmetry. apply Z.mod_unique with (q := 1); [left; lia | lia].
    + symmetry. apply Z.mod_unique with (q := 0); [left; lia | lia].
  - split.
    + symmetry. apply Z.mod_unique with (q := 1); [left; lia | lia].
    + symmetry. apply Z.mod_unique with (q := 1); [left; lia | lia].
  - pose proof sm2_n_more_than_half as Hmodulus.
    exfalso; lia.
Qed.

Ltac finish_add_mod_n_tmp sum out out_2 out_3 out_4 Hvalue Htmpmod :=
  assert (Hbounded :
    u64_list_bounded (out :: out_2 :: out_3 :: out_4 :: nil)) by (
      unfold u64_list_bounded;
      repeat rewrite limb_list_bounded_cons_iff;
      repeat split; try lia;
      unfold limb_list_bounded;
      rewrite Zlength_nil in *; lia);
  assert (Hlistvalue :
    u64_list_value (out :: out_2 :: out_3 :: out_4 :: nil) =
    u256_of_limbs out out_2 out_3 out_4) by (
      unfold u64_list_value, u256_of_limbs;
      repeat rewrite limb_list_value_cons;
      rewrite limb_list_value_nil; ring);
  pose proof sm2_n_bounds as [HNpos HNlt];
  pose proof (Z.mod_pos_bound sum SM2_N_Z HNpos) as Hmodrange;
  Exists (out :: out_2 :: out_3 :: out_4 :: nil);
  unfold StructPredu32, UInt64Array.full, store_array;
  cbn [store_array_rec];
  entailer_with ltac:(
    try rewrite Hvalue; try rewrite Htmpmod; try rewrite Hlistvalue;
    try assumption; try lia);
  cbn [u32_v store_array_rec];
  rewrite sizeof_uint64;
  assert (Htmp_addr :
    eval_addr_expr
      (RE_addr_of (LE_arrow_field (RE_addr_of (LE_var "tmp")) "v")) =
    eval_addr_expr
      (RE_addr_of
        (LE_arrow_field
          (RE_const
            (eval_addr_expr (RE_addr_of (LE_var "tmp")))
            (FET_alias "u32"))
          "v"))) by (csimpl; reflexivity);
  rewrite <- Htmp_addr;
  simpl; cancel;
  entailer!.

Lemma add_mod_p_sub_carry_chain :
  forall t0 t1 t2 t3 d0 d1 d2 d3 c1 c2 c3 c4,
    t0 + unsigned_last_nbits (Z.lnot SM2_P_LIMB_0) 64 + 1 =
      d0 + c1 * U64_MOD ->
    t1 + unsigned_last_nbits (Z.lnot SM2_P_LIMB_1) 64 + c1 =
      d1 + c2 * U64_MOD ->
    t2 + unsigned_last_nbits (Z.lnot SM2_P_LIMB_2) 64 + c2 =
      d2 + c3 * U64_MOD ->
    t3 + unsigned_last_nbits (Z.lnot SM2_P_LIMB_3) 64 + c3 =
      d3 + c4 * U64_MOD ->
    u256_of_limbs t0 t1 t2 t3 + U256_MOD - SM2_P_Z =
      u256_of_limbs d0 d1 d2 d3 + c4 * U256_MOD.
Proof.
  intros t0 t1 t2 t3 d0 d1 d2 d3 c1 c2 c3 c4 H0 H1 H2 H3.
  pose proof sm2_p_limbs as (HP0 & HP1 & HP2 & HP3 & _).
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_0 HP0) in H0.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_1 HP1) in H1.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_2 HP2) in H2.
  rewrite (unsigned_lnot_u64 SM2_P_LIMB_3 HP3) in H3.
  cbv [u256_of_limbs U64_MOD U256_MOD SM2_P_Z
       SM2_P_LIMB_0 SM2_P_LIMB_1 SM2_P_LIMB_2 SM2_P_LIMB_3
       U32_MOD] in *.
  lia.
Qed.

Lemma add_mod_p_no_reduction_arithmetic :
  forall A B T D carry borrow,
    0 <= A < SM2_P_Z ->
    0 <= B < SM2_P_Z ->
    0 <= T < U256_MOD ->
    0 <= D < U256_MOD ->
    0 <= carry <= 1 ->
    0 <= borrow <= 1 ->
    A + B = T + carry * U256_MOD ->
    T + U256_MOD - SM2_P_Z = D + borrow * U256_MOD ->
    Z.lor carry borrow = 0 ->
    Zmod (A + B) SM2_P_Z = T /\
    Zmod (A + B) U256_MOD = T.
Proof.
  intros A B T D carry borrow HA HB HT HD Hcarry Hborrow Hadd Hsub Hlor.
  apply Z.lor_eq_0_iff in Hlor.
  destruct Hlor as [-> ->].
  cbn in Hadd.
  rewrite Hadd.
  replace (T + 0) with T by lia.
  split; apply Z.mod_small; lia.
Qed.

Lemma add_mod_p_reduction_arithmetic :
  forall A B T D carry borrow,
    0 <= A < SM2_P_Z ->
    0 <= B < SM2_P_Z ->
    0 <= T < U256_MOD ->
    0 <= D < U256_MOD ->
    0 <= carry <= 1 ->
    0 <= borrow <= 1 ->
    A + B = T + carry * U256_MOD ->
    T + U256_MOD - SM2_P_Z = D + borrow * U256_MOD ->
    Z.lor carry borrow <> 0 ->
    Zmod (A + B) SM2_P_Z = D /\
    Zmod (A + B) U256_MOD = T.
Proof.
  intros A B T D carry borrow HA HB HT HD Hcarry Hborrow Hadd Hsub Hlor.
  assert (Hcarry_cases : carry = 0 \/ carry = 1) by lia.
  assert (Hborrow_cases : borrow = 0 \/ borrow = 1) by lia.
  destruct Hcarry_cases as [-> | ->];
    destruct Hborrow_cases as [-> | ->].
  - exfalso. apply Hlor. reflexivity.
  - split.
    + symmetry. apply Z.mod_unique with (q := 1); [left; lia | lia].
    + symmetry. apply Z.mod_unique with (q := 0); [left; lia | lia].
  - split.
    + symmetry. apply Z.mod_unique with (q := 1); [left; lia | lia].
    + symmetry. apply Z.mod_unique with (q := 1); [left; lia | lia].
  - pose proof sm2_p_montgomery_bounds as Hmodulus.
    exfalso; lia.
Qed.

Ltac finish_add_mod_p_tmp sum out out_2 out_3 out_4 Hvalue Htmpmod :=
  assert (Hbounded :
    u64_list_bounded (out :: out_2 :: out_3 :: out_4 :: nil)) by (
      unfold u64_list_bounded;
      repeat rewrite limb_list_bounded_cons_iff;
      repeat split; try lia;
      unfold limb_list_bounded;
      rewrite Zlength_nil in *; lia);
  assert (Hlistvalue :
    u64_list_value (out :: out_2 :: out_3 :: out_4 :: nil) =
    u256_of_limbs out out_2 out_3 out_4) by (
      unfold u64_list_value, u256_of_limbs;
      repeat rewrite limb_list_value_cons;
      rewrite limb_list_value_nil; ring);
  destruct sm2_p_montgomery_bounds as [[HPpos HPlt] HPhalf];
  pose proof (Z.mod_pos_bound sum SM2_P_Z HPpos) as Hmodrange;
  Exists (out :: out_2 :: out_3 :: out_4 :: nil);
  unfold StructPredu32, UInt64Array.full, store_array;
  cbn [store_array_rec];
  entailer_with ltac:(
    try rewrite Hvalue; try rewrite Htmpmod; try rewrite Hlistvalue;
    try assumption; try lia);
  cbn [u32_v store_array_rec];
  rewrite sizeof_uint64;
  assert (Htmp_addr :
    eval_addr_expr
      (RE_addr_of (LE_arrow_field (RE_addr_of (LE_var "tmp")) "v")) =
    eval_addr_expr
      (RE_addr_of
        (LE_arrow_field
          (RE_const
            (eval_addr_expr (RE_addr_of (LE_var "tmp")))
            (FET_alias "u32"))
          "v"))) by (csimpl; reflexivity);
  rewrite <- Htmp_addr;
  simpl; cancel;
  entailer!.

Ltac solve_add_mod_p_lnot_range limb :=
  left; intros;
  entailer_with ltac:(
    pose proof (unsigned_Lastnbits_range
      (Z.lnot limb) 64 ltac:(lia));
    cbv [U64_MOD] in *; lia).

Ltac solve_u64_bit_range :=
  lazymatch goal with
  | |- context [
      Z.lor (Z.shiftr (unsigned_last_nbits ?lo 64) 32)
        (unsigned_last_nbits
          (Z.shiftl (unsigned_last_nbits ?hi 64) 32) 64)] =>
      pose proof (unsigned_Lastnbits_range lo 64 ltac:(lia)) as Hlo;
      change (0 <= unsigned_last_nbits lo 64 < U64_MOD) in Hlo;
      pose proof (unsigned_Lastnbits_range hi 64 ltac:(lia)) as Hhi;
      change (0 <= unsigned_last_nbits hi 64 < U64_MOD) in Hhi;
      pose proof (u64_join32_range _ _ Hlo Hhi) as Hjoin;
      entailer!
  | |- context [Z.shiftr (unsigned_last_nbits ?x 64) 32] =>
      pose proof (unsigned_Lastnbits_range x 64 ltac:(lia)) as Hinput;
      change (0 <= unsigned_last_nbits x 64 < U64_MOD) in Hinput;
      pose proof (shiftr32_range_u64 _ Hinput) as Hrange;
      unfold U32_MOD in Hrange;
      unfold U64_MOD;
      entailer!
  | |- context [0 <= unsigned_last_nbits ?x 64] =>
      pose proof (unsigned_Lastnbits_range x 64 ltac:(lia)) as Hrange;
      change (0 <= unsigned_last_nbits x 64 < U64_MOD) in Hrange;
      entailer!
  | |- context [unsigned_last_nbits ?x 64 < U64_MOD] =>
      pose proof (unsigned_Lastnbits_range x 64 ltac:(lia)) as Hrange;
      change (0 <= unsigned_last_nbits x 64 < U64_MOD) in Hrange;
      entailer!
  end.

Ltac close_sub_mod_p_unsigned_range :=
  match goal with
  | |- context [unsigned_last_nbits ?x 64] =>
      pose proof (unsigned_Lastnbits_range x 64 ltac:(lia));
      cbv [U64_MOD] in *;
      lia
  end.

Ltac close_sub_mod_p_partial :=
  pre_process;
  try close_sub_mod_p_unsigned_range;
  try (cbv [U64_MOD] in *; lia);
  entailer_with ltac:(
    try close_sub_mod_p_unsigned_range;
    cbv [U64_MOD] in *;
    lia).

Ltac close_sub_mod_p_partial_parent :=
  left; intros;
  entailer_with ltac:(
    try close_sub_mod_p_unsigned_range;
    cbv [U32_MOD U64_MOD SM2_P_LIMB_0 SM2_P_LIMB_1
         SM2_P_LIMB_2 SM2_P_LIMB_3] in *;
    lia).

Ltac close_sub_mod_p_partial_parent_right :=
  right; intros;
  entailer_with ltac:(
    try close_sub_mod_p_unsigned_range;
    cbv [U32_MOD U64_MOD SM2_P_LIMB_0 SM2_P_LIMB_1
         SM2_P_LIMB_2 SM2_P_LIMB_3] in *;
    lia).

Ltac normalize_base0_offsets :=
  repeat match goal with
  | |- context [?base + 0 + ?offset] =>
      replace (base + 0 + offset) with (base + offset) by lia
  end.

Ltac close_sub_mod_p_borrow
    A B a0 a1 a2 a3 b0 b1 b2 b3
    d0 c1 d1 c2 d2 c3 d3 c4
    r0 c5 r1 c6 r2 c7 r3 c8
    Hs0 Hs1 Hs2 Hs3 HB HA Ha1 Ha2 Ha3 :=
  rewrite (unsigned_lnot_u64 b0 ltac:(lia)) in Hs0;
  rewrite (unsigned_lnot_u64 b1 ltac:(lia)) in Hs1;
  rewrite (unsigned_lnot_u64 b2 ltac:(lia)) in Hs2;
  rewrite (unsigned_lnot_u64 b3 ltac:(lia)) in Hs3;
  assert (Hsub :
    A + U256_MOD - B =
      u256_of_limbs d0 d1 d2 d3 + c4 * U256_MOD) by
    (rewrite HA, HB;
     cbv [u256_of_limbs U64_MOD U256_MOD] in *;
     lia);
  pose proof
    (u256_add_carry_chain
      d0 d1 d2 d3
      SM2_P_LIMB_0 SM2_P_LIMB_1 SM2_P_LIMB_2 SM2_P_LIMB_3
      r0 r1 r2 r3 c5 c6 c7 c8
      ltac:(lia) Ha1 Ha2 Ha3) as Hadd;
  pose proof sm2_p_limbs as
    (Hp0 & Hp1 & Hp2 & Hp3 & Hpvalue);
  rewrite <- Hpvalue in Hadd;
  pose proof
    (u256_of_limbs_range d0 d1 d2 d3
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD;
  pose proof
    (u256_of_limbs_range r0 r1 r2 r3
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HR;
  pose proof sm2_p_montgomery_bounds as HPbounds;
  assert (Hlt : A < B) by nia;
  assert (Hcarry : c8 = 1) by nia;
  assert (Hvalue :
    u256_of_limbs r0 r1 r2 r3 = A - B + SM2_P_Z) by nia;
  assert (Hrange :
    0 <= u256_of_limbs r0 r1 r2 r3 < SM2_P_Z) by nia;
  assert (Hmod :
    Zmod (A - B) SM2_P_Z =
      u256_of_limbs r0 r1 r2 r3) by
    (symmetry;
     apply (Zmod_unique
       (A - B) SM2_P_Z (-1)
       (u256_of_limbs r0 r1 r2 r3));
     lia);
  entailer_with ltac:(rewrite Hmod; lia).

Ltac close_sub_mod_p_no_borrow
    A B a0 a1 a2 a3 b0 b1 b2 b3
    d0 c1 d1 c2 d2 c3 d3 c4
    Hs0 Hs1 Hs2 Hs3 HB HA :=
  rewrite (unsigned_lnot_u64 b0 ltac:(lia)) in Hs0;
  rewrite (unsigned_lnot_u64 b1 ltac:(lia)) in Hs1;
  rewrite (unsigned_lnot_u64 b2 ltac:(lia)) in Hs2;
  rewrite (unsigned_lnot_u64 b3 ltac:(lia)) in Hs3;
  assert (Hsub :
    A + U256_MOD - B =
      u256_of_limbs d0 d1 d2 d3 + c4 * U256_MOD) by
    (rewrite HA, HB;
     cbv [u256_of_limbs U64_MOD U256_MOD] in *;
     lia);
  pose proof
    (u256_of_limbs_range d0 d1 d2 d3
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD;
  assert (Hcarry : c4 = 1) by lia;
  assert (Hvalue : u256_of_limbs d0 d1 d2 d3 = A - B) by nia;
  assert (Hrange :
    0 <= u256_of_limbs d0 d1 d2 d3 < SM2_P_Z) by nia;
  assert (Hmod :
    Zmod (A - B) SM2_P_Z = u256_of_limbs d0 d1 d2 d3) by
    (rewrite <- Hvalue; apply Z.mod_small; exact Hrange);
  entailer_with ltac:(rewrite Hmod; lia).

Ltac solve_sub_mod_n_partial :=
  LLM_pre_process ltac:(lia || nia || entailer!);
  match goal with
  | |- context [unsigned_last_nbits (Z.lnot ?x) 64] =>
      pose proof (unsigned_lnot_u64_range x ltac:(lia)) as Hnot
  | _ => idtac
  end;
  entailer_with ltac:(assumption || lia);
  pose proof sm2_n_limbs as HN;
  lia.
