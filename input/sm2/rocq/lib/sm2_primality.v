Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.micromega.Lia.
From Coqprime Require Import PocklingtonRefl.
Require Import Coqprime.PrimalityTest.Zp.
Require Import Coqprime.PrimalityTest.Euler.
From SimpleC.EE.Applications_human.sm2.lib
  Require Import sm2_common_lib.

Local Open Scope positive_scope.

(**
 * Primality certificates for the SM2 field modulus and group order.
 *
 * The certificate lemmas are local.  Clients use [sm2_p_prime],
 * [sm2_n_prime], and the two nonzero-coprimality corollaries below.
 *)

(** * Certificate verification *)

Local Lemma sm2_p_literal_prime :
  prime 115792089210356248756420345214020892766250353991924191454421193933289684991999.
Proof.
  apply (Pocklington_refl
    (Pock_certif
      115792089210356248756420345214020892766250353991924191454421193933289684991999
      13
      ((66013261729388519804782124120027, 1) :: (2, 1) :: nil)
      110458666826769989534441368410108)
    ((Pock_certif
       66013261729388519804782124120027
       2
       ((4773264379806847, 1) :: (2, 1) :: nil)
       1) ::
     (Pock_certif
       4773264379806847
       3
       ((363761, 1) :: (2, 1) :: nil)
       196346) ::
     (Pock_certif
       363761
       3
       ((4547, 1) :: (5, 1) :: (2, 4) :: nil)
       1) ::
     (Proof_certif 4547 prime4547) ::
     (Proof_certif 5 prime5) ::
     (Proof_certif 2 prime2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Local Lemma sm2_n_literal_prime :
  prime 115792089210356248756420345214020892766061623724957744567843809356293439045923.
Proof.
  apply (Pocklington_refl
    (Pock_certif
      115792089210356248756420345214020892766061623724957744567843809356293439045923
      2
      ((125197554539772723432468576818475380947471091418362477724521, 1) ::
       (2, 1) :: nil)
      1)
    ((Pock_certif
       125197554539772723432468576818475380947471091418362477724521
       3
       ((18120927127286907576013935251791662753637, 1) ::
        (2, 3) :: nil)
       1) ::
     (Pock_certif
       18120927127286907576013935251791662753637
       2
       ((101456283590983, 1) :: (2, 2) :: nil)
       337674284848774) ::
     (Pock_certif
       101456283590983
       3
       ((5636460199499, 1) :: (2, 1) :: nil)
       1) ::
     (Pock_certif
       5636460199499
       2
       ((9061163, 1) :: (127, 1) :: (79, 1) :: (31, 1) :: (2, 1) :: nil)
       1) ::
     (Pock_certif
       9061163
       2
       ((5801, 1) :: (71, 1) :: (11, 1) :: (2, 1) :: nil)
       1) ::
     (Proof_certif 5801 prime5801) ::
     (Proof_certif 127 prime127) ::
     (Proof_certif 79 prime79) ::
     (Proof_certif 71 prime71) ::
     (Proof_certif 31 prime31) ::
     (Proof_certif 11 prime11) ::
     (Proof_certif 2 prime2) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

Local Open Scope Z_scope.

(** * Public SM2 primality facts *)

Lemma sm2_p_prime : prime SM2_P_Z.
Proof.
  unfold SM2_P_Z.
  exact sm2_p_literal_prime.
Qed.

Lemma sm2_n_prime : prime SM2_N_Z.
Proof.
  unfold SM2_N_Z, SM2_N0_Z, SM2_N1_Z, SM2_N2_Z, SM2_N3_Z,
    u256_of_limbs, U64_MOD, U32_MOD.
  exact sm2_n_literal_prime.
Qed.

Lemma sm2_p_fermat :
  forall x, x ^ SM2_P_Z mod SM2_P_Z = x mod SM2_P_Z.
Proof.
  intros x.
  rewrite Zpower_mod by (pose proof sm2_p_montgomery_bounds; lia).
  set (r := x mod SM2_P_Z).
  destruct (Z.eq_dec r 0) as [Hr | Hr].
  - rewrite Hr. simpl. reflexivity.
  - assert (Hr_bounds : 0 <= r < SM2_P_Z).
    { subst r. apply Z.mod_pos_bound.
      pose proof sm2_p_montgomery_bounds. lia. }
    assert (Hrel : rel_prime r SM2_P_Z).
    { apply rel_prime_le_prime.
      - exact sm2_p_prime.
      - lia. }
    assert (Hp_gt_one : 1 < SM2_P_Z).
    { pose proof sm2_p_montgomery_bounds. lia. }
    pose proof
      (phi_power_is_1 r SM2_P_Z Hp_gt_one Hrel) as Hpow.
    rewrite (prime_phi_n_minus_1 SM2_P_Z sm2_p_prime) in Hpow.
    replace SM2_P_Z with (1 + (SM2_P_Z - 1)) by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r.
    rewrite Z.mul_mod by (pose proof sm2_p_montgomery_bounds; lia).
    replace (1 + (SM2_P_Z - 1)) with SM2_P_Z by lia.
    rewrite Hpow.
    assert (Hrmod : r mod SM2_P_Z = r).
    { apply Z.mod_small. exact Hr_bounds. }
    rewrite Hrmod, Z.mul_1_r.
    exact Hrmod.
Qed.

Lemma sm2_p_nonzero_gcd_one :
  forall a,
    0 <= a < SM2_P_Z ->
    a <> 0 ->
    Z.gcd a SM2_P_Z = 1.
Proof.
  intros a Ha Ha0.
  apply Zgcd_1_rel_prime.
  apply rel_prime_le_prime.
  - exact sm2_p_prime.
  - lia.
Qed.

Lemma sm2_n_nonzero_gcd_one :
  forall a,
    0 <= a < SM2_N_Z ->
    a <> 0 ->
    Z.gcd a SM2_N_Z = 1.
Proof.
  intros a Ha Ha0.
  apply Zgcd_1_rel_prime.
  apply rel_prime_le_prime.
  - exact sm2_n_prime.
  - lia.
Qed.
