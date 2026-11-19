From Coq Require Import ZArith Lia String.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.simplex_gmp_minimal
  Require Import integers_fme_model_lib.
From SimpleC.EE.Applications_human.simplex_gmp_optimized
  Require Export build_opt_lib.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* The shared Arch32 dimensions and configured mpz layout entail the
   all_counts preconditions for both row-sized blocks and the whole matrix. *)
Lemma simplex_destroy_release_bounds m n :
  simplex_dimensions_ok m n ->
  (0 < m -> simplex_mpz_layout) ->
  0 <= m <= INT_MAX /\ 0 <= n /\
  0 <= m * (m + n) <= INT_MAX /\
  (0 < m * (m + n) -> simplex_mpz_layout) /\
  0 <= m * sizeof("__mpz_struct") <= INT_MAX /\
  0 <= m * (m + n) * sizeof("__mpz_struct") <= INT_MAX.
Proof.
  intros Hdim Hlayout.
  pose proof (simplex_dimensions_bounds _ _ Hdim) as Hbounds.
  pose proof (simplex_dimensions_mpz_bytes _ _ Hdim Hlayout) as Hbytes.
  unfold simplex_dimensions_ok in Hdim.
  destruct Hdim as (Hm & Hn & Hsum & Hmatrix & Hindices).
  assert (Hpositive : 0 < m * (m + n) -> simplex_mpz_layout).
  { intros Hprod. apply Hlayout. destruct (Z.eq_dec m 0) as [->|Hneq]; lia. }
  destruct Hbounds as (Hcount & Hmbytes & _).
  destruct Hbytes as (Hrowallocated & Htaballocated & _).
  assert (Hrows : 0 <= m <= INT_MAX) by lia.
  exact (conj Hrows (conj Hn (conj Hcount
    (conj Hpositive (conj Hrowallocated Htaballocated))))).
Qed.
