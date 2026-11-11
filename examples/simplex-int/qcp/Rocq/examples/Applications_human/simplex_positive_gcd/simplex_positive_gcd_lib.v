From Coq Require Import ZArith Lia.
Local Open Scope Z_scope.

(* Reference: spec-tool/input-simplex-fme-qcp-foundation-20261101-15/fme/
   QCP_examples/fme.c:45-57 and Rocq/fme_proof_manual.v:8-44.
   FME's recursive gcd assumes 0<a and 0<=b.  Its pure remainder
   equality does not need a>0; the range facts below allow a=0.
   QCP Rocq/SeparationLogic/IntLib.v:12 defines Zgcd as Z.gcd.
   No algorithm or machine state is defined here: use Z.gcd directly. *)

(* Adapted from proof_of_gcd_return_wit_2: commutativity and gcd_rem. *)
Lemma simplex_gcd_rem (a b : Z) :
  b <> 0 -> Z.gcd b (Z.rem a b) = Z.gcd a b.
Proof.
  intros Hb.
  rewrite Z.gcd_comm, Z.gcd_rem by exact Hb.
  apply Z.gcd_comm.
Qed.

(* Adapted from proof_of_gcd_return_wit_1, weakening a>0 to a>=0.
   In particular this also covers the zero-iteration (0,0) case. *)
Lemma simplex_gcd_zero_right (a : Z) :
  0 <= a -> Z.gcd a 0 = a.
Proof. apply Z.gcd_0_r_nonneg. Qed.

Lemma simplex_gcd_zero_left (b : Z) :
  0 <= b -> Z.gcd 0 b = b.
Proof.
  intros Hb. rewrite Z.gcd_comm.
  apply simplex_gcd_zero_right; exact Hb.
Qed.

Lemma simplex_gcd_zero_zero : Z.gcd 0 0 = 0.
Proof. apply simplex_gcd_zero_right; lia. Qed.

(* Adapted from proof_of_gcd_partial_solve_wit_1_pure.
   rem_bound_pos is the supplementary strict bound needed for descent;
   the FME proof uses rem_le and rem_nonneg for representability. *)
Lemma simplex_rem_bounds (a b : Z) :
  0 <= a -> 0 < b -> 0 <= Z.rem a b < b.
Proof.
  intros Ha Hb. apply Z.rem_bound_pos; lia.
Qed.

Lemma simplex_rem_le_dividend (a b : Z) :
  0 <= a -> 0 < b -> Z.rem a b <= a.
Proof.
  intros Ha Hb. apply Z.rem_le; lia.
Qed.

Lemma simplex_rem_preserves_bound (a b M : Z) :
  0 <= a <= M -> 0 < b <= M ->
  0 <= Z.rem a b <= M.
Proof.
  intros Ha Hb.
  pose proof (simplex_rem_bounds a b ltac:(lia) ltac:(lia)).
  lia.
Qed.

(* Pure mathematical exit fact; this is not a C VC proof. *)
Lemma simplex_gcd_exit (A B a : Z) :
  0 <= a -> Z.gcd a 0 = Z.gcd A B -> a = Z.gcd A B.
Proof.
  intros Ha H. rewrite simplex_gcd_zero_right in H by exact Ha.
  exact H.
Qed.

(* Supplement to FME's strictly positive function domain.  This connects
   the target's nonzero-input branch to the positive common-divisor
   characterization in stage3 and candidate item gcd.  All claims are
   proved using the same Z.gcd interface, not the candidate review. *)
Lemma simplex_gcd_positive (a b : Z) :
  0 <= a -> 0 <= b -> (a <> 0 \/ b <> 0) -> 0 < Z.gcd a b.
Proof.
  intros Ha Hb Hnz.
  pose proof (Z.gcd_nonneg a b).
  assert (Z.gcd a b <> 0).
  { intros Hz.
    pose proof (Z.gcd_eq_0_l a b Hz).
    pose proof (Z.gcd_eq_0_r a b Hz).
    tauto. }
  lia.
Qed.

Lemma simplex_gcd_common_divisor (a b : Z) :
  (Z.gcd a b | a) /\ (Z.gcd a b | b).
Proof. split; [apply Z.gcd_divide_l | apply Z.gcd_divide_r]. Qed.

Lemma simplex_gcd_greatest_positive (a b d : Z) :
  0 < Z.gcd a b -> 0 < d -> (d | a) -> (d | b) ->
  d <= Z.gcd a b.
Proof.
  intros Hg Hd Hda Hdb.
  apply Z.divide_pos_le; [exact Hg |].
  apply Z.gcd_greatest; assumption.
Qed.

Lemma simplex_gcd_le_max (a b : Z) :
  0 <= a -> 0 <= b -> Z.gcd a b <= Z.max a b.
Proof.
  intros Ha Hb.
  destruct (Z.eq_dec a 0) as [-> | Hna].
  - rewrite simplex_gcd_zero_left by exact Hb. apply Z.le_max_r.
  - assert (0 < a) by lia.
    assert (Z.gcd a b <= a).
    { apply Z.divide_pos_le; [lia | apply Z.gcd_divide_l]. }
    eapply Z.le_trans; [eassumption | apply Z.le_max_l].
Qed.

Lemma simplex_gcd_int_bound (a b M : Z) :
  0 <= a <= M -> 0 <= b <= M -> 0 <= Z.gcd a b <= M.
Proof.
  intros Ha Hb. split; [apply Z.gcd_nonneg |].
  eapply Z.le_trans.
  - apply simplex_gcd_le_max; lia.
  - apply Z.max_lub; lia.
Qed.
