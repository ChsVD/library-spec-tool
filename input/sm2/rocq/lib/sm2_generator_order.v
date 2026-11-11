(** The exact order of the standard SM2 generator. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
From Coqprime Require Import elliptic.ZEll.
Require Import Coqprime.PrimalityTest.EGroup.
From SimpleC.EE.Applications_human.sm2.lib
  Require Import sm2_primality sm2_curve.

Local Open Scope Z_scope.

Definition sm2_generator_raw : ZEll.nelt :=
  ZEll.ntriple SM2_G_X_Z SM2_G_Y_Z 1.

Definition sm2_generator_scal_value : Z :=
  44497532641492592356002640719663837868738291393541708297341146000435441150887.

Definition sm2_generator_scal_inverse : Z :=
  18944598144542067241444533743580499472762223078897670281854777223703001456907.

Lemma sm2_generator_raw_equiv :
  @ZEll.equiv SM2_A_Z SM2_B_Z SM2_P_Z
    sm2_generator_raw SM2_G_POINT.
Proof.
  unfold sm2_generator_raw, SM2_G_POINT, ec_point_of_affine.
  apply ZEll.n_equiv.
  - vm_compute.
    apply GZnZ.zirr.
    reflexivity.
  - vm_compute.
    apply GZnZ.zirr.
    reflexivity.
Qed.

Lemma sm2_raw_equiv_nzero :
  forall raw point,
    raw = ZEll.nzero ->
    @ZEll.equiv SM2_A_Z SM2_B_Z SM2_P_Z raw point ->
    point = ECInfinity.
Proof.
  intros raw point Hraw Hequiv.
  subst raw.
  inversion Hequiv.
  reflexivity.
Qed.

Lemma sm2_generator_scal_certificate :
  ZEll.scal
    SM2_P_Z SM2_A_Z 1 sm2_generator_raw (Z.to_pos SM2_N_Z) =
  (ZEll.nzero, sm2_generator_scal_value).
Proof. vm_compute. reflexivity. Qed.

Lemma sm2_generator_scal_inversible :
  ZEll.nInversible SM2_P_Z
    (ZEll.scal
      SM2_P_Z SM2_A_Z 1 sm2_generator_raw (Z.to_pos SM2_N_Z)).
Proof.
  rewrite sm2_generator_scal_certificate.
  apply ZEll.nInv_z.
  exists sm2_generator_scal_inverse.
  vm_compute.
  reflexivity.
Qed.

Lemma sm2_generator_gpow_order :
  EGroup.gpow SM2_G_POINT sm2_group SM2_N_Z = ECInfinity.
Proof.
  assert (Hscal :
    @ZEll.equiv SM2_A_Z SM2_B_Z SM2_P_Z
      (fst
        (ZEll.scal
          SM2_P_Z SM2_A_Z 1 sm2_generator_raw (Z.to_pos SM2_N_Z)))
      (EGroup.gpow
        SM2_G_POINT sm2_group (Z.pos (Z.to_pos SM2_N_Z)))).
  {
    unfold sm2_group.
    apply ZEll.scal_correct.
    - vm_compute. reflexivity.
    - exact sm2_generator_raw_equiv.
    - exact sm2_generator_scal_inversible.
  }
  assert (Horder_pos :
    EGroup.gpow
      SM2_G_POINT sm2_group (Z.pos (Z.to_pos SM2_N_Z)) =
    ECInfinity).
  {
    eapply sm2_raw_equiv_nzero.
    - exact (f_equal fst sm2_generator_scal_certificate).
    - exact Hscal.
  }
  rewrite Z2Pos.id in Horder_pos by
    (pose proof sm2_n_bounds; lia).
  exact Horder_pos.
Qed.

Lemma sm2_generator_mul_order :
  sm2_point_mul SM2_N_Z SM2_G_POINT = ECInfinity.
Proof.
  unfold sm2_point_mul.
  exact sm2_generator_gpow_order.
Qed.

Lemma sm2_generator_order_value :
  EGroup.e_order sm2_ec_point_dec SM2_G_POINT sm2_group = SM2_N_Z.
Proof.
  apply EGroup.order_div.
  - pose proof sm2_n_bounds. lia.
  - intros divisor Hprime Hdivides.
    assert (divisor = SM2_N_Z) as ->.
    {
      apply prime_div_prime.
      - exact Hprime.
      - exact sm2_n_prime.
      - exact Hdivides.
    }
    rewrite Z.div_same by (pose proof sm2_n_bounds; lia).
    change (sm2_point_mul 1 SM2_G_POINT <> ECInfinity).
    rewrite sm2_point_mul_one.
    exact sm2_g_not_infinity.
  - apply ec_point_in_sm2_group.
  - rewrite sm2_group_identity.
    exact sm2_generator_gpow_order.
Qed.

Lemma sm2_generator_exact_order :
  forall scalar,
    0 < scalar < SM2_N_Z ->
    sm2_point_mul scalar SM2_G_POINT <> ECInfinity.
Proof.
  intros scalar Hscalar.
  pose proof
    (EGroup.gpow_e_order_lt_is_not_e
      ec_point sm2_ec_point_dec sm2_point_add SM2_G_POINT sm2_group
      (ec_point_in_sm2_group SM2_G_POINT)
      scalar) as Hnonzero.
  rewrite sm2_generator_order_value in Hnonzero.
  specialize (Hnonzero ltac:(lia)).
  rewrite sm2_group_identity in Hnonzero.
  exact Hnonzero.
Qed.

Lemma sm2_generator_mul_injective :
  forall left right,
    0 <= left < SM2_N_Z ->
    0 <= right < SM2_N_Z ->
    sm2_point_mul left SM2_G_POINT =
    sm2_point_mul right SM2_G_POINT ->
    left = right.
Proof.
  intros left right Hleft Hright Heq.
  destruct (Z_le_gt_dec left right) as [Hle | Hgt].
  - destruct (Z.eq_dec left right) as [-> | Hne]; [reflexivity |].
    exfalso.
    apply (sm2_generator_exact_order (right - left)); [lia |].
    unfold sm2_point_mul in *.
    eapply EGroup.gpow_i with (n := left) (m := right - left).
    + apply ec_point_in_sm2_group.
    + lia.
    + lia.
    + replace (left + (right - left)) with right by lia.
      exact Heq.
  - exfalso.
    apply (sm2_generator_exact_order (left - right)); [lia |].
    unfold sm2_point_mul in *.
    eapply EGroup.gpow_i with (n := right) (m := left - right).
    + apply ec_point_in_sm2_group.
    + lia.
    + lia.
    + replace (right + (left - right)) with left by lia.
      symmetry.
      exact Heq.
Qed.
