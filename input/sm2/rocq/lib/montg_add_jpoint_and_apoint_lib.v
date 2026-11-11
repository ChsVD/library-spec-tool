Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
From SimpleC.EE.Applications_human.sm2.lib Require Import
  add_JPoint_lib ec_math_refinement.

Local Open Scope Z_scope.

(** Stable names for the straight-line Montgomery mixed-add trace. *)
Definition maja_z2 (z1 : Z) : Z := (z1 * z1) mod SM2_P_Z.
Definition maja_u2 (x2 z1 : Z) : Z :=
  (x2 * maja_z2 z1) mod SM2_P_Z.
Definition maja_z3 (z1 : Z) : Z :=
  (z1 * maja_z2 z1) mod SM2_P_Z.
Definition maja_s2 (y2 z1 : Z) : Z :=
  (y2 * maja_z3 z1) mod SM2_P_Z.
Definition maja_h (x1 x2 z1 : Z) : Z :=
  (maja_u2 x2 z1 - x1) mod SM2_P_Z.
Definition maja_r (y1 y2 z1 : Z) : Z :=
  (maja_s2 y2 z1 - y1) mod SM2_P_Z.
Definition maja_h2 (x1 x2 z1 : Z) : Z :=
  (maja_h x1 x2 z1 * maja_h x1 x2 z1) mod SM2_P_Z.
Definition maja_h3 (x1 x2 z1 : Z) : Z :=
  (maja_h x1 x2 z1 * maja_h2 x1 x2 z1) mod SM2_P_Z.
Definition maja_u1h2 (x1 x2 z1 : Z) : Z :=
  (x1 * maja_h2 x1 x2 z1) mod SM2_P_Z.
Definition maja_two_u1h2 (x1 x2 z1 : Z) : Z :=
  (2 * maja_u1h2 x1 x2 z1) mod SM2_P_Z.
Definition maja_x_adjust (x1 x2 z1 : Z) : Z :=
  (maja_h3 x1 x2 z1 + maja_two_u1h2 x1 x2 z1) mod SM2_P_Z.
Definition maja_r2 (y1 y2 z1 : Z) : Z :=
  (maja_r y1 y2 z1 * maja_r y1 y2 z1) mod SM2_P_Z.
Definition maja_rx (x1 y1 z1 x2 y2 : Z) : Z :=
  (maja_r2 y1 y2 z1 - maja_x_adjust x1 x2 z1) mod SM2_P_Z.
Definition maja_e_minus_rx (x1 y1 z1 x2 y2 : Z) : Z :=
  (maja_u1h2 x1 x2 z1 - maja_rx x1 y1 z1 x2 y2) mod SM2_P_Z.
Definition maja_r_times_delta (x1 y1 z1 x2 y2 : Z) : Z :=
  (maja_r y1 y2 z1 * maja_e_minus_rx x1 y1 z1 x2 y2)
    mod SM2_P_Z.
Definition maja_y1h3 (x1 y1 x2 z1 : Z) : Z :=
  (y1 * maja_h3 x1 x2 z1) mod SM2_P_Z.
Definition maja_ry (x1 y1 z1 x2 y2 : Z) : Z :=
  (maja_r_times_delta x1 y1 z1 x2 y2 - maja_y1h3 x1 y1 x2 z1)
    mod SM2_P_Z.
Definition maja_rz (x1 x2 z1 : Z) : Z :=
  (z1 * maja_h x1 x2 z1) mod SM2_P_Z.

Lemma maja_mod_range : forall value,
  0 <= value mod SM2_P_Z < SM2_P_Z.
Proof.
  intros value.
  apply Z.mod_pos_bound.
  pose proof sm2_p_gt_one.
  lia.
Qed.

Lemma maja_afpoint_as_jpoint_one :
  forall x y point,
    point <> ECInfinity ->
    afpoint_represents x y point ->
    jpoint_represents x y 1 point.
Proof.
  intros x y point Hfinite Haffine.
  eapply afpoint_to_jpoint_coordinates_represents.
  - exact Haffine.
  - right.
    split.
    + right.
      eapply afpoint_represents_noninfinity_y_nonzero; eauto.
    + repeat split.
Qed.

Lemma maja_aj_qz2_one : aj_qz2 1 = 1.
Proof.
  unfold aj_qz2.
  rewrite Z.mul_1_l.
  apply Z.mod_small.
  pose proof sm2_p_gt_one.
  lia.
Qed.

Lemma maja_aj_qz3_one : aj_qz3 1 = 1.
Proof.
  unfold aj_qz3.
  rewrite maja_aj_qz2_one, Z.mul_1_l.
  apply Z.mod_small.
  pose proof sm2_p_gt_one.
  lia.
Qed.

Lemma maja_aj_u1_one : forall x,
  0 <= x < SM2_P_Z -> aj_u1 x 1 = x.
Proof.
  intros x Hx.
  unfold aj_u1.
  rewrite maja_aj_qz2_one, Z.mul_1_r.
  now apply Z.mod_small.
Qed.

Lemma maja_aj_s1_one : forall y,
  0 <= y < SM2_P_Z -> aj_s1 y 1 = y.
Proof.
  intros y Hy.
  unfold aj_s1.
  rewrite maja_aj_qz3_one, Z.mul_1_r.
  now apply Z.mod_small.
Qed.

Lemma maja_aj_u2_mixed : forall x z,
  aj_u2 x z = maja_u2 x z.
Proof. reflexivity. Qed.

Lemma maja_aj_s2_mixed : forall y z,
  aj_s2 y z = maja_s2 y z.
Proof.
  intros y z.
  unfold aj_s2, aj_pz3, aj_pz2, maja_s2, maja_z3, maja_z2.
  rewrite (Z.mul_comm ((z * z) mod SM2_P_Z) z).
  reflexivity.
Qed.

Lemma maja_h_zero_scaled_x :
  forall x1 x2 z1,
    0 <= x1 < SM2_P_Z ->
    maja_h x1 x2 z1 = 0 ->
    aj_u1 x1 1 = aj_u2 x2 z1.
Proof.
  intros x1 x2 z1 Hx1 Hh.
  rewrite maja_aj_u1_one by exact Hx1.
  rewrite maja_aj_u2_mixed.
  symmetry.
  rewrite <- (Z.mod_small x1 SM2_P_Z Hx1).
  apply (sm2_eqm_canonical_left
    (maja_u2 x2 z1) x1).
  - unfold maja_u2; apply maja_mod_range.
  - apply (proj2 (sm2_eqm_iff_sub_mod_zero _ _)).
    exact Hh.
Qed.

Lemma maja_r_zero_scaled_y :
  forall y1 y2 z1,
    0 <= y1 < SM2_P_Z ->
    maja_r y1 y2 z1 = 0 ->
    aj_s1 y1 1 = aj_s2 y2 z1.
Proof.
  intros y1 y2 z1 Hy1 Hr.
  rewrite maja_aj_s1_one by exact Hy1.
  rewrite maja_aj_s2_mixed.
  symmetry.
  rewrite <- (Z.mod_small y1 SM2_P_Z Hy1).
  apply (sm2_eqm_canonical_left
    (maja_s2 y2 z1) y1).
  - unfold maja_s2; apply maja_mod_range.
  - apply (proj2 (sm2_eqm_iff_sub_mod_zero _ _)).
    exact Hr.
Qed.

Lemma maja_r_nonzero_scaled_y :
  forall y1 y2 z1,
    0 <= y1 < SM2_P_Z ->
    maja_r y1 y2 z1 <> 0 ->
    aj_s1 y1 1 <> aj_s2 y2 z1.
Proof.
  intros y1 y2 z1 Hy1 Hr Hequal.
  apply Hr.
  unfold maja_r.
  rewrite <- maja_aj_s2_mixed, <- Hequal.
  rewrite maja_aj_s1_one by exact Hy1.
  rewrite Z.sub_diag, Z.mod_0_l.
  - reflexivity.
  - pose proof sm2_p_gt_one; lia.
Qed.

Lemma maja_equal_points :
  forall x1 y1 z1 x2 y2 left right,
    left <> ECInfinity ->
    right <> ECInfinity ->
    jpoint_represents x1 y1 z1 left ->
    afpoint_represents x2 y2 right ->
    maja_h x1 x2 z1 = 0 ->
    maja_r y1 y2 z1 = 0 ->
    left = right.
Proof.
  intros x1 y1 z1 x2 y2 left right
    Hleft Hright HJ HA Hh Hr.
  pose proof HJ as HJbounds.
  destruct HJbounds as [Hx1 [Hy1 [Hz1 _]]].
  assert (Hz1_nonzero : z1 <> 0).
  { intros Hz1_zero.
    apply Hleft.
    apply (proj1 (jpoint_represents_infinity_iff
      x1 y1 z1 left HJ)).
    exact Hz1_zero. }
  pose proof (maja_afpoint_as_jpoint_one x2 y2 right Hright HA) as HQ.
  eapply aj_same_u_same_s_points_equal; eauto.
  - lia.
  - now apply maja_h_zero_scaled_x.
  - now apply maja_r_zero_scaled_y.
Qed.

Lemma maja_inverse_points_add_infinity :
  forall x1 y1 z1 x2 y2 left right,
    left <> ECInfinity ->
    right <> ECInfinity ->
    jpoint_represents x1 y1 z1 left ->
    afpoint_represents x2 y2 right ->
    maja_h x1 x2 z1 = 0 ->
    maja_r y1 y2 z1 <> 0 ->
    sm2_point_add left right = ECInfinity.
Proof.
  intros x1 y1 z1 x2 y2 left right
    Hleft Hright HJ HA Hh Hr.
  pose proof HJ as HJbounds.
  destruct HJbounds as [Hx1 [Hy1 [Hz1 _]]].
  assert (Hz1_nonzero : z1 <> 0).
  { intros Hz1_zero.
    apply Hleft.
    apply (proj1 (jpoint_represents_infinity_iff
      x1 y1 z1 left HJ)).
    exact Hz1_zero. }
  pose proof (maja_afpoint_as_jpoint_one x2 y2 right Hright HA) as HQ.
  assert (Hu : aj_u1 x1 1 = aj_u2 x2 z1).
  { now apply maja_h_zero_scaled_x. }
  assert (Hs : aj_s1 y1 1 <> aj_s2 y2 z1).
  { now apply maja_r_nonzero_scaled_y. }
  pose proof (aj_same_u_different_s_implies_s_sum_zero
    x1 y1 z1 x2 y2 1 left right HJ HQ Hz1_nonzero ltac:(lia) Hu Hs)
    as Hsum.
  eapply aj_same_u_s_sum_zero_adds_infinity; eauto; lia.
Qed.

Lemma maja_h_zero_for_same_point :
  forall x1 y1 z1 x2 y2 point,
    point <> ECInfinity ->
    jpoint_represents x1 y1 z1 point ->
    afpoint_represents x2 y2 point ->
    maja_h x1 x2 z1 = 0.
Proof.
  intros x1 y1 z1 x2 y2 point Hfinite HJ HA.
  destruct point as [|point_x point_y Hcurve].
  { contradiction. }
  cbn [jpoint_represents] in HJ.
  cbn [afpoint_represents] in HA.
  destruct HJ as [Hx1 [Hy1 [Hz1 [Hz1_nonzero [HJx HJy]]]]].
  destruct HA as [Hx2 Hy2].
  subst x2 y2.
  unfold maja_h, maja_u2, maja_z2.
  rewrite HJx.
  rewrite Z.mul_mod_idemp_r by (pose proof sm2_p_gt_one; lia).
  replace (z1 * z1) with (z1 ^ 2) by ring.
  rewrite Z.sub_diag, Z.mod_0_l.
  - reflexivity.
  - pose proof sm2_p_gt_one; lia.
Qed.

Lemma maja_generic_formula_represents :
  forall x1 y1 z1 x2 y2 left right,
    left <> ECInfinity ->
    right <> ECInfinity ->
    jpoint_represents x1 y1 z1 left ->
    afpoint_represents x2 y2 right ->
    maja_h x1 x2 z1 <> 0 ->
    jpoint_represents
      (maja_rx x1 y1 z1 x2 y2)
      (maja_ry x1 y1 z1 x2 y2)
      (maja_rz x1 x2 z1)
      (sm2_point_add left right).
Proof.
  intros x1 y1 z1 x2 y2 left right
    Hleft Hright HJ HA Hh.
  assert (Hdistinct : left <> right).
  { intros Hequal.
    apply Hh.
    rewrite <- Hequal in HA.
    exact (maja_h_zero_for_same_point
      x1 y1 z1 x2 y2 left Hleft HJ HA). }
  eapply (jpoint_add_afpoint_mixed_mod_represents
    left right x1 y1 z1 x2 y2
    (maja_z2 z1) (maja_h x1 x2 z1) (maja_r y1 y2 z1)
    (maja_h2 x1 x2 z1) (maja_h3 x1 x2 z1)
    (maja_u1h2 x1 x2 z1) (maja_r2 y1 y2 z1)
    (maja_two_u1h2 x1 x2 z1)
    (maja_rx x1 y1 z1 x2 y2)
    (maja_e_minus_rx x1 y1 z1 x2 y2)
    (maja_ry x1 y1 z1 x2 y2)
    (maja_rz x1 x2 z1)).
  all: try assumption.
  all: try (unfold maja_h, maja_rx, maja_ry, maja_rz;
            apply maja_mod_range).
  - reflexivity.
  - reflexivity.
  - unfold maja_r, maja_s2, maja_z3.
    f_equal.
    f_equal.
    rewrite Z.mul_mod_idemp_r by (pose proof sm2_p_gt_one; lia).
    rewrite Z.mul_mod_idemp_l by (pose proof sm2_p_gt_one; lia).
    f_equal; ring.
  - reflexivity.
  - unfold maja_h3; f_equal; ring.
  - reflexivity.
  - reflexivity.
  - unfold maja_two_u1h2; f_equal; ring.
  - unfold maja_rx, maja_x_adjust.
    apply (congr_mod_eq_canonical SM2_P_Z);
      try (pose proof sm2_p_gt_one; lia);
      try apply maja_mod_range.
    eapply congr_mod_trans.
    + apply aj_mod_congr.
    + eapply congr_mod_trans with
        (b := maja_r2 y1 y2 z1 -
          (maja_h3 x1 x2 z1 + maja_two_u1h2 x1 x2 z1)).
      * apply congr_mod_sub;
          [apply congr_mod_refl | apply aj_mod_congr].
      * eapply congr_mod_trans with
          (b := (maja_r2 y1 y2 z1 -
                 maja_two_u1h2 x1 x2 z1) -
                maja_h3 x1 x2 z1).
        -- replace
             (maja_r2 y1 y2 z1 -
              (maja_h3 x1 x2 z1 + maja_two_u1h2 x1 x2 z1))
             with
             ((maja_r2 y1 y2 z1 - maja_two_u1h2 x1 x2 z1) -
              maja_h3 x1 x2 z1) by ring.
           apply congr_mod_refl.
        -- apply congr_mod_sym.
           eapply congr_mod_trans.
           ++ apply aj_mod_congr.
           ++ apply congr_mod_sub;
                [apply aj_mod_congr | apply congr_mod_refl].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
