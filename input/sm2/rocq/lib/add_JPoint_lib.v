Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Import Snaive_C_Rules.
From SimpleC.EE.Applications_human.sm2.lib Require Export ecc.
From SimpleC.EE.Applications_human.sm2.lib Require Import ec_math_refinement.
From SimpleC.EE.Applications_human.sm2.lib Require Import fieldOp_lib.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.

(** Keep the negative canonical-infinity test opaque during symbolic
    execution.  Expanding it into three disjunctive inequalities duplicates
    every downstream path; proofs may unfold it locally when needed. *)
Definition aj_noncanonical_infinity (x y z : Z) : Prop :=
  ~ canonical_jpoint_infinity x y z.

Lemma aj_noncanonical_encoded_is_finite :
  forall x y z P,
    aj_noncanonical_infinity x y z ->
    jpoint_represents x y z P ->
    jpoint_canonical_infinity_encoding x y z P ->
    z <> 0.
Proof.
  intros x y z P Hnoncanonical Hrep Hencoding Hz.
  apply Hnoncanonical.
  apply Hencoding.
  subst z.
  now apply (jpoint_represents_z0_only_infinity x y P).
Qed.

(** Internal ownership bridge used after a generated four-limb result has
    been reassembled.  The field name remains parametric, so this is one
    memory-model lemma rather than one rule per coordinate or algorithm. *)
Lemma aj_jpoint_field_limbs_pack :
  forall address field x,
    0 <= x < SM2_P_Z ->
    store_u256_limbs (&(address # "JPoint" ->ₛ field .ₛ "v")) x |--
    store_fp (&(address # "JPoint" ->ₛ field)) x.
Proof.
  intros address field x Hx.
  unfold store_fp, store_mod, store_u256.
  entailer!; csimpl; entailer!.
Qed.

Lemma aj_global_jpoint_field_limbs_pack :
  forall field x,
    0 <= x < SM2_P_Z ->
    store_u256_limbs (&(( &( "JPoint_ZERO" ) )->ₛ field .ₛ "v")) x |--
    store_fp (&(( &( "JPoint_ZERO" ) )->ₛ field)) x.
Proof.
  intros field x Hx.
  unfold store_fp, store_mod, store_u256.
  entailer!; csimpl; entailer!.
Qed.

Lemma aj_store_jpoint_fields_fold :
  forall address x y z P,
    jpoint_represents x y z P ->
    store_jpoint_fields address x y z |-- store_jpoint address P.
Proof.
  intros address x y z P Hrep.
  unfold store_jpoint.
  Exists x y z.
  entailer!.
Qed.

Lemma aj_store_jpoint_fields_fold_canonical :
  forall address x y z P,
    jpoint_represents x y z P ->
    jpoint_canonical_infinity_encoding x y z P ->
    store_jpoint_fields address x y z |--
    store_jpoint_with_canonical_infinity address P.
Proof.
  intros address x y z P Hrep Hencoding.
  unfold store_jpoint_with_canonical_infinity.
  Exists x y z.
  entailer!.
Qed.

(** Aggregate-copy bridge for the non-alias early-return branches.  It says
    only that two complete four-limb copies realize the same three field
    values; point-addition semantics remains outside this memory lemma. *)
Lemma aj_copy_full_lists_to_two_jpoint_fields :
  forall destination source xs ys zs x y z,
    u64_list_value xs = x ->
    u64_list_value ys = y ->
    u64_list_value zs = z ->
    0 <= x < SM2_P_Z ->
    0 <= y < SM2_P_Z ->
    0 <= z < SM2_P_Z ->
    UInt64Array.full (&(destination # "JPoint" ->ₛ "z" .ₛ "v")) 4 zs **
    UInt64Array.full (&(source # "JPoint" ->ₛ "z" .ₛ "v")) 4 zs **
    UInt64Array.full (&(destination # "JPoint" ->ₛ "y" .ₛ "v")) 4 ys **
    UInt64Array.full (&(source # "JPoint" ->ₛ "y" .ₛ "v")) 4 ys **
    UInt64Array.full (&(destination # "JPoint" ->ₛ "x" .ₛ "v")) 4 xs **
    UInt64Array.full (&(source # "JPoint" ->ₛ "x" .ₛ "v")) 4 xs |--
    store_jpoint_fields source x y z **
    store_jpoint_fields destination x y z.
Proof.
  intros destination source xs ys zs x y z Hxv Hyv Hzv Hx Hy Hz.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  rewrite Hxv, Hyv, Hzv.
  sep_apply (aj_jpoint_field_limbs_pack destination "x" x Hx).
  sep_apply (aj_jpoint_field_limbs_pack destination "y" y Hy).
  sep_apply (aj_jpoint_field_limbs_pack destination "z" z Hz).
  sep_apply (aj_jpoint_field_limbs_pack source "x" x Hx).
  sep_apply (aj_jpoint_field_limbs_pack source "y" y Hy).
  sep_apply (aj_jpoint_field_limbs_pack source "z" z Hz).
  unfold store_jpoint_fields.
  entailer!.
Qed.

Local Opaque SM2_P_Z SM2_A_Z SM2_B_Z.

Lemma aj_sm2_point_on_curve_equation :
  forall x y,
    sm2_affine_on_curve x y ->
    (y * y) mod SM2_P_Z =
    (x * x * x + SM2_A_Z * x + SM2_B_Z) mod SM2_P_Z.
Proof.
  intros x y Hcurve.
  apply (proj1 (sm2_affine_equation_iff x y)).
  exact (proj2 (proj2 Hcurve)).
Qed.

Local Transparent SM2_P_Z SM2_A_Z SM2_B_Z.

(** Private logical trace for [add_JPoint].  These definitions connect leaf
    contracts to the internal coordinate relation and are not public API. *)
Definition aj_pz2 (z1 : Z) : Z := (z1 * z1) mod SM2_P_Z.
Definition aj_qz2 (z2 : Z) : Z := (z2 * z2) mod SM2_P_Z.
Definition aj_pz3 (z1 : Z) : Z := (aj_pz2 z1 * z1) mod SM2_P_Z.
Definition aj_qz3 (z2 : Z) : Z := (aj_qz2 z2 * z2) mod SM2_P_Z.
Definition aj_u1 (x1 z2 : Z) : Z := (x1 * aj_qz2 z2) mod SM2_P_Z.
Definition aj_u2 (x2 z1 : Z) : Z := (x2 * aj_pz2 z1) mod SM2_P_Z.
Definition aj_s1 (y1 z2 : Z) : Z := (y1 * aj_qz3 z2) mod SM2_P_Z.
Definition aj_s2 (y2 z1 : Z) : Z := (y2 * aj_pz3 z1) mod SM2_P_Z.
Definition aj_s_sum (y1 z1 y2 z2 : Z) : Z :=
  (aj_s1 y1 z2 + aj_s2 y2 z1) mod SM2_P_Z.
Definition aj_h (x1 z1 x2 z2 : Z) : Z :=
  (aj_u1 x1 z2 - aj_u2 x2 z1) mod SM2_P_Z.
Definition aj_rr (y1 z1 y2 z2 : Z) : Z :=
  (aj_s1 y1 z2 - aj_s2 y2 z1) mod SM2_P_Z.
Definition aj_u_sum (x1 z1 x2 z2 : Z) : Z :=
  (aj_u1 x1 z2 + aj_u2 x2 z1) mod SM2_P_Z.
Definition aj_rr2 (y1 z1 y2 z2 : Z) : Z :=
  (aj_rr y1 z1 y2 z2 * aj_rr y1 z1 y2 z2) mod SM2_P_Z.
Definition aj_h2 (x1 z1 x2 z2 : Z) : Z :=
  (aj_h x1 z1 x2 z2 * aj_h x1 z1 x2 z2) mod SM2_P_Z.
Definition aj_base (x1 z1 x2 z2 : Z) : Z :=
  (aj_u_sum x1 z1 x2 z2 * aj_h2 x1 z1 x2 z2) mod SM2_P_Z.
Definition aj_rx (x1 y1 z1 x2 y2 z2 : Z) : Z :=
  (aj_rr2 y1 z1 y2 z2 - aj_base x1 z1 x2 z2) mod SM2_P_Z.
Definition aj_twice_rx (x1 y1 z1 x2 y2 z2 : Z) : Z :=
  (2 * aj_rx x1 y1 z1 x2 y2 z2) mod SM2_P_Z.
Definition aj_base_minus_twice_rx (x1 y1 z1 x2 y2 z2 : Z) : Z :=
  (aj_base x1 z1 x2 z2 - aj_twice_rx x1 y1 z1 x2 y2 z2) mod SM2_P_Z.
Definition aj_left_y (x1 y1 z1 x2 y2 z2 : Z) : Z :=
  (aj_base_minus_twice_rx x1 y1 z1 x2 y2 z2 *
   aj_rr y1 z1 y2 z2) mod SM2_P_Z.
Definition aj_right_y (x1 y1 z1 x2 y2 z2 : Z) : Z :=
  ((aj_s_sum y1 z1 y2 z2 * aj_h2 x1 z1 x2 z2) *
   aj_h x1 z1 x2 z2) mod SM2_P_Z.
Definition aj_y_num (x1 y1 z1 x2 y2 z2 : Z) : Z :=
  (aj_left_y x1 y1 z1 x2 y2 z2 -
   aj_right_y x1 y1 z1 x2 y2 z2) mod SM2_P_Z.
Definition aj_ry (x1 y1 z1 x2 y2 z2 : Z) : Z :=
  (aj_y_num x1 y1 z1 x2 y2 z2 * SM2_P_INV2_Z) mod SM2_P_Z.
Definition aj_zbase (z1 z2 : Z) : Z := (z1 * z2) mod SM2_P_Z.
Definition aj_rz (x1 z1 x2 z2 : Z) : Z :=
  (aj_zbase z1 z2 * aj_h x1 z1 x2 z2) mod SM2_P_Z.

(** Pure boundary between the implementation trace and the public curve-point
    semantics.  Its proof is case-local; callers see only [sm2_point_add]. *)
Definition aj_result_refines
    (P1 P2 : ec_point) (x1 y1 z1 x2 y2 z2 : Z) : Prop :=
  jpoint_represents
    (aj_rx x1 y1 z1 x2 y2 z2)
    (aj_ry x1 y1 z1 x2 y2 z2)
    (aj_rz x1 z1 x2 z2) (sm2_point_add P1 P2) /\
  jpoint_canonical_infinity_encoding
    (aj_rx x1 y1 z1 x2 y2 z2)
    (aj_ry x1 y1 z1 x2 y2 z2)
    (aj_rz x1 z1 x2 z2) (sm2_point_add P1 P2).

Definition aj_generic_trace_case
    (x1 y1 z1 x2 y2 z2 : Z) : Prop :=
  aj_u1 x1 z2 <> aj_u2 x2 z1 \/
  (aj_u1 x1 z2 = aj_u2 x2 z1 /\
   aj_s1 y1 z2 <> aj_s2 y2 z1 /\
   aj_s_sum y1 z1 y2 z2 <> 0).


(** Cancellation where the nonzero factor is not assumed canonical.  The
    implementation trace naturally produces differences before reducing
    them; canonicalization is therefore kept inside this pure field lemma. *)
Lemma aj_congr_mod_cancel_nonzero_right_raw :
  forall a b c,
    ~ congr_mod SM2_P_Z c 0 ->
    congr_mod SM2_P_Z (a * c) (b * c) ->
    congr_mod SM2_P_Z a b.
Proof.
  intros a b c Hc Habc.
  assert (Hp : SM2_P_Z <> 0)
    by (pose proof sm2_p_montgomery_bounds; lia).
  set (cm := c mod SM2_P_Z).
  assert (Hcm_range : 0 <= cm < SM2_P_Z).
  { unfold cm. apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds; lia. }
  assert (Hcm0 : cm <> 0).
  { intro Hzero; apply Hc.
    apply congr_mod_of_mod_eq; [exact Hp|].
    unfold cm in Hzero.
    rewrite Hzero, Z.mod_0_l by exact Hp.
    reflexivity. }
  assert (Hc_cm : congr_mod SM2_P_Z c cm).
  { unfold cm. apply congr_mod_sym, congr_mod_mod; exact Hp. }
  apply (sm2_congr_mod_cancel_nonzero_right a b cm Hcm_range Hcm0).
  eapply congr_mod_trans.
  - apply congr_mod_mul; [apply congr_mod_refl|].
    apply congr_mod_sym; exact Hc_cm.
  - eapply congr_mod_trans; [exact Habc|].
    apply congr_mod_mul; [apply congr_mod_refl|].
    exact Hc_cm.
Qed.

Definition aj_secant_k (x1 y1 x2 lambda : Z) : Z :=
  SM2_A_Z + lambda * lambda * x1 - lambda * lambda * x2 -
  2 * lambda * y1 + x1 * x1 + x1 * x2 + x2 * x2.

Lemma aj_move_sub_eq : forall a b c : Z, a - b = c -> a = b + c.
Proof. intros; lia. Qed.

Lemma aj_secant_factor_identity :
  forall A B x1 y1 x2 y2 lambda,
    (x1 - x2) *
      (A + lambda * lambda * x1 - lambda * lambda * x2 -
       2 * lambda * y1 + x1 * x1 + x1 * x2 + x2 * x2) -
      ((y2 * y2 - (x2 * x2 * x2 + A * x2 + B)) -
       (y1 * y1 - (x1 * x1 * x1 + A * x1 + B))) =
      (lambda * x1 - lambda * x2 - y1 - y2) *
      (lambda * x1 - lambda * x2 - y1 + y2).
Proof. intros; ring. Qed.

Lemma aj_secant_output_identity :
  forall A B x1 y1 x2 lambda,
    (lambda * (x1 - (lambda * lambda - x1 - x2)) - y1) *
      (lambda * (x1 - (lambda * lambda - x1 - x2)) - y1) -
      ((lambda * lambda - x1 - x2) *
       (lambda * lambda - x1 - x2) *
       (lambda * lambda - x1 - x2) +
       A * (lambda * lambda - x1 - x2) + B) =
      (y1 * y1 - (x1 * x1 * x1 + A * x1 + B)) +
      (- lambda * lambda + 2 * x1 + x2) *
      (A + lambda * lambda * x1 - lambda * lambda * x2 -
       2 * lambda * y1 + x1 * x1 + x1 * x2 + x2 * x2).
Proof. intros; ring. Qed.

(** The affine chord formula preserves the SM2 curve equation.  This theorem
    mentions only mathematical coordinates and modular congruence; the
    Jacobian implementation temporaries remain in the case-local bridge. *)
Lemma aj_secant_raw_preserves_curve :
  forall x1 y1 x2 y2 lambda,
    sm2_affine_on_curve x1 y1 ->
    sm2_affine_on_curve x2 y2 ->
    ~ congr_mod SM2_P_Z (x1 - x2) 0 ->
    congr_mod SM2_P_Z ((x1 - x2) * lambda) (y1 - y2) ->
    let x3 := lambda * lambda - x1 - x2 in
    let y3 := lambda * (x1 - x3) - y1 in
    congr_mod SM2_P_Z (y3 * y3)
      (x3 * x3 * x3 + SM2_A_Z * x3 + SM2_B_Z).
Proof.
  intros x1 y1 x2 y2 lambda HC1 HC2 Hdx Hslope.
  assert (Hp : SM2_P_Z <> 0)
    by (pose proof sm2_p_montgomery_bounds; lia).
  pose proof (aj_sm2_point_on_curve_equation x1 y1 HC1) as HC1eq.
  pose proof (aj_sm2_point_on_curve_equation x2 y2 HC2) as HC2eq.
  assert (HC1c : congr_mod SM2_P_Z
      (y1 * y1) (x1 * x1 * x1 + SM2_A_Z * x1 + SM2_B_Z)).
  { apply congr_mod_of_mod_eq; assumption. }
  assert (HC2c : congr_mod SM2_P_Z
      (y2 * y2) (x2 * x2 * x2 + SM2_A_Z * x2 + SM2_B_Z)).
  { apply congr_mod_of_mod_eq; assumption. }
  assert (HC1z : congr_mod SM2_P_Z
      (y1 * y1 - (x1 * x1 * x1 + SM2_A_Z * x1 + SM2_B_Z)) 0).
  { eapply congr_mod_trans.
    - apply congr_mod_sub; [exact HC1c|apply congr_mod_refl].
    - rewrite Z.sub_diag. apply congr_mod_refl. }
  assert (HC2z : congr_mod SM2_P_Z
      (y2 * y2 - (x2 * x2 * x2 + SM2_A_Z * x2 + SM2_B_Z)) 0).
  { eapply congr_mod_trans.
    - apply congr_mod_sub; [exact HC2c|apply congr_mod_refl].
    - rewrite Z.sub_diag. apply congr_mod_refl. }
  assert (Hslopez : congr_mod SM2_P_Z
      (lambda * x1 - lambda * x2 - y1 + y2) 0).
  { replace (lambda * x1 - lambda * x2 - y1 + y2) with
      ((x1 - x2) * lambda - (y1 - y2)) by ring.
    eapply congr_mod_trans.
    - apply congr_mod_sub; [exact Hslope|apply congr_mod_refl].
    - rewrite Z.sub_diag. apply congr_mod_refl. }
  set (K := aj_secant_k x1 y1 x2 lambda).
  assert (HdxK : congr_mod SM2_P_Z ((x1 - x2) * K) 0).
    { assert (Hcurvediff : congr_mod SM2_P_Z
        ((y2 * y2 - (x2 * x2 * x2 + SM2_A_Z * x2 + SM2_B_Z)) -
         (y1 * y1 - (x1 * x1 * x1 + SM2_A_Z * x1 + SM2_B_Z))) 0).
    { eapply congr_mod_trans.
      - apply congr_mod_sub; [exact HC2z|exact HC1z].
      - rewrite Z.sub_diag. apply congr_mod_refl. }
    assert (Hfactor : congr_mod SM2_P_Z
        ((lambda * x1 - lambda * x2 - y1 - y2) *
         (lambda * x1 - lambda * x2 - y1 + y2)) 0).
    { eapply congr_mod_trans.
      - apply congr_mod_mul; [apply congr_mod_refl|exact Hslopez].
      - rewrite Z.mul_0_r. apply congr_mod_refl. }
    eapply congr_mod_trans with
      (b :=
        ((y2 * y2 - (x2 * x2 * x2 + SM2_A_Z * x2 + SM2_B_Z)) -
         (y1 * y1 - (x1 * x1 * x1 + SM2_A_Z * x1 + SM2_B_Z))) +
        ((lambda * x1 - lambda * x2 - y1 - y2) *
         (lambda * x1 - lambda * x2 - y1 + y2))).
    - unfold K, aj_secant_k.
      pose proof (aj_secant_factor_identity SM2_A_Z SM2_B_Z
        x1 y1 x2 y2 lambda) as Hid.
      assert (Heq :
        (x1 - x2) *
          (SM2_A_Z + lambda * lambda * x1 - lambda * lambda * x2 -
           2 * lambda * y1 + x1 * x1 + x1 * x2 + x2 * x2) =
        ((y2 * y2 - (x2 * x2 * x2 + SM2_A_Z * x2 + SM2_B_Z)) -
         (y1 * y1 - (x1 * x1 * x1 + SM2_A_Z * x1 + SM2_B_Z))) +
        ((lambda * x1 - lambda * x2 - y1 - y2) *
         (lambda * x1 - lambda * x2 - y1 + y2))).
      { exact (aj_move_sub_eq _ _ _ Hid). }
      rewrite Heq. apply congr_mod_refl.
    - replace 0 with (0 + 0) by reflexivity.
      apply congr_mod_add; assumption. }
  assert (HK : congr_mod SM2_P_Z K 0).
  { apply (aj_congr_mod_cancel_nonzero_right_raw K 0 (x1 - x2) Hdx).
    rewrite Z.mul_comm.
    exact HdxK. }
  set (x3 := lambda * lambda - x1 - x2).
  set (y3 := lambda * (x1 - x3) - y1).
  assert (Hres : congr_mod SM2_P_Z
      (y3 * y3 - (x3 * x3 * x3 + SM2_A_Z * x3 + SM2_B_Z)) 0).
  { eapply congr_mod_trans with
      (b :=
        (y1 * y1 - (x1 * x1 * x1 + SM2_A_Z * x1 + SM2_B_Z)) +
        (- lambda * lambda + 2 * x1 + x2) * K).
    - assert (Heq :
        y3 * y3 - (x3 * x3 * x3 + SM2_A_Z * x3 + SM2_B_Z) =
        (y1 * y1 - (x1 * x1 * x1 + SM2_A_Z * x1 + SM2_B_Z)) +
        (- lambda * lambda + 2 * x1 + x2) * K).
      { unfold x3, y3, K, aj_secant_k.
        exact (aj_secant_output_identity SM2_A_Z SM2_B_Z
          x1 y1 x2 lambda). }
      rewrite Heq. apply congr_mod_refl.
    - eapply congr_mod_trans with
        (b := 0 + (- lambda * lambda + 2 * x1 + x2) * 0).
      + apply congr_mod_add; [exact HC1z|].
        apply congr_mod_mul; [apply congr_mod_refl|exact HK].
      + rewrite Z.mul_0_r, Z.add_0_r. apply congr_mod_refl. }
  unfold congr_mod in Hres |- *.
  unfold x3, y3 in Hres |- *.
  rewrite Z.sub_0_r in Hres.
  exact Hres.
Qed.

Lemma aj_canonical_difference_nonzero_mod :
  forall x1 x2,
    0 <= x1 < SM2_P_Z ->
    0 <= x2 < SM2_P_Z ->
    x1 <> x2 ->
    ~ congr_mod SM2_P_Z (x1 - x2) 0.
Proof.
  intros x1 x2 Hx1 Hx2 Hneq Hdiff.
  apply Hneq.
  apply (congr_mod_eq_canonical SM2_P_Z x1 x2).
  - pose proof sm2_p_montgomery_bounds; lia.
  - exact Hx1.
  - exact Hx2.
  - unfold congr_mod in Hdiff |- *.
    rewrite Z.sub_0_r in Hdiff.
    exact Hdiff.
Qed.

(** Construction of the abstract finite-point branch used by functional point
    addition.  The witness is canonical, but no executable inversion routine
    is exposed in the public function contract. *)
Lemma aj_sm2_point_add_finite_distinct_construct :
  forall x1 y1 x2 y2,
    forall (HP1 : sm2_affine_on_curve x1 y1),
    forall (HP2 : sm2_affine_on_curve x2 y2),
    x1 <> x2 ->
    exists lambda qx qy,
      exists HQ : sm2_affine_on_curve qx qy,
        sm2_point_add
          (ec_point_of_affine x1 y1 HP1)
          (ec_point_of_affine x2 y2 HP2) =
          ec_point_of_affine qx qy HQ /\
        congr_mod SM2_P_Z ((x1 - x2) * lambda) (y1 - y2) /\
        qx = (lambda * lambda - x1 - x2) mod SM2_P_Z /\
        qy = (lambda * (x1 - qx) - y1) mod SM2_P_Z.
Proof.
  intros x1 y1 x2 y2 HP1 HP2 Hneq.
  pose proof (sm2_point_on_curve_coordinate_bounds x1 y1 HP1)
    as [Hx1 Hy1].
  pose proof (sm2_point_on_curve_coordinate_bounds x2 y2 HP2)
    as [Hx2 Hy2].
  assert (Hden : ~ congr_mod SM2_P_Z (x1 - x2) 0).
  { now apply aj_canonical_difference_nonzero_mod. }
  destruct (sm2_congruence_division_exists
      (x1 - x2) (y1 - y2) Hden) as [lambda [Hlambda Hslope]].
  set (raw_x := lambda * lambda - x1 - x2).
  set (qx := raw_x mod SM2_P_Z).
  set (raw_y := lambda * (x1 - qx) - y1).
  set (qy := raw_y mod SM2_P_Z).
  assert (Hraw_curve : congr_mod SM2_P_Z (raw_y * raw_y)
      (raw_x * raw_x * raw_x + SM2_A_Z * raw_x + SM2_B_Z)).
  { assert (Hraw0 := aj_secant_raw_preserves_curve
        x1 y1 x2 y2 lambda HP1 HP2 Hden Hslope).
    simpl in Hraw0.
    assert (Hqx_raw : congr_mod SM2_P_Z qx raw_x).
    { unfold qx. apply congr_mod_mod.
      pose proof sm2_p_montgomery_bounds; lia. }
    assert (Hy_adjust : congr_mod SM2_P_Z raw_y
        (lambda * (x1 - raw_x) - y1)).
    { unfold raw_y.
      apply congr_mod_sub.
      - apply congr_mod_mul; [apply congr_mod_refl|].
        apply congr_mod_sub; [apply congr_mod_refl|exact Hqx_raw].
      - apply congr_mod_refl. }
    assert (Hy_square := congr_mod_pow2 SM2_P_Z _ _ Hy_adjust).
    replace (raw_y ^ 2) with (raw_y * raw_y) in Hy_square by ring.
    replace ((lambda * (x1 - raw_x) - y1) ^ 2) with
      ((lambda * (x1 - raw_x) - y1) *
       (lambda * (x1 - raw_x) - y1)) in Hy_square by ring.
    eapply congr_mod_trans; [exact Hy_square|].
    exact Hraw0. }
  assert (HQ : sm2_affine_on_curve qx qy).
  { unfold qx, qy. now apply sm2_canonicalize_curve_point. }
  assert (Hslope_direct : sm2_affine_slope
      (y2 - y1) (x2 - x1) lambda).
  { split; [exact Hlambda|].
    apply (proj1 (sm2_eqm_iff_sub_mod_zero _ _)).
    unfold eqm.
    apply congr_mod_to_mod_eq.
    - pose proof sm2_p_montgomery_bounds; lia.
    - replace ((x2 - x1) * lambda) with
        ((-1) * ((x1 - x2) * lambda)) by ring.
      replace (y2 - y1) with ((-1) * (y1 - y2)) by ring.
      apply congr_mod_scale; exact Hslope. }
  exists lambda, qx, qy, HQ.
  split.
  - apply (sm2_point_add_affine_distinct
      x1 y1 x2 y2 lambda qx qy HP1 HP2 HQ Hneq Hslope_direct).
    unfold sm2_affine_sum.
    split.
    + unfold qx, raw_x; reflexivity.
    + unfold qy, raw_y; reflexivity.
  - split; [exact Hslope|].
    split.
    + unfold qx, raw_x; reflexivity.
    + unfold qy, raw_y; reflexivity.
Qed.

Lemma aj_mod_range : forall a,
  0 <= a mod SM2_P_Z < SM2_P_Z.
Proof.
  intros; apply Z.mod_pos_bound.
  pose proof sm2_p_montgomery_bounds; lia.
Qed.

Lemma aj_mod_congr : forall a,
  congr_mod SM2_P_Z (a mod SM2_P_Z) a.
Proof.
  intros; apply congr_mod_mod.
  pose proof sm2_p_montgomery_bounds; lia.
Qed.

Lemma aj_inv2_congr_half : forall numerator half,
  congr_mod SM2_P_Z numerator (2 * half) ->
  congr_mod SM2_P_Z
    ((numerator * SM2_P_INV2_Z) mod SM2_P_Z) half.
Proof.
  intros numerator half Hnum.
  eapply congr_mod_trans; [apply aj_mod_congr|].
  eapply congr_mod_trans.
  - apply congr_mod_mul; [exact Hnum|apply congr_mod_refl].
  - replace ((2 * half) * SM2_P_INV2_Z) with
      (half * (2 * SM2_P_INV2_Z)) by ring.
    replace half with (half * 1) at 2 by ring.
    apply congr_mod_mul; [apply congr_mod_refl|].
    unfold congr_mod.
    exists 1.
    assert (Hinv : 2 * SM2_P_INV2_Z = SM2_P_Z + 1)
      by (vm_compute; reflexivity).
    lia.
Qed.

Lemma aj_h_nonzero :
  forall x1 z1 x2 z2,
    aj_u1 x1 z2 <> aj_u2 x2 z1 ->
    aj_h x1 z1 x2 z2 <> 0.
Proof.
  intros x1 z1 x2 z2 Hneq Hzero.
  apply Hneq.
  apply (congr_mod_eq_canonical SM2_P_Z
    (aj_u1 x1 z2) (aj_u2 x2 z1)).
  - pose proof sm2_p_montgomery_bounds; lia.
  - unfold aj_u1; apply aj_mod_range.
  - unfold aj_u2; apply aj_mod_range.
  - unfold aj_h in Hzero.
    unfold congr_mod.
    apply Z.mod_divide.
    + pose proof sm2_p_montgomery_bounds; lia.
    + exact Hzero.
Qed.

Lemma aj_rz_nonzero :
  forall x1 z1 x2 z2,
    0 <= z1 < SM2_P_Z -> z1 <> 0 ->
    0 <= z2 < SM2_P_Z -> z2 <> 0 ->
    aj_u1 x1 z2 <> aj_u2 x2 z1 ->
    aj_rz x1 z1 x2 z2 <> 0.
Proof.
  intros x1 z1 x2 z2 Hz1 Hz10 Hz2 Hz20 Hu.
  assert (Hzbase0 : aj_zbase z1 z2 <> 0).
  { unfold aj_zbase.
    now apply sm2_canonical_product_mod_nonzero. }
  assert (Hh0 : aj_h x1 z1 x2 z2 <> 0).
  { now apply aj_h_nonzero. }
  unfold aj_rz.
  apply sm2_canonical_product_mod_nonzero.
  - unfold aj_zbase; apply aj_mod_range.
  - exact Hzbase0.
  - unfold aj_h; apply aj_mod_range.
  - exact Hh0.
Qed.

Lemma aj_scale_pow2_pow4 : forall A q z : Z,
  A * (q * z ^ 2) * z ^ 4 = (A * q) * z ^ 6.
Proof. intros; ring. Qed.

Lemma aj_distribute_pow6 : forall a b c z : Z,
  a * z ^ 6 + b * z ^ 6 + c * z ^ 6 = (a + b + c) * z ^ 6.
Proof. intros; ring. Qed.

(** Fold canonical projective coordinates back to the abstract finite point.
    This is the representation boundary used after the implementation trace
    has established its two cross-product congruences. *)
Lemma aj_projective_represents_affine :
  forall rx ry rz qx qy (HQ : sm2_affine_on_curve qx qy),
    0 <= rx < SM2_P_Z ->
    0 <= ry < SM2_P_Z ->
    0 <= rz < SM2_P_Z ->
    rz <> 0 ->
    congr_mod SM2_P_Z rx (qx * rz ^ 2) ->
    congr_mod SM2_P_Z ry (qy * rz ^ 3) ->
    jpoint_represents rx ry rz (ec_point_of_affine qx qy HQ).
Proof.
  intros rx ry rz qx qy HQ Hrxr Hryr Hrzr Hrz0 Hrx Hry.
  assert (Hp : SM2_P_Z <> 0)
    by (pose proof sm2_p_montgomery_bounds; lia).
  cbn [jpoint_represents].
  split; [exact Hrxr|].
  split; [exact Hryr|].
  split; [exact Hrzr|].
  split; [exact Hrz0|].
  split.
  - pose proof
      (congr_mod_to_mod_eq SM2_P_Z rx (qx * rz ^ 2) Hp Hrx)
      as Heq.
    rewrite Z.mod_small in Heq by exact Hrxr.
    rewrite sm2_fe_value_of_Z by exact (proj1 HQ).
    exact Heq.
  - pose proof
      (congr_mod_to_mod_eq SM2_P_Z ry (qy * rz ^ 3) Hp Hry)
      as Heq.
    rewrite Z.mod_small in Heq by exact Hryr.
    rewrite sm2_fe_value_of_Z by exact (proj1 (proj2 HQ)).
    exact Heq.
Qed.

Lemma aj_u1_affine_scale : forall x1 z1 z2 px1,
  congr_mod SM2_P_Z x1 (px1 * z1 ^ 2) ->
  congr_mod SM2_P_Z (aj_u1 x1 z2) (px1 * (z1 * z2) ^ 2).
Proof.
  intros x1 z1 z2 px1 Hx.
  unfold aj_u1, aj_qz2.
  eapply congr_mod_trans; [apply aj_mod_congr|].
  eapply congr_mod_trans with (b := (px1 * z1 ^ 2) * z2 ^ 2).
  - apply congr_mod_mul.
    + exact Hx.
    + eapply congr_mod_trans; [apply aj_mod_congr|].
      replace (z2 * z2) with (z2 ^ 2) by ring.
      apply congr_mod_refl.
  - replace ((px1 * z1 ^ 2) * z2 ^ 2) with
      (px1 * (z1 * z2) ^ 2) by ring.
    apply congr_mod_refl.
Qed.

Lemma aj_u2_affine_scale : forall x2 z1 z2 px2,
  congr_mod SM2_P_Z x2 (px2 * z2 ^ 2) ->
  congr_mod SM2_P_Z (aj_u2 x2 z1) (px2 * (z1 * z2) ^ 2).
Proof.
  intros x2 z1 z2 px2 Hx.
  unfold aj_u2, aj_pz2.
  eapply congr_mod_trans; [apply aj_mod_congr|].
  eapply congr_mod_trans with (b := (px2 * z2 ^ 2) * z1 ^ 2).
  - apply congr_mod_mul.
    + exact Hx.
    + eapply congr_mod_trans; [apply aj_mod_congr|].
      replace (z1 * z1) with (z1 ^ 2) by ring.
      apply congr_mod_refl.
  - replace ((px2 * z2 ^ 2) * z1 ^ 2) with
      (px2 * (z1 * z2) ^ 2) by ring.
    apply congr_mod_refl.
Qed.

Lemma aj_s1_affine_scale : forall y1 z1 z2 py1,
  congr_mod SM2_P_Z y1 (py1 * z1 ^ 3) ->
  congr_mod SM2_P_Z (aj_s1 y1 z2) (py1 * (z1 * z2) ^ 3).
Proof.
  intros y1 z1 z2 py1 Hy.
  unfold aj_s1, aj_qz3, aj_qz2.
  eapply congr_mod_trans; [apply aj_mod_congr|].
  eapply congr_mod_trans with (b := (py1 * z1 ^ 3) * z2 ^ 3).
  - apply congr_mod_mul.
    + exact Hy.
    + eapply congr_mod_trans; [apply aj_mod_congr|].
      eapply congr_mod_trans with (b := z2 ^ 2 * z2).
      * apply congr_mod_mul.
        -- eapply congr_mod_trans; [apply aj_mod_congr|].
           replace (z2 * z2) with (z2 ^ 2) by ring.
           apply congr_mod_refl.
        -- apply congr_mod_refl.
      * replace (z2 ^ 2 * z2) with (z2 ^ 3) by ring.
        apply congr_mod_refl.
  - replace ((py1 * z1 ^ 3) * z2 ^ 3) with
      (py1 * (z1 * z2) ^ 3) by ring.
    apply congr_mod_refl.
Qed.

Lemma aj_s2_affine_scale : forall y2 z1 z2 py2,
  congr_mod SM2_P_Z y2 (py2 * z2 ^ 3) ->
  congr_mod SM2_P_Z (aj_s2 y2 z1) (py2 * (z1 * z2) ^ 3).
Proof.
  intros y2 z1 z2 py2 Hy.
  unfold aj_s2, aj_pz3, aj_pz2.
  eapply congr_mod_trans; [apply aj_mod_congr|].
  eapply congr_mod_trans with (b := (py2 * z2 ^ 3) * z1 ^ 3).
  - apply congr_mod_mul.
    + exact Hy.
    + eapply congr_mod_trans; [apply aj_mod_congr|].
      eapply congr_mod_trans with (b := z1 ^ 2 * z1).
      * apply congr_mod_mul.
        -- eapply congr_mod_trans; [apply aj_mod_congr|].
           replace (z1 * z1) with (z1 ^ 2) by ring.
           apply congr_mod_refl.
        -- apply congr_mod_refl.
      * replace (z1 ^ 2 * z1) with (z1 ^ 3) by ring.
        apply congr_mod_refl.
  - replace ((py2 * z2 ^ 3) * z1 ^ 3) with
      (py2 * (z1 * z2) ^ 3) by ring.
    apply congr_mod_refl.
Qed.

Lemma aj_x_numerator_factor_identity :
  forall px1 py1 px2 py2 lambda,
    ((py1 - py2) * (py1 - py2) -
     (px1 + px2) * (px1 - px2) * (px1 - px2)) -
    ((lambda * lambda - px1 - px2) *
     (px1 - px2) * (px1 - px2)) =
    (- ((px1 - px2) * lambda - (py1 - py2))) *
    ((px1 - px2) * lambda + (py1 - py2)).
Proof. intros; ring. Qed.

Lemma aj_negative_witness_reassociate : forall k p f : Z,
  (- (k * p)) * f = (- k * f) * p.
Proof. intros; ring. Qed.

Lemma aj_x_numerator_matches_raw_affine :
  forall px1 py1 px2 py2 lambda,
    congr_mod SM2_P_Z ((px1 - px2) * lambda) (py1 - py2) ->
    congr_mod SM2_P_Z
      ((py1 - py2) * (py1 - py2) -
       (px1 + px2) * (px1 - px2) * (px1 - px2))
      ((lambda * lambda - px1 - px2) *
       (px1 - px2) * (px1 - px2)).
Proof.
  intros px1 py1 px2 py2 lambda [k Hk].
  unfold congr_mod.
  exists (- k * ((px1 - px2) * lambda + (py1 - py2))).
  rewrite (aj_x_numerator_factor_identity px1 py1 px2 py2 lambda).
  rewrite Hk.
  apply aj_negative_witness_reassociate.
Qed.

Definition aj_y_factor (px1 py1 px2 py2 lambda : Z) : Z :=
  lambda * lambda * px1 * px1 -
  2 * lambda * lambda * px1 * px2 +
  lambda * lambda * px2 * px2 +
  lambda * px1 * py1 - lambda * px1 * py2 -
  lambda * px2 * py1 + lambda * px2 * py2 -
  2 * px1 * px1 * px1 + 3 * px1 * px1 * px2 -
  px2 * px2 * px2 +
  py1 * py1 - 2 * py1 * py2 + py2 * py2.

Lemma aj_y_numerator_factor_identity :
  forall px1 py1 px2 py2 lambda,
    let d := px1 - px2 in
    let e := py1 - py2 in
    let xnum := e * e - (px1 + px2) * d * d in
    let raw_x := lambda * lambda - px1 - px2 in
    let raw_y := lambda * (px1 - raw_x) - py1 in
    (((px1 + px2) * d * d - 2 * xnum) * e -
     ((py1 + py2) * d * d) * d) - 2 * raw_y * d ^ 3 =
    2 * (d * lambda - e) * aj_y_factor px1 py1 px2 py2 lambda.
Proof.
  intros px1 py1 px2 py2 lambda.
  cbv beta; unfold aj_y_factor; ring.
Qed.

Lemma aj_witness_reassociate : forall k p f : Z,
  2 * (k * p) * f = (2 * k * f) * p.
Proof. intros; ring. Qed.

Lemma aj_y_numerator_matches_raw_affine :
  forall px1 py1 px2 py2 lambda,
    congr_mod SM2_P_Z ((px1 - px2) * lambda) (py1 - py2) ->
    let d := px1 - px2 in
    let e := py1 - py2 in
    let xnum := e * e - (px1 + px2) * d * d in
    let raw_x := lambda * lambda - px1 - px2 in
    let raw_y := lambda * (px1 - raw_x) - py1 in
    congr_mod SM2_P_Z
      (((px1 + px2) * d * d - 2 * xnum) * e -
       ((py1 + py2) * d * d) * d)
      (2 * raw_y * d ^ 3).
Proof.
  intros px1 py1 px2 py2 lambda [k Hk].
  cbv beta.
  unfold congr_mod.
  exists (2 * k * aj_y_factor px1 py1 px2 py2 lambda).
  rewrite (aj_y_numerator_factor_identity px1 py1 px2 py2 lambda).
  rewrite Hk.
  apply aj_witness_reassociate.
Qed.

(** A finite curve point has only the two expected ordinates above a fixed
    abscissa.  This excludes the symbolic-execution artefact in which the
    cross-scaled X coordinates agree, the cross-scaled Y coordinates differ,
    but their sum is nevertheless nonzero. *)
Lemma aj_same_x_curve_y_equal_or_opposite :
  forall x y1 y2,
    sm2_affine_on_curve x y1 ->
    sm2_affine_on_curve x y2 ->
    y1 <> y2 ->
    congr_mod SM2_P_Z (y1 + y2) 0.
Proof.
  intros x y1 y2 HV1 HV2 Hneq.
  pose proof (sm2_point_on_curve_coordinate_bounds x y1 HV1)
    as [_ Hy1].
  pose proof (sm2_point_on_curve_coordinate_bounds x y2 HV2)
    as [_ Hy2].
  pose proof (aj_sm2_point_on_curve_equation x y1 HV1) as HC1.
  pose proof (aj_sm2_point_on_curve_equation x y2 HV2) as HC2.
  assert (Hp : SM2_P_Z <> 0)
    by (pose proof sm2_p_montgomery_bounds; lia).
  assert (Hsq : congr_mod SM2_P_Z (y1 * y1) (y2 * y2)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    now rewrite HC1, HC2. }
  assert (Hprod : congr_mod SM2_P_Z ((y1 - y2) * (y1 + y2)) 0).
  { replace ((y1 - y2) * (y1 + y2)) with
      (y1 * y1 - y2 * y2) by ring.
    replace 0 with (y2 * y2 - y2 * y2) by ring.
    apply congr_mod_sub; [exact Hsq|apply congr_mod_refl]. }
  apply (aj_congr_mod_cancel_nonzero_right_raw
    (y1 + y2) 0 (y1 - y2)).
  - now apply aj_canonical_difference_nonzero_mod.
  - replace ((y1 + y2) * (y1 - y2)) with
      ((y1 - y2) * (y1 + y2)) by ring.
    replace (0 * (y1 - y2)) with 0 by ring.
    exact Hprod.
Qed.

Lemma aj_same_u_different_s_implies_s_sum_zero :
  forall x1 y1 z1 x2 y2 z2 P1 P2,
    jpoint_represents x1 y1 z1 P1 ->
    jpoint_represents x2 y2 z2 P2 ->
    z1 <> 0 -> z2 <> 0 ->
    aj_u1 x1 z2 = aj_u2 x2 z1 ->
    aj_s1 y1 z2 <> aj_s2 y2 z1 ->
    aj_s_sum y1 z1 y2 z2 = 0.
Proof.
  intros x1 y1 z1 x2 y2 z2 P1 P2 HR1 HR2 Hz10 Hz20 Hu Hs.
  destruct P1 as [|px1_fe py1_fe HP1_fe].
  { cbn [jpoint_represents jpoint_infinity] in HR1.
    exfalso; apply Hz10; exact (proj2 (proj2 (proj2 HR1))). }
  destruct P2 as [|px2_fe py2_fe HP2_fe].
  { cbn [jpoint_represents jpoint_infinity] in HR2.
    exfalso; apply Hz20; exact (proj2 (proj2 (proj2 HR2))). }
  set (px1 := sm2_fe_value px1_fe).
  set (py1 := sm2_fe_value py1_fe).
  set (px2 := sm2_fe_value px2_fe).
  set (py2 := sm2_fe_value py2_fe).
  cbn [jpoint_represents] in HR1, HR2.
  fold px1 py1 in HR1.
  fold px2 py2 in HR2.
  destruct HR1 as [Hx1r [Hy1r [Hz1r [_ [HX1 HY1]]]]].
  destruct HR2 as [Hx2r [Hy2r [Hz2r [_ [HX2 HY2]]]]].
  assert (HP1 : sm2_affine_on_curve px1 py1).
  { unfold sm2_affine_on_curve.
    split; [unfold px1; apply sm2_fe_value_bounds|].
    split; [unfold py1; apply sm2_fe_value_bounds|].
    unfold sm2_affine_equation, px1, py1.
    repeat rewrite sm2_fe_of_Z_value.
    exact HP1_fe. }
  assert (HP2 : sm2_affine_on_curve px2 py2).
  { unfold sm2_affine_on_curve.
    split; [unfold px2; apply sm2_fe_value_bounds|].
    split; [unfold py2; apply sm2_fe_value_bounds|].
    unfold sm2_affine_equation, px2, py2.
    repeat rewrite sm2_fe_of_Z_value.
    exact HP2_fe. }
  pose proof (sm2_point_on_curve_coordinate_bounds px1 py1 HP1)
    as [Hpx1range Hpy1range].
  pose proof (sm2_point_on_curve_coordinate_bounds px2 py2 HP2)
    as [Hpx2range Hpy2range].
  assert (Hp : SM2_P_Z <> 0)
    by (pose proof sm2_p_montgomery_bounds; lia).
  assert (CX1 : congr_mod SM2_P_Z x1 (px1 * z1 ^ 2)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hx1r; exact HX1. }
  assert (CY1 : congr_mod SM2_P_Z y1 (py1 * z1 ^ 3)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hy1r; exact HY1. }
  assert (CX2 : congr_mod SM2_P_Z x2 (px2 * z2 ^ 2)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hx2r; exact HX2. }
  assert (CY2 : congr_mod SM2_P_Z y2 (py2 * z2 ^ 3)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hy2r; exact HY2. }
  set (w := z1 * z2).
  assert (Hz1c : ~ congr_mod SM2_P_Z z1 0).
  { intro H; apply Hz10.
    apply (congr_mod_eq_canonical SM2_P_Z z1 0).
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact Hz1r.
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact H. }
  assert (Hz2c : ~ congr_mod SM2_P_Z z2 0).
  { intro H; apply Hz20.
    apply (congr_mod_eq_canonical SM2_P_Z z2 0).
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact Hz2r.
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact H. }
  assert (Hwc : ~ congr_mod SM2_P_Z w 0).
  { intro H.
    unfold w in H.
    apply Hz1c.
    apply (aj_congr_mod_cancel_nonzero_right_raw z1 0 z2 Hz2c).
    replace (0 * z2) with 0 by ring; exact H. }
  assert (Hw2c : ~ congr_mod SM2_P_Z (w ^ 2) 0).
  { intro H; apply Hwc.
    apply (aj_congr_mod_cancel_nonzero_right_raw w 0 w Hwc).
    replace (w * w) with (w ^ 2) by ring.
    replace (0 * w) with 0 by ring; exact H. }
  assert (Hw3c : ~ congr_mod SM2_P_Z (w ^ 3) 0).
  { intro H; apply Hwc.
    apply (aj_congr_mod_cancel_nonzero_right_raw w 0 (w ^ 2) Hw2c).
    replace (w * w ^ 2) with (w ^ 3) by ring.
    replace (0 * w ^ 2) with 0 by ring; exact H. }
  assert (CU1 : congr_mod SM2_P_Z (aj_u1 x1 z2) (px1 * w ^ 2)).
  { unfold w; now apply aj_u1_affine_scale. }
  assert (CU2 : congr_mod SM2_P_Z (aj_u2 x2 z1) (px2 * w ^ 2)).
  { unfold w; now apply aj_u2_affine_scale. }
  assert (Hpx : px1 = px2).
  { apply (congr_mod_eq_canonical SM2_P_Z px1 px2).
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact Hpx1range.
    - exact Hpx2range.
    - apply (aj_congr_mod_cancel_nonzero_right_raw px1 px2 (w ^ 2) Hw2c).
      eapply congr_mod_trans; [apply congr_mod_sym; exact CU1|].
      rewrite Hu; exact CU2. }
  assert (CS1 : congr_mod SM2_P_Z (aj_s1 y1 z2) (py1 * w ^ 3)).
  { unfold w; now apply aj_s1_affine_scale. }
  assert (CS2 : congr_mod SM2_P_Z (aj_s2 y2 z1) (py2 * w ^ 3)).
  { unfold w; now apply aj_s2_affine_scale. }
  assert (Hpy : py1 <> py2).
  { intro Heq; apply Hs.
    apply (congr_mod_eq_canonical SM2_P_Z
      (aj_s1 y1 z2) (aj_s2 y2 z1)).
    - pose proof sm2_p_montgomery_bounds; lia.
    - unfold aj_s1; apply aj_mod_range.
    - unfold aj_s2; apply aj_mod_range.
    - eapply congr_mod_trans; [exact CS1|].
      apply congr_mod_sym.
      rewrite <- Heq in CS2.
      exact CS2. }
  assert (Hysum : congr_mod SM2_P_Z (py1 + py2) 0).
  { apply (aj_same_x_curve_y_equal_or_opposite px1 py1 py2).
    - exact HP1.
    - rewrite Hpx. exact HP2.
    - exact Hpy. }
  assert (CSsum : congr_mod SM2_P_Z (aj_s_sum y1 z1 y2 z2)
      ((py1 + py2) * w ^ 3)).
  { unfold aj_s_sum.
    eapply congr_mod_trans; [apply aj_mod_congr|].
    eapply congr_mod_trans.
    - apply congr_mod_add; [exact CS1|exact CS2].
    - replace (py1 * w ^ 3 + py2 * w ^ 3) with
        ((py1 + py2) * w ^ 3) by ring.
      apply congr_mod_refl. }
  apply (congr_mod_eq_canonical SM2_P_Z
    (aj_s_sum y1 z1 y2 z2) 0).
  - pose proof sm2_p_montgomery_bounds; lia.
  - unfold aj_s_sum; apply aj_mod_range.
  - pose proof sm2_p_montgomery_bounds; lia.
  - eapply congr_mod_trans; [exact CSsum|].
    replace 0 with (0 * w ^ 3) by ring.
    apply congr_mod_mul; [exact Hysum|apply congr_mod_refl].
Qed.

Lemma aj_same_u_s_sum_zero_adds_infinity :
  forall x1 y1 z1 x2 y2 z2 P1 P2,
    jpoint_represents x1 y1 z1 P1 ->
    jpoint_represents x2 y2 z2 P2 ->
    z1 <> 0 -> z2 <> 0 ->
    aj_u1 x1 z2 = aj_u2 x2 z1 ->
    aj_s_sum y1 z1 y2 z2 = 0 ->
    sm2_point_add P1 P2 = ECInfinity.
Proof.
  intros x1 y1 z1 x2 y2 z2 P1 P2 HR1 HR2 Hz10 Hz20 Hu Hsum.
  destruct P1 as [|px1_fe py1_fe HP1_fe].
  { cbn [jpoint_represents jpoint_infinity] in HR1.
    exfalso; apply Hz10; exact (proj2 (proj2 (proj2 HR1))). }
  destruct P2 as [|px2_fe py2_fe HP2_fe].
  { cbn [jpoint_represents jpoint_infinity] in HR2.
    exfalso; apply Hz20; exact (proj2 (proj2 (proj2 HR2))). }
  set (px1 := sm2_fe_value px1_fe).
  set (py1 := sm2_fe_value py1_fe).
  set (px2 := sm2_fe_value px2_fe).
  set (py2 := sm2_fe_value py2_fe).
  cbn [jpoint_represents] in HR1, HR2.
  fold px1 py1 in HR1.
  fold px2 py2 in HR2.
  destruct HR1 as [Hx1r [Hy1r [Hz1r [_ [HX1 HY1]]]]].
  destruct HR2 as [Hx2r [Hy2r [Hz2r [_ [HX2 HY2]]]]].
  assert (HP1 : sm2_affine_on_curve px1 py1).
  { unfold sm2_affine_on_curve.
    split; [unfold px1; apply sm2_fe_value_bounds|].
    split; [unfold py1; apply sm2_fe_value_bounds|].
    unfold sm2_affine_equation, px1, py1.
    repeat rewrite sm2_fe_of_Z_value.
    exact HP1_fe. }
  assert (HP2 : sm2_affine_on_curve px2 py2).
  { unfold sm2_affine_on_curve.
    split; [unfold px2; apply sm2_fe_value_bounds|].
    split; [unfold py2; apply sm2_fe_value_bounds|].
    unfold sm2_affine_equation, px2, py2.
    repeat rewrite sm2_fe_of_Z_value.
    exact HP2_fe. }
  pose proof (sm2_point_on_curve_coordinate_bounds px1 py1 HP1)
    as [Hpx1range Hpy1range].
  pose proof (sm2_point_on_curve_coordinate_bounds px2 py2 HP2)
    as [Hpx2range Hpy2range].
  assert (Hp : SM2_P_Z <> 0)
    by (pose proof sm2_p_montgomery_bounds; lia).
  assert (CX1 : congr_mod SM2_P_Z x1 (px1 * z1 ^ 2)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hx1r; exact HX1. }
  assert (CY1 : congr_mod SM2_P_Z y1 (py1 * z1 ^ 3)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hy1r; exact HY1. }
  assert (CX2 : congr_mod SM2_P_Z x2 (px2 * z2 ^ 2)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hx2r; exact HX2. }
  assert (CY2 : congr_mod SM2_P_Z y2 (py2 * z2 ^ 3)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hy2r; exact HY2. }
  set (w := z1 * z2).
  assert (Hz1c : ~ congr_mod SM2_P_Z z1 0).
  { intro H; apply Hz10.
    apply (congr_mod_eq_canonical SM2_P_Z z1 0).
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact Hz1r.
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact H. }
  assert (Hz2c : ~ congr_mod SM2_P_Z z2 0).
  { intro H; apply Hz20.
    apply (congr_mod_eq_canonical SM2_P_Z z2 0).
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact Hz2r.
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact H. }
  assert (Hwc : ~ congr_mod SM2_P_Z w 0).
  { intro H.
    unfold w in H.
    apply Hz1c.
    apply (aj_congr_mod_cancel_nonzero_right_raw z1 0 z2 Hz2c).
    replace (0 * z2) with 0 by ring; exact H. }
  assert (Hw2c : ~ congr_mod SM2_P_Z (w ^ 2) 0).
  { intro H; apply Hwc.
    apply (aj_congr_mod_cancel_nonzero_right_raw w 0 w Hwc).
    replace (w * w) with (w ^ 2) by ring.
    replace (0 * w) with 0 by ring; exact H. }
  assert (Hw3c : ~ congr_mod SM2_P_Z (w ^ 3) 0).
  { intro H; apply Hwc.
    apply (aj_congr_mod_cancel_nonzero_right_raw w 0 (w ^ 2) Hw2c).
    replace (w * w ^ 2) with (w ^ 3) by ring.
    replace (0 * w ^ 2) with 0 by ring; exact H. }
  assert (CU1 : congr_mod SM2_P_Z (aj_u1 x1 z2) (px1 * w ^ 2)).
  { unfold w; now apply aj_u1_affine_scale. }
  assert (CU2 : congr_mod SM2_P_Z (aj_u2 x2 z1) (px2 * w ^ 2)).
  { unfold w; now apply aj_u2_affine_scale. }
  assert (Hpx : px1 = px2).
  { apply (congr_mod_eq_canonical SM2_P_Z px1 px2).
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact Hpx1range.
    - exact Hpx2range.
    - apply (aj_congr_mod_cancel_nonzero_right_raw px1 px2 (w ^ 2) Hw2c).
      eapply congr_mod_trans; [apply congr_mod_sym; exact CU1|].
      rewrite Hu; exact CU2. }
  assert (CS1 : congr_mod SM2_P_Z (aj_s1 y1 z2) (py1 * w ^ 3)).
  { unfold w; now apply aj_s1_affine_scale. }
  assert (CS2 : congr_mod SM2_P_Z (aj_s2 y2 z1) (py2 * w ^ 3)).
  { unfold w; now apply aj_s2_affine_scale. }
  assert (CSsum : congr_mod SM2_P_Z (aj_s_sum y1 z1 y2 z2)
      ((py1 + py2) * w ^ 3)).
  { unfold aj_s_sum.
    eapply congr_mod_trans; [apply aj_mod_congr|].
    eapply congr_mod_trans.
    - apply congr_mod_add; [exact CS1|exact CS2].
    - replace (py1 * w ^ 3 + py2 * w ^ 3) with
        ((py1 + py2) * w ^ 3) by ring.
      apply congr_mod_refl. }
  assert (Hpysum : congr_mod SM2_P_Z (py1 + py2) 0).
  { apply (aj_congr_mod_cancel_nonzero_right_raw
      (py1 + py2) 0 (w ^ 3) Hw3c).
    replace (0 * w ^ 3) with 0 by ring.
    apply congr_mod_sym.
    rewrite <- Hsum.
    exact CSsum. }
  assert (Hpyneq : py1 <> py2).
  { intros Hpyeq.
    pose proof (sm2_point_on_curve_y_nonzero px1 py1 HP1) as Hpy10.
    apply Hpy10.
    apply (congr_mod_eq_canonical SM2_P_Z py1 0).
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact Hpy1range.
    - pose proof sm2_p_montgomery_bounds; lia.
    - apply sm2_congr_mod_cancel_two.
      replace (2 * py1) with (py1 + py2) by lia.
      replace (2 * 0) with 0 by ring.
      exact Hpysum. }
  assert (HP1_affine :
    @SMain.curve_elt
      (ZEll.pK SM2_P_Z)
      (ZEll.pkI SM2_P_Z) (@ZEll.pkplus SM2_P_Z)
      (@ZEll.pkmul SM2_P_Z)
      (ZEll.pA SM2_A_Z SM2_P_Z) (ZEll.pB SM2_B_Z SM2_P_Z)
      px1_fe py1_fe HP1_fe =
    ec_point_of_affine px1 py1 HP1).
  { apply ec_point_of_affine_complete.
    cbn [ec_point_affine_coordinates].
    split; reflexivity. }
  assert (HP2_affine :
    @SMain.curve_elt
      (ZEll.pK SM2_P_Z)
      (ZEll.pkI SM2_P_Z) (@ZEll.pkplus SM2_P_Z)
      (@ZEll.pkmul SM2_P_Z)
      (ZEll.pA SM2_A_Z SM2_P_Z) (ZEll.pB SM2_B_Z SM2_P_Z)
      px2_fe py2_fe HP2_fe =
    ec_point_of_affine px2 py2 HP2).
  { apply ec_point_of_affine_complete.
    cbn [ec_point_affine_coordinates].
    split; reflexivity. }
  assert (HPneq :
    ec_point_of_affine px1 py1 HP1 <>
    ec_point_of_affine px2 py2 HP2).
  { intros Hequal.
    pose proof (ec_point_of_affine_coordinates px1 py1 HP1) as HC1.
    pose proof (ec_point_of_affine_coordinates px2 py2 HP2) as HC2.
    rewrite <- Hequal in HC2.
    pose proof (ec_point_affine_coordinates_functional
      (ec_point_of_affine px1 py1 HP1)
      px1 py1 px2 py2 HC1 HC2) as [_ Hpyeq].
    contradiction. }
  rewrite HP1_affine, HP2_affine.
  exact (sm2_point_add_affine_same_x_distinct
    px1 py1 px2 py2 HP1 HP2 Hpx HPneq).
Qed.

Lemma aj_same_u_same_s_points_equal :
  forall x1 y1 z1 x2 y2 z2 P1 P2,
    jpoint_represents x1 y1 z1 P1 ->
    jpoint_represents x2 y2 z2 P2 ->
    z1 <> 0 -> z2 <> 0 ->
    aj_u1 x1 z2 = aj_u2 x2 z1 ->
    aj_s1 y1 z2 = aj_s2 y2 z1 ->
    P1 = P2.
Proof.
  intros x1 y1 z1 x2 y2 z2 P1 P2 HR1 HR2 Hz10 Hz20 Hu Hs.
  destruct P1 as [|px1_fe py1_fe HP1_fe].
  { cbn [jpoint_represents jpoint_infinity] in HR1.
    exfalso; apply Hz10; exact (proj2 (proj2 (proj2 HR1))). }
  destruct P2 as [|px2_fe py2_fe HP2_fe].
  { cbn [jpoint_represents jpoint_infinity] in HR2.
    exfalso; apply Hz20; exact (proj2 (proj2 (proj2 HR2))). }
  set (px1 := sm2_fe_value px1_fe).
  set (py1 := sm2_fe_value py1_fe).
  set (px2 := sm2_fe_value px2_fe).
  set (py2 := sm2_fe_value py2_fe).
  cbn [jpoint_represents] in HR1, HR2.
  fold px1 py1 in HR1.
  fold px2 py2 in HR2.
  destruct HR1 as [Hx1r [Hy1r [Hz1r [_ [HX1 HY1]]]]].
  destruct HR2 as [Hx2r [Hy2r [Hz2r [_ [HX2 HY2]]]]].
  assert (HP1 : sm2_affine_on_curve px1 py1).
  { unfold sm2_affine_on_curve.
    split; [unfold px1; apply sm2_fe_value_bounds|].
    split; [unfold py1; apply sm2_fe_value_bounds|].
    unfold sm2_affine_equation, px1, py1.
    repeat rewrite sm2_fe_of_Z_value.
    exact HP1_fe. }
  assert (HP2 : sm2_affine_on_curve px2 py2).
  { unfold sm2_affine_on_curve.
    split; [unfold px2; apply sm2_fe_value_bounds|].
    split; [unfold py2; apply sm2_fe_value_bounds|].
    unfold sm2_affine_equation, px2, py2.
    repeat rewrite sm2_fe_of_Z_value.
    exact HP2_fe. }
  pose proof (sm2_point_on_curve_coordinate_bounds px1 py1 HP1)
    as [Hpx1range Hpy1range].
  pose proof (sm2_point_on_curve_coordinate_bounds px2 py2 HP2)
    as [Hpx2range Hpy2range].
  assert (Hp : SM2_P_Z <> 0)
    by (pose proof sm2_p_montgomery_bounds; lia).
  assert (CX1 : congr_mod SM2_P_Z x1 (px1 * z1 ^ 2)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hx1r; exact HX1. }
  assert (CY1 : congr_mod SM2_P_Z y1 (py1 * z1 ^ 3)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hy1r; exact HY1. }
  assert (CX2 : congr_mod SM2_P_Z x2 (px2 * z2 ^ 2)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hx2r; exact HX2. }
  assert (CY2 : congr_mod SM2_P_Z y2 (py2 * z2 ^ 3)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hy2r; exact HY2. }
  set (w := z1 * z2).
  assert (Hz1c : ~ congr_mod SM2_P_Z z1 0).
  { intro H; apply Hz10.
    apply (congr_mod_eq_canonical SM2_P_Z z1 0).
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact Hz1r.
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact H. }
  assert (Hz2c : ~ congr_mod SM2_P_Z z2 0).
  { intro H; apply Hz20.
    apply (congr_mod_eq_canonical SM2_P_Z z2 0).
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact Hz2r.
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact H. }
  assert (Hwc : ~ congr_mod SM2_P_Z w 0).
  { intro H.
    unfold w in H.
    apply Hz1c.
    apply (aj_congr_mod_cancel_nonzero_right_raw z1 0 z2 Hz2c).
    replace (0 * z2) with 0 by ring; exact H. }
  assert (Hw2c : ~ congr_mod SM2_P_Z (w ^ 2) 0).
  { intro H; apply Hwc.
    apply (aj_congr_mod_cancel_nonzero_right_raw w 0 w Hwc).
    replace (w * w) with (w ^ 2) by ring.
    replace (0 * w) with 0 by ring; exact H. }
  assert (Hw3c : ~ congr_mod SM2_P_Z (w ^ 3) 0).
  { intro H; apply Hwc.
    apply (aj_congr_mod_cancel_nonzero_right_raw w 0 (w ^ 2) Hw2c).
    replace (w * w ^ 2) with (w ^ 3) by ring.
    replace (0 * w ^ 2) with 0 by ring; exact H. }
  assert (CU1 : congr_mod SM2_P_Z (aj_u1 x1 z2) (px1 * w ^ 2)).
  { unfold w; now apply aj_u1_affine_scale. }
  assert (CU2 : congr_mod SM2_P_Z (aj_u2 x2 z1) (px2 * w ^ 2)).
  { unfold w; now apply aj_u2_affine_scale. }
  assert (Hpx : px1 = px2).
  { apply (congr_mod_eq_canonical SM2_P_Z px1 px2).
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact Hpx1range.
    - exact Hpx2range.
    - apply (aj_congr_mod_cancel_nonzero_right_raw px1 px2 (w ^ 2) Hw2c).
      eapply congr_mod_trans; [apply congr_mod_sym; exact CU1|].
      rewrite Hu; exact CU2. }
  assert (CS1 : congr_mod SM2_P_Z (aj_s1 y1 z2) (py1 * w ^ 3)).
  { unfold w; now apply aj_s1_affine_scale. }
  assert (CS2 : congr_mod SM2_P_Z (aj_s2 y2 z1) (py2 * w ^ 3)).
  { unfold w; now apply aj_s2_affine_scale. }
  assert (Hpy : py1 = py2).
  { apply (congr_mod_eq_canonical SM2_P_Z py1 py2).
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact Hpy1range.
    - exact Hpy2range.
    - apply (aj_congr_mod_cancel_nonzero_right_raw py1 py2 (w ^ 3) Hw3c).
      eapply congr_mod_trans; [apply congr_mod_sym; exact CS1|].
      rewrite Hs; exact CS2. }
  apply (SMain.curve_elt_irr sm2_curve_theory).
  - rewrite <- (sm2_fe_of_Z_value px1_fe).
    rewrite <- (sm2_fe_of_Z_value px2_fe).
    apply f_equal.
    unfold px1, px2 in Hpx.
    exact Hpx.
  - rewrite <- (sm2_fe_of_Z_value py1_fe).
    rewrite <- (sm2_fe_of_Z_value py2_fe).
    apply f_equal.
    unfold py1, py2 in Hpy.
    exact Hpy.
Qed.

Lemma aj_result_refines_finite_distinct :
  forall x1 y1 z1 x2 y2 z2 P1 P2,
    jpoint_represents x1 y1 z1 P1 ->
    jpoint_represents x2 y2 z2 P2 ->
    aj_u1 x1 z2 <> aj_u2 x2 z1 ->
    z1 <> 0 -> z2 <> 0 ->
    aj_result_refines P1 P2 x1 y1 z1 x2 y2 z2.
Proof.
  intros x1 y1 z1 x2 y2 z2 P1 P2 HR1 HR2 Hu Hz10 Hz20.
  destruct P1 as [|px1_fe py1_fe HP1_fe].
  { cbn [jpoint_represents jpoint_infinity] in HR1.
    exfalso; apply Hz10; exact (proj2 (proj2 (proj2 HR1))). }
  destruct P2 as [|px2_fe py2_fe HP2_fe].
  { cbn [jpoint_represents jpoint_infinity] in HR2.
    exfalso; apply Hz20; exact (proj2 (proj2 (proj2 HR2))). }
  set (px1 := sm2_fe_value px1_fe).
  set (py1 := sm2_fe_value py1_fe).
  set (px2 := sm2_fe_value px2_fe).
  set (py2 := sm2_fe_value py2_fe).
  cbn [jpoint_represents] in HR1, HR2.
  fold px1 py1 in HR1.
  fold px2 py2 in HR2.
  destruct HR1 as [Hx1r [Hy1r [Hz1r [_ [HX1 HY1]]]]].
  destruct HR2 as [Hx2r [Hy2r [Hz2r [_ [HX2 HY2]]]]].
  assert (HP1 : sm2_affine_on_curve px1 py1).
  { unfold sm2_affine_on_curve.
    split; [unfold px1; apply sm2_fe_value_bounds|].
    split; [unfold py1; apply sm2_fe_value_bounds|].
    unfold sm2_affine_equation, px1, py1.
    repeat rewrite sm2_fe_of_Z_value.
    exact HP1_fe. }
  assert (HP2 : sm2_affine_on_curve px2 py2).
  { unfold sm2_affine_on_curve.
    split; [unfold px2; apply sm2_fe_value_bounds|].
    split; [unfold py2; apply sm2_fe_value_bounds|].
    unfold sm2_affine_equation, px2, py2.
    repeat rewrite sm2_fe_of_Z_value.
    exact HP2_fe. }
  assert (Hp : SM2_P_Z <> 0)
    by (pose proof sm2_p_montgomery_bounds; lia).
  assert (CX1 : congr_mod SM2_P_Z x1 (px1 * z1 ^ 2)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hx1r; exact HX1. }
  assert (CY1 : congr_mod SM2_P_Z y1 (py1 * z1 ^ 3)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hy1r; exact HY1. }
  assert (CX2 : congr_mod SM2_P_Z x2 (px2 * z2 ^ 2)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hx2r; exact HX2. }
  assert (CY2 : congr_mod SM2_P_Z y2 (py2 * z2 ^ 3)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hy2r; exact HY2. }
  assert (Hpxneq : px1 <> px2).
  { intro Heq.
    apply Hu.
    apply (congr_mod_eq_canonical SM2_P_Z
      (aj_u1 x1 z2) (aj_u2 x2 z1)).
    - pose proof sm2_p_montgomery_bounds; lia.
    - unfold aj_u1; apply aj_mod_range.
    - unfold aj_u2; apply aj_mod_range.
    - eapply congr_mod_trans.
      + apply aj_u1_affine_scale; exact CX1.
      + apply congr_mod_sym.
        rewrite Heq.
        apply aj_u2_affine_scale; exact CX2. }
  destruct (aj_sm2_point_add_finite_distinct_construct
      px1 py1 px2 py2 HP1 HP2 Hpxneq)
    as [lambda [qx [qy [HQ [Hadd [Hslope [Hqx Hqy]]]]]]].
  set (w := z1 * z2).
  set (d := px1 - px2).
  set (e := py1 - py2).
  set (xnum := e * e - (px1 + px2) * d * d).
  assert (CU1 : congr_mod SM2_P_Z (aj_u1 x1 z2) (px1 * w ^ 2)).
  { unfold w; now apply aj_u1_affine_scale. }
  assert (CU2 : congr_mod SM2_P_Z (aj_u2 x2 z1) (px2 * w ^ 2)).
  { unfold w; now apply aj_u2_affine_scale. }
  assert (CS1 : congr_mod SM2_P_Z (aj_s1 y1 z2) (py1 * w ^ 3)).
  { unfold w; now apply aj_s1_affine_scale. }
  assert (CS2 : congr_mod SM2_P_Z (aj_s2 y2 z1) (py2 * w ^ 3)).
  { unfold w; now apply aj_s2_affine_scale. }
  assert (CH : congr_mod SM2_P_Z (aj_h x1 z1 x2 z2) (d * w ^ 2)).
  { unfold aj_h, d.
    eapply congr_mod_trans; [apply aj_mod_congr|].
    eapply congr_mod_trans.
    - apply congr_mod_sub; [exact CU1|exact CU2].
    - replace (px1 * w ^ 2 - px2 * w ^ 2) with
        ((px1 - px2) * w ^ 2) by ring.
      apply congr_mod_refl. }
  assert (CR : congr_mod SM2_P_Z (aj_rr y1 z1 y2 z2) (e * w ^ 3)).
  { unfold aj_rr, e.
    eapply congr_mod_trans; [apply aj_mod_congr|].
    eapply congr_mod_trans.
    - apply congr_mod_sub; [exact CS1|exact CS2].
    - replace (py1 * w ^ 3 - py2 * w ^ 3) with
        ((py1 - py2) * w ^ 3) by ring.
      apply congr_mod_refl. }
  assert (CUadd : congr_mod SM2_P_Z (aj_u_sum x1 z1 x2 z2)
      ((px1 + px2) * w ^ 2)).
  { unfold aj_u_sum.
    eapply congr_mod_trans; [apply aj_mod_congr|].
    eapply congr_mod_trans.
    - apply congr_mod_add; [exact CU1|exact CU2].
    - replace (px1 * w ^ 2 + px2 * w ^ 2) with
        ((px1 + px2) * w ^ 2) by ring.
      apply congr_mod_refl. }
  assert (CSadd : congr_mod SM2_P_Z (aj_s_sum y1 z1 y2 z2)
      ((py1 + py2) * w ^ 3)).
  { unfold aj_s_sum.
    eapply congr_mod_trans; [apply aj_mod_congr|].
    eapply congr_mod_trans.
    - apply congr_mod_add; [exact CS1|exact CS2].
    - replace (py1 * w ^ 3 + py2 * w ^ 3) with
        ((py1 + py2) * w ^ 3) by ring.
      apply congr_mod_refl. }
  assert (CH2 : congr_mod SM2_P_Z (aj_h2 x1 z1 x2 z2)
      (d * d * w ^ 4)).
  { unfold aj_h2.
    eapply congr_mod_trans; [apply aj_mod_congr|].
    pose proof (congr_mod_mul SM2_P_Z _ _ _ _ CH CH) as H.
    eapply congr_mod_trans; [exact H|].
    replace ((d * w ^ 2) * (d * w ^ 2)) with (d * d * w ^ 4) by ring.
    apply congr_mod_refl. }
  assert (CR2 : congr_mod SM2_P_Z (aj_rr2 y1 z1 y2 z2)
      (e * e * w ^ 6)).
  { unfold aj_rr2.
    eapply congr_mod_trans; [apply aj_mod_congr|].
    pose proof (congr_mod_mul SM2_P_Z _ _ _ _ CR CR) as H.
    eapply congr_mod_trans; [exact H|].
    replace ((e * w ^ 3) * (e * w ^ 3)) with (e * e * w ^ 6) by ring.
    apply congr_mod_refl. }
  assert (CBase : congr_mod SM2_P_Z (aj_base x1 z1 x2 z2)
      ((px1 + px2) * d * d * w ^ 6)).
  { unfold aj_base.
    eapply congr_mod_trans; [apply aj_mod_congr|].
    pose proof (congr_mod_mul SM2_P_Z _ _ _ _ CUadd CH2) as H.
    eapply congr_mod_trans; [exact H|].
    replace (((px1 + px2) * w ^ 2) * (d * d * w ^ 4)) with
      ((px1 + px2) * d * d * w ^ 6) by ring.
    apply congr_mod_refl. }
  assert (CRX : congr_mod SM2_P_Z (aj_rx x1 y1 z1 x2 y2 z2)
      (xnum * w ^ 6)).
  { unfold aj_rx, xnum.
    eapply congr_mod_trans; [apply aj_mod_congr|].
    eapply congr_mod_trans.
    - apply congr_mod_sub; [exact CR2|exact CBase].
    - replace
        (e * e * w ^ 6 - (px1 + px2) * d * d * w ^ 6) with
        ((e * e - (px1 + px2) * d * d) * w ^ 6) by ring.
      apply congr_mod_refl. }
  assert (CZB : congr_mod SM2_P_Z (aj_zbase z1 z2) w).
  { unfold aj_zbase, w. apply aj_mod_congr. }
  assert (CRZ : congr_mod SM2_P_Z (aj_rz x1 z1 x2 z2) (d * w ^ 3)).
  { unfold aj_rz.
    eapply congr_mod_trans; [apply aj_mod_congr|].
    pose proof (congr_mod_mul SM2_P_Z _ _ _ _ CZB CH) as H.
    eapply congr_mod_trans; [exact H|].
    replace (w * (d * w ^ 2)) with (d * w ^ 3) by ring.
    apply congr_mod_refl. }
  assert (CXnum : congr_mod SM2_P_Z xnum
      ((lambda * lambda - px1 - px2) * d * d)).
  { unfold xnum, d, e.
    exact (aj_x_numerator_matches_raw_affine
      px1 py1 px2 py2 lambda Hslope). }
  assert (CQX : congr_mod SM2_P_Z qx (lambda * lambda - px1 - px2)).
  { rewrite Hqx. apply aj_mod_congr. }
  assert (CXnumQ : congr_mod SM2_P_Z xnum (qx * d * d)).
  { eapply congr_mod_trans; [exact CXnum|].
    apply congr_mod_sym.
    apply congr_mod_mul.
    - apply congr_mod_mul; [exact CQX|apply congr_mod_refl].
    - apply congr_mod_refl. }
  assert (CRXQ : congr_mod SM2_P_Z
      (aj_rx x1 y1 z1 x2 y2 z2)
      (qx * aj_rz x1 z1 x2 z2 ^ 2)).
  { eapply congr_mod_trans; [exact CRX|].
    eapply congr_mod_trans with (b := (qx * d * d) * w ^ 6).
    - apply congr_mod_mul; [exact CXnumQ|apply congr_mod_refl].
    - pose proof (congr_mod_pow2 SM2_P_Z _ _ CRZ) as HRZ2.
      apply congr_mod_sym in HRZ2.
      eapply congr_mod_trans.
      + replace ((qx * d * d) * w ^ 6) with
          (qx * (d * w ^ 3) ^ 2) by ring.
        apply congr_mod_refl.
      + apply congr_mod_mul; [apply congr_mod_refl|exact HRZ2]. }
  assert (CLeft : congr_mod SM2_P_Z
      (aj_left_y x1 y1 z1 x2 y2 z2)
      (((px1 + px2) * d * d - 2 * xnum) * e * w ^ 9)).
  { unfold aj_left_y, aj_base_minus_twice_rx, aj_twice_rx.
    eapply congr_mod_trans; [apply aj_mod_congr|].
    assert (CTwoRX : congr_mod SM2_P_Z
        ((2 * aj_rx x1 y1 z1 x2 y2 z2) mod SM2_P_Z)
        (2 * xnum * w ^ 6)).
    { eapply congr_mod_trans; [apply aj_mod_congr|].
      pose proof (congr_mod_scale SM2_P_Z 2 _ _ CRX) as H.
      eapply congr_mod_trans; [exact H|].
      replace (2 * (xnum * w ^ 6)) with (2 * xnum * w ^ 6) by ring.
      apply congr_mod_refl. }
    assert (CDiff : congr_mod SM2_P_Z
        ((aj_base x1 z1 x2 z2 -
          ((2 * aj_rx x1 y1 z1 x2 y2 z2) mod SM2_P_Z)) mod SM2_P_Z)
        (((px1 + px2) * d * d - 2 * xnum) * w ^ 6)).
    { eapply congr_mod_trans; [apply aj_mod_congr|].
      eapply congr_mod_trans.
      - apply congr_mod_sub; [exact CBase|exact CTwoRX].
      - replace
          ((px1 + px2) * d * d * w ^ 6 - 2 * xnum * w ^ 6) with
          (((px1 + px2) * d * d - 2 * xnum) * w ^ 6) by ring.
        apply congr_mod_refl. }
    pose proof (congr_mod_mul SM2_P_Z _ _ _ _ CDiff CR) as H.
    eapply congr_mod_trans; [exact H|].
    replace
      (((px1 + px2) * d * d - 2 * xnum) * w ^ 6 * (e * w ^ 3)) with
      (((px1 + px2) * d * d - 2 * xnum) * e * w ^ 9) by ring.
    apply congr_mod_refl. }
  assert (CRight : congr_mod SM2_P_Z
      (aj_right_y x1 y1 z1 x2 y2 z2)
      (((py1 + py2) * d * d) * d * w ^ 9)).
  { unfold aj_right_y.
    eapply congr_mod_trans; [apply aj_mod_congr|].
    pose proof (congr_mod_mul SM2_P_Z _ _ _ _ CSadd CH2) as H1.
    pose proof (congr_mod_mul SM2_P_Z _ _ _ _ H1 CH) as H2.
    eapply congr_mod_trans; [exact H2|].
    replace
      ((((py1 + py2) * w ^ 3) * (d * d * w ^ 4)) * (d * w ^ 2)) with
      (((py1 + py2) * d * d) * d * w ^ 9) by ring.
    apply congr_mod_refl. }
  assert (CYN : congr_mod SM2_P_Z
      (aj_y_num x1 y1 z1 x2 y2 z2)
      ((((px1 + px2) * d * d - 2 * xnum) * e -
        ((py1 + py2) * d * d) * d) * w ^ 9)).
  { unfold aj_y_num.
    eapply congr_mod_trans; [apply aj_mod_congr|].
    eapply congr_mod_trans.
    - apply congr_mod_sub; [exact CLeft|exact CRight].
    - replace
        (((px1 + px2) * d * d - 2 * xnum) * e * w ^ 9 -
         ((py1 + py2) * d * d) * d * w ^ 9) with
        ((((px1 + px2) * d * d - 2 * xnum) * e -
          ((py1 + py2) * d * d) * d) * w ^ 9) by ring.
      apply congr_mod_refl. }
  assert (CYraw : congr_mod SM2_P_Z
      (((px1 + px2) * d * d - 2 * xnum) * e -
       ((py1 + py2) * d * d) * d)
      (2 * (lambda * (px1 - (lambda * lambda - px1 - px2)) - py1) *
       d ^ 3)).
  { unfold xnum, d, e.
    exact (aj_y_numerator_matches_raw_affine
      px1 py1 px2 py2 lambda Hslope). }
  assert (CQY : congr_mod SM2_P_Z qy
      (lambda * (px1 - (lambda * lambda - px1 - px2)) - py1)).
  { eapply congr_mod_trans with
      (b := lambda * (px1 - qx) - py1).
    - rewrite Hqy. apply aj_mod_congr.
    - apply congr_mod_sub.
      + apply congr_mod_mul; [apply congr_mod_refl|].
        apply congr_mod_sub; [apply congr_mod_refl|exact CQX].
      + apply congr_mod_refl. }
  assert (CYNhalf : congr_mod SM2_P_Z
      (aj_y_num x1 y1 z1 x2 y2 z2)
      (2 * (qy * d ^ 3 * w ^ 9))).
  { eapply congr_mod_trans; [exact CYN|].
    eapply congr_mod_trans with
      (b := (2 *
        (lambda * (px1 - (lambda * lambda - px1 - px2)) - py1) *
        d ^ 3) * w ^ 9).
    - apply congr_mod_mul; [exact CYraw|apply congr_mod_refl].
    - pose proof (congr_mod_mul SM2_P_Z
        qy (lambda * (px1 - (lambda * lambda - px1 - px2)) - py1)
        (d ^ 3) (d ^ 3) CQY (congr_mod_refl _ _)) as H1.
      pose proof (congr_mod_mul SM2_P_Z
        (qy * d ^ 3)
        ((lambda * (px1 - (lambda * lambda - px1 - px2)) - py1) * d ^ 3)
        (w ^ 9) (w ^ 9) H1 (congr_mod_refl _ _)) as H2.
      pose proof (congr_mod_scale SM2_P_Z 2 _ _ H2) as H3.
      replace
        (2 *
          ((lambda * (px1 - (lambda * lambda - px1 - px2)) - py1) *
           d ^ 3 * w ^ 9)) with
        (2 * (lambda * (px1 - (lambda * lambda - px1 - px2)) - py1) *
         d ^ 3 * w ^ 9) in H3 by ring.
      apply congr_mod_sym; exact H3. }
  assert (CRY0 : congr_mod SM2_P_Z
      (aj_ry x1 y1 z1 x2 y2 z2) (qy * d ^ 3 * w ^ 9)).
  { unfold aj_ry. now apply aj_inv2_congr_half. }
  assert (CRYQ : congr_mod SM2_P_Z
      (aj_ry x1 y1 z1 x2 y2 z2)
      (qy * aj_rz x1 z1 x2 z2 ^ 3)).
  { eapply congr_mod_trans; [exact CRY0|].
    pose proof (congr_mod_pow3 SM2_P_Z _ _ CRZ) as HRZ3.
    apply congr_mod_sym in HRZ3.
    eapply congr_mod_trans.
    - replace (qy * d ^ 3 * w ^ 9) with
        (qy * (d * w ^ 3) ^ 3) by ring.
      apply congr_mod_refl.
    - apply congr_mod_mul; [apply congr_mod_refl|exact HRZ3]. }
  assert (HRZ0 : aj_rz x1 z1 x2 z2 <> 0).
  { now apply aj_rz_nonzero. }
  assert (Hout : jpoint_represents
      (aj_rx x1 y1 z1 x2 y2 z2)
      (aj_ry x1 y1 z1 x2 y2 z2)
      (aj_rz x1 z1 x2 z2) (ec_point_of_affine qx qy HQ)).
  { apply (aj_projective_represents_affine
      (aj_rx x1 y1 z1 x2 y2 z2)
      (aj_ry x1 y1 z1 x2 y2 z2)
      (aj_rz x1 z1 x2 z2) qx qy HQ); try assumption.
    - unfold aj_rx; apply aj_mod_range.
    - unfold aj_ry; apply aj_mod_range.
    - unfold aj_rz; apply aj_mod_range. }
  assert (HP1_affine :
    @SMain.curve_elt
      (ZEll.pK SM2_P_Z)
      (ZEll.pkI SM2_P_Z) (@ZEll.pkplus SM2_P_Z)
      (@ZEll.pkmul SM2_P_Z)
      (ZEll.pA SM2_A_Z SM2_P_Z) (ZEll.pB SM2_B_Z SM2_P_Z)
      px1_fe py1_fe HP1_fe =
    ec_point_of_affine px1 py1 HP1).
  { apply ec_point_of_affine_complete.
    cbn [ec_point_affine_coordinates].
    split; reflexivity. }
  assert (HP2_affine :
    @SMain.curve_elt
      (ZEll.pK SM2_P_Z)
      (ZEll.pkI SM2_P_Z) (@ZEll.pkplus SM2_P_Z)
      (@ZEll.pkmul SM2_P_Z)
      (ZEll.pA SM2_A_Z SM2_P_Z) (ZEll.pB SM2_B_Z SM2_P_Z)
      px2_fe py2_fe HP2_fe =
    ec_point_of_affine px2 py2 HP2).
  { apply ec_point_of_affine_complete.
    cbn [ec_point_affine_coordinates].
    split; reflexivity. }
  unfold aj_result_refines.
  rewrite HP1_affine, HP2_affine, Hadd.
  split; [exact Hout|].
  unfold jpoint_canonical_infinity_encoding.
  discriminate.
Qed.

Lemma aj_result_refines_generic_trace_case :
  forall x1 y1 z1 x2 y2 z2 P1 P2,
    jpoint_represents x1 y1 z1 P1 ->
    jpoint_represents x2 y2 z2 P2 ->
    z1 <> 0 -> z2 <> 0 ->
    aj_generic_trace_case x1 y1 z1 x2 y2 z2 ->
    aj_result_refines P1 P2 x1 y1 z1 x2 y2 z2.
Proof.
  intros x1 y1 z1 x2 y2 z2 P1 P2 HR1 HR2 Hz1 Hz2 Hcase.
  unfold aj_generic_trace_case in Hcase.
  destruct Hcase as [Hu | [Hu [Hs Hsum]]].
  - now apply aj_result_refines_finite_distinct.
  - exfalso; apply Hsum.
    now apply (aj_same_u_different_s_implies_s_sum_zero
      x1 y1 z1 x2 y2 z2 P1 P2).
Qed.
