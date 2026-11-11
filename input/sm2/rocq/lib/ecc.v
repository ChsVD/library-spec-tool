Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.Applications_human.sm2.lib
  Require Export sm2_common_lib sm2_curve ecc_point_def sm2_c_layout.
From SimpleC.EE.Applications_human.sm2.lib Require Import sm2_primality.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Import Snaive_C_Rules.
Import ListNotations.
Local Open Scope sac.

(** * Coordinate representations *)

(** The C affine representation uses [(0, 0)] for the point at infinity. *)
Definition afpoint_infinity (x y : Z) : Prop :=
  x = 0 /\ y = 0.

(** A Jacobian point represents the point at infinity exactly when [z = 0]. *)
Definition jpoint_infinity (z : Z) : Prop :=
  z = 0.

(** The distinguished Jacobian infinity value used by the C implementation. *)
Definition canonical_jpoint_infinity (x y z : Z) : Prop :=
  x = 1 /\ y = 1 /\ z = 0.

(** Pure form of the API invariant that only infinity needs the
    distinguished Jacobian encoding. *)
Definition jpoint_canonical_infinity_encoding
    (x y z : Z) (point : ec_point) : Prop :=
  point = ECInfinity -> canonical_jpoint_infinity x y z.

(** Exact coordinate conversion performed by [affine_to_jacobian]. *)
Definition afpoint_to_jpoint_coordinates
    (x y result_x result_y result_z : Z) : Prop :=
  (afpoint_infinity x y /\
   canonical_jpoint_infinity result_x result_y result_z) \/
  ((x <> 0 \/ y <> 0) /\
   result_x = x /\ result_y = y /\ result_z = 1).

(** Exact inverse-based normalization performed by [jacobian_to_affine]. *)
Definition jpoint_to_afpoint_coordinates
    (x y z result_x result_y : Z) : Prop :=
  (canonical_jpoint_infinity x y z /\
   afpoint_infinity result_x result_y) \/
  (z <> 0 /\
   exists z_inverse,
     0 <= z_inverse < SM2_P_Z /\
     (z * z_inverse) mod SM2_P_Z = 1 /\
     result_x = (x * z_inverse ^ 2) mod SM2_P_Z /\
     result_y = (y * z_inverse ^ 3) mod SM2_P_Z).

(** Canonical affine coordinates representing one abstract SM2 point. *)
Definition afpoint_represents (x y : Z) (point : ec_point) : Prop :=
  match point with
  | SMain.inf_elt _ _ _ _ _ => afpoint_infinity x y
  | @SMain.curve_elt _ _ _ _ _ _ point_x point_y _ =>
      x = sm2_fe_value point_x /\
      y = sm2_fe_value point_y
  end.

Lemma afpoint_represents_bounds :
  forall x y point,
    afpoint_represents x y point ->
    0 <= x < SM2_P_Z /\ 0 <= y < SM2_P_Z.
Proof.
  intros x y point Hrepresents.
  destruct point as [|point_x point_y Hcurve].
  - cbn [afpoint_represents afpoint_infinity] in Hrepresents.
    destruct Hrepresents as [-> ->].
    pose proof sm2_p_montgomery_bounds as [[Hp _] _].
    lia.
  - cbn [afpoint_represents] in Hrepresents.
    destruct Hrepresents as [-> ->].
    split; apply sm2_fe_value_bounds.
Qed.

Lemma afpoint_represents_functional :
  forall x1 y1 x2 y2 point,
    afpoint_represents x1 y1 point ->
    afpoint_represents x2 y2 point ->
    x1 = x2 /\ y1 = y2.
Proof.
  intros x1 y1 x2 y2 point Hleft Hright.
  destruct point as [|point_x point_y Hcurve];
    cbn [afpoint_represents afpoint_infinity] in Hleft, Hright;
    destruct Hleft; destruct Hright; split; congruence.
Qed.

(** Canonical Jacobian coordinates representing one abstract SM2 point. *)
Definition jpoint_represents
    (x y z : Z) (point : ec_point) : Prop :=
  0 <= x < SM2_P_Z /\
  0 <= y < SM2_P_Z /\
  0 <= z < SM2_P_Z /\
  match point with
  | SMain.inf_elt _ _ _ _ _ => jpoint_infinity z
  | @SMain.curve_elt _ _ _ _ _ _ point_x point_y _ =>
      z <> 0 /\
      x = (sm2_fe_value point_x * z ^ 2) mod SM2_P_Z /\
      y = (sm2_fe_value point_y * z ^ 3) mod SM2_P_Z
  end.

(** Coordinates accepted by the public affine-point checker. *)
Definition valid_afpoint (x y : Z) : Prop :=
  (x = 0 /\ y = 0) \/
  (0 <= x < SM2_P_Z /\
   0 <= y < SM2_P_Z /\
   (y * y) mod SM2_P_Z =
     (x * x * x + SM2_A_Z * x + SM2_B_Z) mod SM2_P_Z).

Definition valid_jpoint (x y z : Z) : Prop :=
  exists point, jpoint_represents x y z point.

Lemma valid_afpoint_iff :
  forall x y,
  valid_afpoint x y <->
    exists point, afpoint_represents x y point.
Proof.
  intros x y.
  split.
  - intros [[Hx Hy] | [Hx [Hy Hequation]]].
    + exists ECInfinity.
      cbn [afpoint_represents afpoint_infinity].
      split; assumption.
    + assert (Hon_curve : sm2_affine_on_curve x y).
      { unfold sm2_affine_on_curve.
        split; [exact Hx |].
        split; [exact Hy |].
        apply (proj2 (sm2_affine_equation_iff x y)).
        exact Hequation. }
      exists (ec_point_of_affine x y Hon_curve).
      exact (ec_point_of_affine_coordinates x y Hon_curve).
  - intros [point Hrep].
    destruct point as [|point_x point_y Hcurve].
    + left. exact Hrep.
    + right.
      cbn [afpoint_represents] in Hrep.
      destruct Hrep as [-> ->].
      split; [apply sm2_fe_value_bounds |].
      split; [apply sm2_fe_value_bounds |].
      apply (proj1
        (sm2_affine_equation_iff
          (sm2_fe_value point_x) (sm2_fe_value point_y))).
      unfold sm2_affine_equation.
      repeat rewrite sm2_fe_of_Z_value.
      exact Hcurve.
Qed.

Lemma afpoint_represents_on_curve_complete :
  forall x y point (Hon_curve : sm2_affine_on_curve x y),
    afpoint_represents x y point ->
    point = ec_point_of_affine x y Hon_curve.
Proof.
  intros x y point Hon_curve Hrepresents.
  destruct point as [|point_x point_y Hcurve].
  - cbn [afpoint_represents afpoint_infinity] in Hrepresents.
    destruct Hrepresents as [-> ->].
    exfalso.
    destruct Hon_curve as [_ [_ Hon_curve]].
    apply sm2_affine_equation_iff in Hon_curve.
    vm_compute in Hon_curve.
    discriminate Hon_curve.
  - apply ec_point_of_affine_complete.
    exact Hrepresents.
Qed.

Lemma valid_afpoint_equation_iff :
  forall x y,
    valid_afpoint x y <->
    (x = 0 /\ y = 0) \/
    (0 <= x < SM2_P_Z /\
     0 <= y < SM2_P_Z /\
     (y * y) mod SM2_P_Z =
       (x * x * x + SM2_A_Z * x + SM2_B_Z) mod SM2_P_Z).
Proof.
  intros x y.
  unfold valid_afpoint.
  reflexivity.
Qed.

(** The sequence of modular multiplications and additions used by
    [is_on_curve] computes the canonical right-hand side of the SM2 curve
    equation. *)
Lemma sm2_curve_rhs_mod :
  forall x,
    (((x * ((x * x) mod SM2_P_Z)) mod SM2_P_Z +
       (SM2_A_Z * x) mod SM2_P_Z) mod SM2_P_Z +
      SM2_B_Z) mod SM2_P_Z =
    (x * x * x + SM2_A_Z * x + SM2_B_Z) mod SM2_P_Z.
Proof.
  intros x.
  assert (Hp : 0 < SM2_P_Z).
  { pose proof sm2_a_bounds. lia. }
  rewrite <-
    (Z.add_mod
       (x * ((x * x) mod SM2_P_Z))
       (SM2_A_Z * x)
       SM2_P_Z)
    by lia.
  rewrite Z.add_mod_idemp_l by lia.
  replace
    (x * ((x * x) mod SM2_P_Z) + SM2_A_Z * x + SM2_B_Z)
    with
    (x * ((x * x) mod SM2_P_Z) +
     (SM2_A_Z * x + SM2_B_Z))
    by apply Z.add_assoc.
  rewrite <- Z.add_mod_idemp_l by lia.
  rewrite Z.mul_mod_idemp_r by lia.
  rewrite Z.add_mod_idemp_l by lia.
  f_equal.
  rewrite Z.mul_assoc.
  rewrite Z.add_assoc.
  reflexivity.
Qed.

Lemma sm2_origin_not_on_curve :
  ~ sm2_affine_on_curve 0 0.
Proof.
  intros [_ [_ Hcurve]].
  apply sm2_affine_equation_iff in Hcurve.
  vm_compute in Hcurve.
  discriminate Hcurve.
Qed.

(** * The SM2 curve has no affine point of order two *)

Module Sm2NoTwoTorsionCertificate.

Record cubic_residue : Type := {
  cubic_c0 : Z;
  cubic_c1 : Z;
  cubic_c2 : Z
}.

Definition cubic_eval (r : cubic_residue) (x : Z) : Z :=
  cubic_c0 r + cubic_c1 r * x + cubic_c2 r * x * x.

Definition cubic_norm (r : cubic_residue) : cubic_residue :=
  {| cubic_c0 := cubic_c0 r mod SM2_P_Z;
     cubic_c1 := cubic_c1 r mod SM2_P_Z;
     cubic_c2 := cubic_c2 r mod SM2_P_Z |}.

Definition cubic_mul_raw_with
    (coefficient_a coefficient_b : Z)
    (r s : cubic_residue) : cubic_residue :=
  let degree3 := cubic_c1 r * cubic_c2 s + cubic_c2 r * cubic_c1 s in
  let degree4 := cubic_c2 r * cubic_c2 s in
  {| cubic_c0 :=
       cubic_c0 r * cubic_c0 s - coefficient_b * degree3;
     cubic_c1 :=
       cubic_c0 r * cubic_c1 s + cubic_c1 r * cubic_c0 s -
       coefficient_a * degree3 - coefficient_b * degree4;
     cubic_c2 :=
       cubic_c0 r * cubic_c2 s + cubic_c1 r * cubic_c1 s +
       cubic_c2 r * cubic_c0 s - coefficient_a * degree4 |}.

Definition cubic_mul_raw (r s : cubic_residue) : cubic_residue :=
  cubic_mul_raw_with SM2_A_Z SM2_B_Z r s.

Definition cubic_mul (r s : cubic_residue) : cubic_residue :=
  cubic_norm (cubic_mul_raw r s).

Fixpoint cubic_pow_pos (r : cubic_residue) (exponent : positive)
    : cubic_residue :=
  match exponent with
  | xH => r
  | xO half =>
      let powered := cubic_pow_pos r half in
      cubic_mul powered powered
  | xI half =>
      let powered := cubic_pow_pos r half in
      cubic_mul r (cubic_mul powered powered)
  end.

Definition cubic_eqmod (left right : Z) : Prop :=
  left mod SM2_P_Z = right mod SM2_P_Z.

Lemma cubic_eqmod_refl : forall x, cubic_eqmod x x.
Proof. intros x. reflexivity. Qed.

Lemma cubic_eqmod_trans :
  forall x y z,
    cubic_eqmod x y -> cubic_eqmod y z -> cubic_eqmod x z.
Proof. intros x y z Hxy Hyz. unfold cubic_eqmod in *. congruence. Qed.

Lemma cubic_eqmod_add :
  forall a b c d,
    cubic_eqmod a b -> cubic_eqmod c d ->
    cubic_eqmod (a + c) (b + d).
Proof.
  intros a b c d Hab Hcd.
  unfold cubic_eqmod in *.
  rewrite (Z.add_mod a c SM2_P_Z) by (pose proof sm2_p_gt_one; lia).
  rewrite (Z.add_mod b d SM2_P_Z) by (pose proof sm2_p_gt_one; lia).
  now rewrite Hab, Hcd.
Qed.

Lemma cubic_eqmod_mul :
  forall a b c d,
    cubic_eqmod a b -> cubic_eqmod c d ->
    cubic_eqmod (a * c) (b * d).
Proof.
  intros a b c d Hab Hcd.
  unfold cubic_eqmod in *.
  rewrite (Z.mul_mod a c SM2_P_Z) by (pose proof sm2_p_gt_one; lia).
  rewrite (Z.mul_mod b d SM2_P_Z) by (pose proof sm2_p_gt_one; lia).
  now rewrite Hab, Hcd.
Qed.

Lemma cubic_norm_eval_eqmod :
  forall r x, cubic_eqmod (cubic_eval (cubic_norm r) x) (cubic_eval r x).
Proof.
  intros [r0 r1 r2] x.
  unfold cubic_norm, cubic_eval; cbn.
  apply cubic_eqmod_add.
  - apply cubic_eqmod_add.
    + unfold cubic_eqmod.
      rewrite Z.mod_mod by (pose proof sm2_p_gt_one; lia).
      reflexivity.
    + apply cubic_eqmod_mul.
      * unfold cubic_eqmod.
        rewrite Z.mod_mod by (pose proof sm2_p_gt_one; lia).
        reflexivity.
      * apply cubic_eqmod_refl.
  - apply cubic_eqmod_mul.
    + apply cubic_eqmod_mul.
      * unfold cubic_eqmod.
        rewrite Z.mod_mod by (pose proof sm2_p_gt_one; lia).
        reflexivity.
      * apply cubic_eqmod_refl.
    + apply cubic_eqmod_refl.
Qed.

Lemma cubic_mul_raw_with_eval :
  forall coefficient_a coefficient_b r s x,
    cubic_eval (cubic_mul_raw_with coefficient_a coefficient_b r s) x =
    cubic_eval r x * cubic_eval s x -
    (cubic_c1 r * cubic_c2 s + cubic_c2 r * cubic_c1 s +
     cubic_c2 r * cubic_c2 s * x) *
    (x * x * x + coefficient_a * x + coefficient_b).
Proof.
  intros coefficient_a coefficient_b [r0 r1 r2] [s0 s1 s2] x.
  unfold cubic_mul_raw_with, cubic_eval; cbn.
  ring.
Qed.

Lemma cubic_mul_raw_eval :
  forall r s x,
    cubic_eval (cubic_mul_raw r s) x =
    cubic_eval r x * cubic_eval s x -
    (cubic_c1 r * cubic_c2 s + cubic_c2 r * cubic_c1 s +
     cubic_c2 r * cubic_c2 s * x) *
    (x * x * x + SM2_A_Z * x + SM2_B_Z).
Proof.
  intros r s x.
  unfold cubic_mul_raw.
  apply cubic_mul_raw_with_eval.
Qed.

Lemma cubic_mul_eval_eqmod :
  forall r s x,
    (x * x * x + SM2_A_Z * x + SM2_B_Z) mod SM2_P_Z = 0 ->
    cubic_eqmod
      (cubic_eval (cubic_mul r s) x)
      (cubic_eval r x * cubic_eval s x).
Proof.
  intros r s x Hroot.
  eapply cubic_eqmod_trans.
  - apply cubic_norm_eval_eqmod.
  - rewrite cubic_mul_raw_eval.
    unfold cubic_eqmod.
    rewrite Zminus_mod.
    rewrite (Z.mul_mod
      (cubic_c1 r * cubic_c2 s + cubic_c2 r * cubic_c1 s +
       cubic_c2 r * cubic_c2 s * x)
      (x * x * x + SM2_A_Z * x + SM2_B_Z)
      SM2_P_Z) by (pose proof sm2_p_gt_one; lia).
    rewrite Hroot, Z.mul_0_r.
    rewrite Z.mod_0_l by (pose proof sm2_p_gt_one; lia).
    rewrite Z.sub_0_r.
    rewrite Z.mod_mod by (pose proof sm2_p_gt_one; lia).
    reflexivity.
Qed.

Lemma cubic_pow_pos_eval_eqmod :
  forall exponent r x,
    (x * x * x + SM2_A_Z * x + SM2_B_Z) mod SM2_P_Z = 0 ->
    cubic_eqmod
      (cubic_eval (cubic_pow_pos r exponent) x)
      (cubic_eval r x ^ Z.pos exponent).
Proof.
  intros exponent.
  induction exponent as [half IH | half IH |].
  - intros r x Hroot. cbn [cubic_pow_pos].
    eapply cubic_eqmod_trans.
    + apply cubic_mul_eval_eqmod. exact Hroot.
    + eapply cubic_eqmod_trans.
      * apply cubic_eqmod_mul.
        -- apply cubic_eqmod_refl.
        -- eapply cubic_eqmod_trans.
           ++ apply cubic_mul_eval_eqmod. exact Hroot.
           ++ apply cubic_eqmod_mul; apply IH; exact Hroot.
      * unfold cubic_eqmod.
        replace (Z.pos (xI half)) with
          (1 + (Z.pos half + Z.pos half)) by lia.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_1_r.
        rewrite Z.pow_add_r by lia.
        reflexivity.
  - intros r x Hroot. cbn [cubic_pow_pos].
    eapply cubic_eqmod_trans.
    + apply cubic_mul_eval_eqmod. exact Hroot.
    + eapply cubic_eqmod_trans.
      * apply cubic_eqmod_mul; apply IH; exact Hroot.
      * unfold cubic_eqmod.
        replace (Z.pos (xO half)) with
          (Z.pos half + Z.pos half) by lia.
        rewrite Z.pow_add_r by lia.
        reflexivity.
  - intros r x Hroot. cbn [cubic_pow_pos].
    unfold cubic_eqmod.
    rewrite Z.pow_1_r.
    reflexivity.
Qed.

Definition cubic_x : cubic_residue :=
  {| cubic_c0 := 0; cubic_c1 := 1; cubic_c2 := 0 |}.

Lemma cubic_x_eval : forall x, cubic_eval cubic_x x = x.
Proof.
  intros x.
  change (0 + 1 * x + 0 * x * x = x).
  ring.
Qed.

Definition sm2_cubic_fermat_remainder : cubic_residue :=
  {| cubic_c0 :=
       24241843467033289261822167031801059841470004286498168969055675753862713640179;
     cubic_c1 :=
       11924795065368500245190788640598551301948517221217076382674152911949953289256;
     cubic_c2 :=
       45775122871661479747299089091109916462390174852713011242682759089713485675910 |}.

Lemma sm2_cubic_fermat_remainder_correct :
  cubic_pow_pos cubic_x (Z.to_pos SM2_P_Z) =
  sm2_cubic_fermat_remainder.
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition cubic_sub_x (r : cubic_residue) : cubic_residue :=
  {| cubic_c0 := cubic_c0 r;
     cubic_c1 := cubic_c1 r - 1;
     cubic_c2 := cubic_c2 r |}.

Lemma cubic_sub_x_eval :
  forall r x,
    cubic_eval (cubic_sub_x r) x = cubic_eval r x - x.
Proof.
  intros [r0 r1 r2] x.
  unfold cubic_sub_x, cubic_eval; cbn.
  ring.
Qed.

Definition sm2_cubic_fermat_difference : cubic_residue :=
  cubic_sub_x sm2_cubic_fermat_remainder.

Definition cubic_coefficients (r : cubic_residue) : list Z :=
  cubic_c0 r :: cubic_c1 r :: cubic_c2 r :: nil.

Fixpoint polynomial_eval (coefficients : list Z) (x : Z) : Z :=
  match coefficients with
  | nil => 0
  | coefficient :: remaining =>
      coefficient + x * polynomial_eval remaining x
  end.

Fixpoint polynomial_add (left right : list Z) : list Z :=
  match left, right with
  | nil, _ => right
  | _, nil => left
  | left_head :: left_tail, right_head :: right_tail =>
      (left_head + right_head) ::
      polynomial_add left_tail right_tail
  end.

Fixpoint polynomial_scale (factor : Z) (polynomial : list Z) : list Z :=
  match polynomial with
  | nil => nil
  | coefficient :: remaining =>
      factor * coefficient :: polynomial_scale factor remaining
  end.

Fixpoint polynomial_mul (left right : list Z) : list Z :=
  match left with
  | nil => nil
  | coefficient :: remaining =>
      polynomial_add
        (polynomial_scale coefficient right)
        (0 :: polynomial_mul remaining right)
  end.

Definition polynomial_norm (polynomial : list Z) : list Z :=
  List.map (fun coefficient => coefficient mod SM2_P_Z) polynomial.

Lemma polynomial_add_eval :
  forall left right x,
    polynomial_eval (polynomial_add left right) x =
    polynomial_eval left x + polynomial_eval right x.
Proof.
  induction left as [|left_head left_tail IH];
    intros [|right_head right_tail] x; cbn; try ring.
  rewrite IH.
  ring.
Qed.

Lemma polynomial_scale_eval :
  forall factor polynomial x,
    polynomial_eval (polynomial_scale factor polynomial) x =
    factor * polynomial_eval polynomial x.
Proof.
  intros factor polynomial.
  induction polynomial as [|coefficient remaining IH];
    intros x; cbn; try ring.
  rewrite IH.
  ring.
Qed.

Lemma polynomial_mul_eval :
  forall left right x,
    polynomial_eval (polynomial_mul left right) x =
    polynomial_eval left x * polynomial_eval right x.
Proof.
  induction left as [|coefficient remaining IH];
    intros right x; cbn; try ring.
  rewrite polynomial_add_eval.
  rewrite polynomial_scale_eval.
  cbn [polynomial_eval].
  rewrite IH.
  ring.
Qed.

Lemma polynomial_norm_eval_eqmod :
  forall polynomial x,
    cubic_eqmod
      (polynomial_eval (polynomial_norm polynomial) x)
      (polynomial_eval polynomial x).
Proof.
  induction polynomial as [|coefficient remaining IH]; intros x.
  - apply cubic_eqmod_refl.
  - cbn [polynomial_norm polynomial_eval List.map].
    apply cubic_eqmod_add.
    + unfold cubic_eqmod.
      rewrite Z.mod_mod by (pose proof sm2_p_gt_one; lia).
      reflexivity.
    + apply cubic_eqmod_mul.
      * apply cubic_eqmod_refl.
      * apply IH.
Qed.

Lemma cubic_coefficients_eval :
  forall r x,
    polynomial_eval (cubic_coefficients r) x = cubic_eval r x.
Proof.
  intros [r0 r1 r2] x.
  unfold cubic_coefficients, polynomial_eval, cubic_eval; cbn.
  ring.
Qed.

Definition sm2_curve_polynomial : list Z :=
  SM2_B_Z :: SM2_A_Z :: 0 :: 1 :: nil.

Lemma cubic_polynomial_eval :
  forall coefficient_a coefficient_b x,
    polynomial_eval
      (coefficient_b :: coefficient_a :: 0 :: 1 :: nil) x =
    x * x * x + coefficient_a * x + coefficient_b.
Proof.
  intros coefficient_a coefficient_b x.
  cbn [polynomial_eval].
  ring.
Qed.

Lemma sm2_curve_polynomial_eval :
  forall x,
    polynomial_eval sm2_curve_polynomial x =
    x * x * x + SM2_A_Z * x + SM2_B_Z.
Proof.
  intros x.
  unfold sm2_curve_polynomial.
  apply cubic_polynomial_eval.
Qed.

Definition sm2_cubic_bezout_left : list Z :=
  33061160807029584433984820566486306066082868608953260424773038747806185531060 ::
  28300541144467212999486884716381389349126416487140647343748535711944319893083 ::
  nil.

Definition sm2_cubic_bezout_right : list Z :=
  106557179798172127300574136655860231618341984660982404479791742557385015191369 ::
  84996361976986330174717689059298811725079258493181573729141059899368768071857 ::
  35585630630933897022180037835235642085639273520660122098341330484096648951663 ::
  nil.

Definition sm2_cubic_bezout_result : list Z :=
  polynomial_norm
    (polynomial_add
      (polynomial_mul sm2_cubic_bezout_left sm2_curve_polynomial)
      (polynomial_mul sm2_cubic_bezout_right
        (cubic_coefficients sm2_cubic_fermat_difference))).

Lemma sm2_cubic_bezout_result_correct :
  sm2_cubic_bezout_result = 1 :: 0 :: 0 :: 0 :: 0 :: nil.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma sm2_curve_polynomial_no_root :
  forall x,
    (x * x * x + SM2_A_Z * x + SM2_B_Z) mod SM2_P_Z <> 0.
Proof.
  intros x Hroot.
  pose proof
    (cubic_pow_pos_eval_eqmod
       (Z.to_pos SM2_P_Z) cubic_x x Hroot) as Hpower.
  rewrite sm2_cubic_fermat_remainder_correct in Hpower.
  unfold cubic_eqmod in Hpower.
  rewrite cubic_x_eval in Hpower.
  rewrite (Z2Pos.id SM2_P_Z) in Hpower
    by (pose proof sm2_p_gt_one; lia).
  rewrite sm2_p_fermat in Hpower.
  assert (Hdifference :
    cubic_eqmod (cubic_eval sm2_cubic_fermat_difference x) 0).
  { unfold sm2_cubic_fermat_difference.
    rewrite cubic_sub_x_eval.
    unfold cubic_eqmod.
    rewrite Zminus_mod, Hpower, Z.sub_diag.
    rewrite Z.mod_0_l by (pose proof sm2_p_gt_one; lia).
    reflexivity. }
  assert (Hcurve :
    cubic_eqmod (polynomial_eval sm2_curve_polynomial x) 0).
  { unfold cubic_eqmod.
    rewrite sm2_curve_polynomial_eval, Hroot.
    rewrite Z.mod_0_l by (pose proof sm2_p_gt_one; lia).
    reflexivity. }
  assert (Hdifference_polynomial :
    cubic_eqmod
      (polynomial_eval
        (cubic_coefficients sm2_cubic_fermat_difference) x)
      0).
  { rewrite cubic_coefficients_eval. exact Hdifference. }
  set (raw_bezout :=
    polynomial_add
      (polynomial_mul sm2_cubic_bezout_left sm2_curve_polynomial)
      (polynomial_mul sm2_cubic_bezout_right
        (cubic_coefficients sm2_cubic_fermat_difference))).
  assert (Hraw : cubic_eqmod (polynomial_eval raw_bezout x) 0).
  { subst raw_bezout.
    rewrite polynomial_add_eval, !polynomial_mul_eval.
    eapply cubic_eqmod_trans.
    - apply cubic_eqmod_add.
      + apply cubic_eqmod_mul.
        * apply cubic_eqmod_refl.
        * exact Hcurve.
      + apply cubic_eqmod_mul.
        * apply cubic_eqmod_refl.
        * exact Hdifference_polynomial.
    - replace
        (polynomial_eval sm2_cubic_bezout_left x * 0 +
         polynomial_eval sm2_cubic_bezout_right x * 0)
        with 0 by ring.
      apply cubic_eqmod_refl. }
  pose proof (polynomial_norm_eval_eqmod raw_bezout x) as Hnorm.
  assert (Hone :
    cubic_eqmod
      (polynomial_eval (1 :: 0 :: 0 :: 0 :: 0 :: nil) x)
      0).
  { eapply cubic_eqmod_trans.
    - rewrite <- sm2_cubic_bezout_result_correct.
      unfold sm2_cubic_bezout_result.
      exact Hnorm.
    - exact Hraw. }
  assert (Hone_eval :
    polynomial_eval (1 :: 0 :: 0 :: 0 :: 0 :: nil) x = 1).
  { change
      (1 + x * (0 + x * (0 + x * (0 + x * (0 + x * 0)))) = 1).
    ring. }
  rewrite Hone_eval in Hone.
  unfold cubic_eqmod in Hone.
  rewrite Z.mod_small in Hone
    by (pose proof sm2_p_gt_one; lia).
  rewrite Z.mod_0_l in Hone
    by (pose proof sm2_p_gt_one; lia).
  discriminate.
Qed.

Lemma sm2_point_on_curve_y_nonzero :
  forall x y,
    sm2_affine_on_curve x y ->
    y <> 0.
Proof.
  intros x y Hon_curve Hy.
  subst y.
  destruct Hon_curve as [_ [_ Hcurve]].
  apply sm2_affine_equation_iff in Hcurve.
  pose proof (sm2_curve_polynomial_no_root x) as Hnonroot.
  apply Hnonroot.
  rewrite <- Hcurve.
  apply Z.mod_0_l.
  pose proof sm2_p_gt_one.
  lia.
Qed.

End Sm2NoTwoTorsionCertificate.

Lemma sm2_point_on_curve_y_nonzero :
  forall x y,
    sm2_affine_on_curve x y ->
    y <> 0.
Proof.
  exact Sm2NoTwoTorsionCertificate.sm2_point_on_curve_y_nonzero.
Qed.

Lemma afpoint_represents_noninfinity_y_nonzero :
  forall x y point,
    afpoint_represents x y point ->
    point <> ECInfinity ->
    y <> 0.
Proof.
  intros x y point Hrep Hfinite.
  destruct point as [|point_x point_y Hcurve].
  - contradiction.
  - cbn [afpoint_represents] in Hrep.
    destruct Hrep as [Hx Hy].
    subst x y.
    apply (sm2_point_on_curve_y_nonzero
      (sm2_fe_value point_x) (sm2_fe_value point_y)).
    unfold sm2_affine_on_curve.
    split; [apply sm2_fe_value_bounds |].
    split; [apply sm2_fe_value_bounds |].
    unfold sm2_affine_equation.
    repeat rewrite sm2_fe_of_Z_value.
    exact Hcurve.
Qed.

Lemma afpoint_represents_negate_noninfinity :
  forall x y point,
    afpoint_represents x y point ->
    point <> ECInfinity ->
    afpoint_represents
      x ((-y) mod SM2_P_Z) (sm2_point_negate point).
Proof.
  intros x y point Hrep Hfinite.
  destruct point as [|point_x point_y Hcurve].
  - contradiction.
  - cbn [afpoint_represents] in Hrep.
    destruct Hrep as [Hx Hy].
    subst x y.
    cbn [sm2_point_negate SMain.opp afpoint_represents].
    split; [reflexivity |].
    unfold sm2_fe_value, ZEll.pkopp, GZnZ.opp.
    cbn.
    reflexivity.
Qed.

Lemma sm2_p_minus_nonzero :
  forall y,
    0 < y < SM2_P_Z ->
    0 <= SM2_P_Z - y < SM2_P_Z /\
    SM2_P_Z - y = (-y) mod SM2_P_Z.
Proof.
  intros y Hy.
  split; [lia |].
  symmetry.
  replace (-y) with ((SM2_P_Z - y) - 1 * SM2_P_Z) by lia.
  rewrite Zminus_mod.
  rewrite Z.mod_mul by (pose proof sm2_p_gt_one; lia).
  rewrite Z.sub_0_r.
  rewrite Z.mod_mod by (pose proof sm2_p_gt_one; lia).
  apply Z.mod_small.
  lia.
Qed.


Lemma sm2_point_on_curve_coordinate_bounds :
  forall x y,
    sm2_affine_on_curve x y ->
    0 <= x < SM2_P_Z /\ 0 <= y < SM2_P_Z.
Proof.
  intros x y Hon_curve.
  exact (conj (proj1 Hon_curve) (proj1 (proj2 Hon_curve))).
Qed.

Lemma afpoint_to_jpoint_coordinates_represents :
  forall x y result_x result_y result_z point,
    afpoint_represents x y point ->
    afpoint_to_jpoint_coordinates
      x y result_x result_y result_z ->
    jpoint_represents result_x result_y result_z point.
Proof.
  intros x y result_x result_y result_z point Haffine Hconvert.
  destruct point as [|point_x point_y Hcurve].
  - cbn [afpoint_represents] in Haffine.
    destruct Haffine as [Hx Hy].
    destruct Hconvert as
      [[_ [Hresult_x [Hresult_y Hresult_z]]] |
       [[Hnonzero_x | Hnonzero_y] _]].
    + subst result_x result_y result_z.
      cbn [jpoint_represents jpoint_infinity].
      split; [split; [lia | exact sm2_p_gt_one] |].
      split; [split; [lia | exact sm2_p_gt_one] |].
      split.
      { split; [lia |].
        apply Z.lt_trans with (m := 1).
        - lia.
        - exact sm2_p_gt_one. }
      reflexivity.
    + exfalso. apply Hnonzero_x. exact Hx.
    + exfalso. apply Hnonzero_y. exact Hy.
  - cbn [afpoint_represents] in Haffine.
    destruct Haffine as [Hx Hy].
    assert (Hpoint_on_curve :
      sm2_affine_on_curve
        (sm2_fe_value point_x) (sm2_fe_value point_y)).
    { unfold sm2_affine_on_curve.
      split; [apply sm2_fe_value_bounds |].
      split; [apply sm2_fe_value_bounds |].
      unfold sm2_affine_equation.
      repeat rewrite sm2_fe_of_Z_value.
      exact Hcurve. }
    destruct Hconvert as
      [[[Hx_zero Hy_zero] _] |
       [_ [Hresult_x [Hresult_y Hresult_z]]]].
    + rewrite Hx in Hx_zero.
      rewrite Hy in Hy_zero.
      rewrite Hx_zero, Hy_zero in Hpoint_on_curve.
      exfalso.
      exact (sm2_origin_not_on_curve Hpoint_on_curve).
    + subst x y result_x result_y result_z.
      pose proof (sm2_fe_value_bounds point_x) as Hpoint_x.
      pose proof (sm2_fe_value_bounds point_y) as Hpoint_y.
      cbn [jpoint_represents].
      split; [exact Hpoint_x |].
      split; [exact Hpoint_y |].
      split.
      { split; [lia | exact sm2_p_gt_one]. }
      split; [lia |].
      split.
      { rewrite Z.mul_1_r, Z.mod_small; [reflexivity | exact Hpoint_x]. }
      { rewrite Z.mul_1_r, Z.mod_small; [reflexivity | exact Hpoint_y]. }
Qed.

Lemma afpoint_to_jpoint_coordinates_represents_canonical :
  forall x y result_x result_y result_z point,
    afpoint_represents x y point ->
    afpoint_to_jpoint_coordinates
      x y result_x result_y result_z ->
    jpoint_represents result_x result_y result_z point /\
    jpoint_canonical_infinity_encoding
      result_x result_y result_z point.
Proof.
  intros x y result_x result_y result_z point Haffine Hconvert.
  split.
  - eapply afpoint_to_jpoint_coordinates_represents; eauto.
  - unfold jpoint_canonical_infinity_encoding.
    intros Hpoint.
    subst point.
    cbn [afpoint_represents] in Haffine.
    destruct Haffine as [Hx Hy].
    unfold afpoint_to_jpoint_coordinates in Hconvert.
    destruct Hconvert as
      [[_ Hcanonical] | [[Hnonzero_x | Hnonzero_y] _]].
    + exact Hcanonical.
    + contradiction.
    + contradiction.
Qed.

(** Multiplying a residue containing [z ^ exponent] by the same power
    of an inverse of [z] cancels the projective factor. *)
Lemma mod_inverse_power_cancel :
  forall a z z_inverse exponent,
    0 <= exponent ->
    (z * z_inverse) mod SM2_P_Z = 1 ->
    ((((a * z ^ exponent) mod SM2_P_Z) *
       z_inverse ^ exponent) mod SM2_P_Z) =
    a mod SM2_P_Z.
Proof.
  intros a z z_inverse exponent Hexponent Hinverse.
  pose proof sm2_p_gt_one as Hp.
  rewrite Z.mul_mod_idemp_l by lia.
  replace ((a * z ^ exponent) * z_inverse ^ exponent) with
      (a * (z * z_inverse) ^ exponent)
      by (rewrite Z.pow_mul_l; rewrite Z.mul_assoc; reflexivity).
  rewrite <- Z.mul_mod_idemp_r by lia.
  rewrite Zpow_facts.Zpower_mod by lia.
  rewrite Hinverse.
  rewrite Z.pow_1_l by lia.
  replace (1 mod SM2_P_Z) with 1
    by (symmetry; apply Z.mod_small; lia).
  rewrite Z.mul_1_r.
  reflexivity.
Qed.

(** The exact finite-branch multiplication sequence used by
    [jacobian_to_affine] satisfies its coordinate relation. *)
Lemma jpoint_to_afpoint_coordinates_nonzero :
  forall x y z z_inverse,
    z <> 0 ->
    0 <= z_inverse < SM2_P_Z ->
    (z * z_inverse) mod SM2_P_Z = 1 ->
    jpoint_to_afpoint_coordinates
      x y z
      ((x * ((z_inverse * z_inverse) mod SM2_P_Z)) mod SM2_P_Z)
      ((y * ((((z_inverse * z_inverse) mod SM2_P_Z) *
               z_inverse) mod SM2_P_Z)) mod SM2_P_Z).
Proof.
  intros x y z z_inverse Hz Hinverse_bounds Hinverse.
  unfold jpoint_to_afpoint_coordinates.
  right.
  split; [exact Hz |].
  exists z_inverse.
  split; [exact Hinverse_bounds |].
  split; [exact Hinverse |].
  split.
  - rewrite Z.pow_2_r.
    rewrite Z.mul_mod_idemp_r by (pose proof sm2_p_gt_one; lia).
    reflexivity.
  - replace (z_inverse ^ 3) with
        ((z_inverse * z_inverse) * z_inverse) by ring.
    rewrite Z.mul_mod_idemp_r by (pose proof sm2_p_gt_one; lia).
    rewrite <- Z.mul_mod_idemp_r by (pose proof sm2_p_gt_one; lia).
    rewrite Z.mul_mod_idemp_l by (pose proof sm2_p_gt_one; lia).
    rewrite Z.mul_mod_idemp_r by (pose proof sm2_p_gt_one; lia).
    reflexivity.
Qed.

(** Normalizing a represented Jacobian point gives the canonical affine
    representation of the same abstract point. *)
Lemma jpoint_to_afpoint_coordinates_represents :
  forall x y z result_x result_y point,
    jpoint_represents x y z point ->
    jpoint_to_afpoint_coordinates x y z result_x result_y ->
    afpoint_represents result_x result_y point.
Proof.
  intros x y z result_x result_y point Hjacobian Hconvert.
  destruct point as [|point_x point_y Hcurve].
  - cbn [jpoint_represents] in Hjacobian.
    destruct Hjacobian as [_ [_ [_ Hz]]].
    destruct Hconvert as [[_ Hinfinity] | [Hz_nonzero _]].
    + cbn [afpoint_represents].
      exact Hinfinity.
    + unfold jpoint_infinity in Hz.
      contradiction.
  - cbn [jpoint_represents] in Hjacobian.
    destruct Hjacobian as
      [_ [_ [_ [Hz_nonzero [Hx Hy]]]]].
    pose proof (sm2_fe_value_bounds point_x) as Hpoint_x.
    pose proof (sm2_fe_value_bounds point_y) as Hpoint_y.
    destruct Hconvert as
      [[Hcanonical _] |
       [_ [z_inverse [_ [Hinverse [Hresult_x Hresult_y]]]]]].
    + unfold canonical_jpoint_infinity in Hcanonical.
      destruct Hcanonical as [_ [_ Hz]].
      contradiction.
    + cbn [afpoint_represents].
      split.
      { rewrite Hresult_x, Hx.
        rewrite
          (mod_inverse_power_cancel
             (sm2_fe_value point_x) z z_inverse 2)
          by (try lia; exact Hinverse).
        apply Z.mod_small.
        exact Hpoint_x. }
      { rewrite Hresult_y, Hy.
        rewrite
          (mod_inverse_power_cancel
             (sm2_fe_value point_y) z z_inverse 3)
          by (try lia; exact Hinverse).
        apply Z.mod_small.
        exact Hpoint_y. }
Qed.

(** * Mixed Jacobian-affine addition *)

(** Fix the standard equality-modulo relation and its ring morphisms to the
    SM2 field modulus.  This lets the algebraic lemmas below use
    [setoid_rewrite] without introducing a separate coordinate predicate. *)
Local Instance sm2_eqm_equivalence :
  Equivalence (eqm SM2_P_Z) := eqm_setoid SM2_P_Z.

Local Instance sm2_add_eqm_proper :
  Proper (eqm SM2_P_Z ==> eqm SM2_P_Z ==> eqm SM2_P_Z) Z.add :=
  Zplus_eqm SM2_P_Z.

Local Instance sm2_sub_eqm_proper :
  Proper (eqm SM2_P_Z ==> eqm SM2_P_Z ==> eqm SM2_P_Z) Z.sub :=
  Zminus_eqm SM2_P_Z.

Local Instance sm2_mul_eqm_proper :
  Proper (eqm SM2_P_Z ==> eqm SM2_P_Z ==> eqm SM2_P_Z) Z.mul :=
  Zmult_eqm SM2_P_Z.

Lemma sm2_eqm_iff_sub_mod_zero :
  forall a b,
    eqm SM2_P_Z a b <->
    (a - b) mod SM2_P_Z = 0.
Proof.
  intros a b.
  unfold eqm.
  split.
  - intros Hab.
    rewrite Zminus_mod, Hab, Z.sub_diag.
    apply Z.mod_0_l.
    pose proof sm2_p_gt_one.
    lia.
  - intros Hsub.
    rewrite Zminus_mod in Hsub.
    apply Z.mod_divide in Hsub.
    2: { pose proof sm2_p_gt_one. lia. }
    destruct Hsub as [k Hk].
    assert (Hp : 0 < SM2_P_Z) by (pose proof sm2_p_gt_one; lia).
    pose proof (Z.mod_pos_bound a SM2_P_Z Hp) as Ha.
    pose proof (Z.mod_pos_bound b SM2_P_Z Hp) as Hb.
    assert (k = 0) by nia.
    nia.
Qed.

Lemma sm2_eqm_mul_cancel_l :
  forall a b c,
    0 <= a < SM2_P_Z ->
    a <> 0 ->
    eqm SM2_P_Z (a * b) (a * c) ->
    eqm SM2_P_Z b c.
Proof.
  intros a b c Ha Ha0 Hmul.
  unfold eqm in *.
  assert (Hzero : (a * (b - c)) mod SM2_P_Z = 0).
  {
    rewrite Z.mul_sub_distr_l.
    rewrite Zminus_mod.
    rewrite Hmul.
    rewrite Z.sub_diag.
    apply Z.mod_0_l.
    pose proof sm2_p_gt_one.
    lia.
  }
  apply Z.mod_divide in Hzero.
  2: { pose proof sm2_p_gt_one. lia. }
  assert (Hrel : rel_prime SM2_P_Z a).
  {
    apply rel_prime_sym.
    apply (proj1 (Zgcd_1_rel_prime a SM2_P_Z)).
    apply sm2_p_nonzero_gcd_one; assumption.
  }
  pose proof (Gauss SM2_P_Z a (b - c) Hzero Hrel) as Hdiv.
  apply Z.mod_divide in Hdiv.
  2: { pose proof sm2_p_gt_one. lia. }
  rewrite Zminus_mod in Hdiv.
  apply Z.mod_divide in Hdiv.
  2: { pose proof sm2_p_gt_one. lia. }
  destruct Hdiv as [k Hk].
  assert (Hp : 0 < SM2_P_Z) by (pose proof sm2_p_gt_one; lia).
  pose proof (Z.mod_pos_bound b SM2_P_Z Hp) as Hb.
  pose proof (Z.mod_pos_bound c SM2_P_Z Hp) as Hc.
  assert (k = 0) by nia.
  nia.
Qed.

Lemma sm2_difference_mod_nonzero :
  forall x1 x2,
    0 <= x1 < SM2_P_Z ->
    0 <= x2 < SM2_P_Z ->
    x1 <> x2 ->
    (x2 - x1) mod SM2_P_Z <> 0.
Proof.
  intros x1 x2 Hx1 Hx2 Hneq Hzero.
  apply Z.mod_divide in Hzero.
  2: { pose proof sm2_p_gt_one. lia. }
  destruct Hzero as [k Hk].
  assert (k = 0) by nia.
  lia.
Qed.

Lemma sm2_eqm_mul_cancel :
  forall a b c,
    a mod SM2_P_Z <> 0 ->
    eqm SM2_P_Z (a * b) (a * c) ->
    eqm SM2_P_Z b c.
Proof.
  intros a b c Ha Hmul.
  apply (sm2_eqm_mul_cancel_l (a mod SM2_P_Z)).
  - apply Z.mod_pos_bound.
    pose proof sm2_p_gt_one.
    lia.
  - exact Ha.
  - unfold eqm in *.
    rewrite !Z.mul_mod_idemp_l.
    exact Hmul.
    all: pose proof sm2_p_gt_one; lia.
Qed.

(** The secant formulas preserve the curve equation.  The only field
    cancellation is by the nonzero difference of the two x coordinates. *)
Lemma sm2_affine_secant_equation :
  forall coefficient_a coefficient_b x1 y1 x2 y2 slope x3 y3,
    eqm SM2_P_Z
      (y1 * y1)
      (x1 * x1 * x1 + coefficient_a * x1 + coefficient_b) ->
    eqm SM2_P_Z
      (y2 * y2)
      (x2 * x2 * x2 + coefficient_a * x2 + coefficient_b) ->
    (x2 - x1) mod SM2_P_Z <> 0 ->
    eqm SM2_P_Z ((x2 - x1) * slope) (y2 - y1) ->
    eqm SM2_P_Z x3 (slope * slope - x1 - x2) ->
    eqm SM2_P_Z y3 (slope * (x1 - x3) - y1) ->
    eqm SM2_P_Z
      (y3 * y3)
      (x3 * x3 * x3 + coefficient_a * x3 + coefficient_b).
Proof.
  intros coefficient_a coefficient_b
    x1 y1 x2 y2 slope x3 y3
    Hcurve1 Hcurve2 Hdx Hslope Hx3 Hy3.
  assert (Hfactor :
    eqm SM2_P_Z
      ((y2 - y1) * (y2 + y1))
      ((x2 - x1) *
       (x2 * x2 + x1 * x2 + x1 * x1 + coefficient_a))).
  {
    eapply
      (eqm_trans SM2_P_Z _
        (y2 * y2 - y1 * y1) _).
    - unfold eqm. f_equal. ring.
    - setoid_rewrite Hcurve1.
      setoid_rewrite Hcurve2.
      unfold eqm. f_equal. ring.
  }
  assert (Hslope_sum :
    eqm SM2_P_Z
      (slope * (y2 + y1))
      (x2 * x2 + x1 * x2 + x1 * x1 + coefficient_a)).
  {
    apply (sm2_eqm_mul_cancel (x2 - x1)).
    - exact Hdx.
    - eapply
        (eqm_trans SM2_P_Z _
          (((x2 - x1) * slope) * (y2 + y1)) _).
      + unfold eqm. f_equal. ring.
      + setoid_rewrite Hslope.
        exact Hfactor.
  }
  assert (Htwo :
    eqm SM2_P_Z
      (2 * slope * y1)
      ((x2 * x2 + x1 * x2 + x1 * x1 + coefficient_a) -
       (x2 - x1) * slope * slope)).
  {
    eapply
      (eqm_trans SM2_P_Z _
        (slope * (y2 + y1) - slope * (y2 - y1)) _).
    - unfold eqm. f_equal. ring.
    - setoid_rewrite Hslope_sum.
      setoid_rewrite <- Hslope.
      unfold eqm. f_equal. ring.
  }
  assert (Hfactor3 :
    eqm SM2_P_Z
      (2 * slope * y1 + slope * slope * (x3 - x1))
      (x3 * x3 + x3 * x1 + x1 * x1 + coefficient_a)).
  {
    setoid_rewrite Htwo.
    setoid_rewrite Hx3.
    unfold eqm. f_equal. ring.
  }
  eapply
    (eqm_trans SM2_P_Z _
      ((y3 * y3 - y1 * y1) + y1 * y1) _).
  - unfold eqm. f_equal. ring.
  - setoid_rewrite Hy3.
    eapply
      (eqm_trans SM2_P_Z _
        (((x3 - x1) *
          (2 * slope * y1 + slope * slope * (x3 - x1))) +
         y1 * y1) _).
    + unfold eqm. f_equal. ring.
    + setoid_rewrite Hfactor3.
      setoid_rewrite Hcurve1.
      unfold eqm. f_equal. ring.
Qed.

(** Integer-coordinate side conditions for the secant branch of SM2 point
    addition.  These predicates deliberately stay independent of
    [SMain.add]; they are the form produced by symbolic execution. *)
Definition sm2_affine_slope
    (numerator denominator slope : Z) : Prop :=
  0 <= slope < SM2_P_Z /\
  (denominator * slope - numerator) mod SM2_P_Z = 0.

Definition sm2_affine_sum
    (x1 y1 x2 slope x3 y3 : Z) : Prop :=
  x3 = (slope * slope - x1 - x2) mod SM2_P_Z /\
  y3 = (slope * (x1 - x3) - y1) mod SM2_P_Z.

Lemma sm2_affine_sum_on_curve_distinct_x :
  forall x1 y1 x2 y2 slope x3 y3,
    sm2_affine_on_curve x1 y1 ->
    sm2_affine_on_curve x2 y2 ->
    x1 <> x2 ->
    sm2_affine_slope (y2 - y1) (x2 - x1) slope ->
    sm2_affine_sum x1 y1 x2 slope x3 y3 ->
    sm2_affine_on_curve x3 y3.
Proof.
  intros x1 y1 x2 y2 slope x3 y3
    Hcurve1 Hcurve2 Hxneq Hslope Hsum.
  unfold sm2_affine_on_curve in Hcurve1, Hcurve2 |- *.
  unfold sm2_affine_slope in Hslope.
  unfold sm2_affine_sum in Hsum.
  destruct Hcurve1 as [Hx1 [Hy1 Hcurve1]].
  destruct Hcurve2 as [Hx2 [Hy2 Hcurve2]].
  apply sm2_affine_equation_iff in Hcurve1.
  apply sm2_affine_equation_iff in Hcurve2.
  destruct Hslope as [Hslope_bounds Hslope].
  destruct Hsum as [Hx3 Hy3].
  split.
  - rewrite Hx3.
    apply Z.mod_pos_bound.
    pose proof sm2_p_gt_one.
    lia.
  - split.
    + rewrite Hy3.
      apply Z.mod_pos_bound.
      pose proof sm2_p_gt_one.
      lia.
    + apply sm2_affine_equation_iff.
      apply
        (sm2_affine_secant_equation
           SM2_A_Z SM2_B_Z x1 y1 x2 y2 slope x3 y3).
      * exact Hcurve1.
      * exact Hcurve2.
      * apply sm2_difference_mod_nonzero; assumption.
      * apply (proj2 (sm2_eqm_iff_sub_mod_zero _ _)).
        exact Hslope.
      * rewrite Hx3.
        apply Zmod_eqm.
      * rewrite Hy3.
        apply Zmod_eqm.
Qed.

Lemma sm2_mod_inverse_exists :
  forall a,
    a mod SM2_P_Z <> 0 ->
    exists inverse,
      0 <= inverse < SM2_P_Z /\
      (a * inverse) mod SM2_P_Z = 1.
Proof.
  intros a Ha.
  set (r := a mod SM2_P_Z).
  assert (Hr_bounds : 0 <= r < SM2_P_Z).
  {
    unfold r.
    apply Z.mod_pos_bound.
    pose proof sm2_p_gt_one.
    lia.
  }
  assert (Hr_nonzero : r <> 0).
  { unfold r. exact Ha. }
  assert (Hrel : rel_prime r SM2_P_Z).
  {
    apply (proj1 (Zgcd_1_rel_prime _ _)).
    apply sm2_p_nonzero_gcd_one; assumption.
  }
  destruct (rel_prime_bezout r SM2_P_Z Hrel)
    as [u v Hbezout].
  exists (u mod SM2_P_Z).
  split.
  - apply Z.mod_pos_bound.
    pose proof sm2_p_gt_one.
    lia.
  - rewrite Z.mul_mod by (pose proof sm2_p_gt_one; lia).
    fold r.
    rewrite Z.mod_mod by (pose proof sm2_p_gt_one; lia).
    rewrite (Z.mul_mod_idemp_r r u SM2_P_Z)
      by (pose proof sm2_p_gt_one; lia).
    rewrite Z.mul_comm.
    replace (u * r) with (1 + (-v) * SM2_P_Z) by nia.
    rewrite Z.mod_add by (pose proof sm2_p_gt_one; lia).
    apply Z.mod_small.
    pose proof sm2_p_gt_one.
    lia.
Qed.

(** Algebraic correctness of the exact temporary-variable schedule used by
    [add_JPoint_and_AFPoint]. *)
Lemma sm2_mixed_add_formula_eqm :
  forall x1 y1 x2 y2 z slope x3 y3
         jx jy z2 a b c2 c3 x1c2 d2 x1c22 rx tmp ry rz,
    eqm SM2_P_Z jx (x1 * z * z) ->
    eqm SM2_P_Z jy (y1 * z * z * z) ->
    eqm SM2_P_Z z2 (z * z) ->
    eqm SM2_P_Z a (x2 * z2 - jx) ->
    eqm SM2_P_Z b (y2 * z2 * z - jy) ->
    eqm SM2_P_Z c2 (a * a) ->
    eqm SM2_P_Z c3 (c2 * a) ->
    eqm SM2_P_Z x1c2 (jx * c2) ->
    eqm SM2_P_Z d2 (b * b) ->
    eqm SM2_P_Z x1c22 (x1c2 + x1c2) ->
    eqm SM2_P_Z rx (d2 - x1c22 - c3) ->
    eqm SM2_P_Z tmp (x1c2 - rx) ->
    eqm SM2_P_Z ry (b * tmp - jy * c3) ->
    eqm SM2_P_Z rz (z * a) ->
    eqm SM2_P_Z ((x2 - x1) * slope) (y2 - y1) ->
    eqm SM2_P_Z x3 (slope * slope - x1 - x2) ->
    eqm SM2_P_Z y3 (slope * (x1 - x3) - y1) ->
    eqm SM2_P_Z rx (x3 * rz * rz) /\
    eqm SM2_P_Z ry (y3 * rz * rz * rz).
Proof.
  intros x1 y1 x2 y2 z slope x3 y3
    jx jy z2 a b c2 c3 x1c2 d2 x1c22 rx tmp ry rz
    Hjx Hjy Hz2 Ha Hb Hc2 Hc3 Hx1c2 Hd2 Hx1c22
    Hrx Htmp Hry Hrz Hslope Hx3 Hy3.
  assert (Ha_direct :
    eqm SM2_P_Z a ((x2 - x1) * z * z)).
  {
    setoid_rewrite Ha.
    setoid_rewrite Hz2.
    setoid_rewrite Hjx.
    unfold eqm. f_equal. ring.
  }
  assert (Hb_direct :
    eqm SM2_P_Z b ((y2 - y1) * z * z * z)).
  {
    setoid_rewrite Hb.
    setoid_rewrite Hz2.
    setoid_rewrite Hjy.
    unfold eqm. f_equal. ring.
  }
  assert (Hb_slope :
    eqm SM2_P_Z b (slope * a * z)).
  {
    setoid_rewrite Hb_direct.
    setoid_rewrite <- Hslope.
    setoid_rewrite Ha_direct.
    unfold eqm. f_equal. ring.
  }
  assert (Hrx_result :
    eqm SM2_P_Z rx (x3 * rz * rz)).
  {
    setoid_rewrite Hrx.
    setoid_rewrite Hd2.
    setoid_rewrite Hb_direct.
    setoid_rewrite Hx1c22.
    setoid_rewrite Hx1c2.
    setoid_rewrite Hjx.
    setoid_rewrite Hc2.
    setoid_rewrite Hc3.
    setoid_rewrite Ha_direct.
    setoid_rewrite <- Hslope.
    setoid_rewrite Hx3.
    setoid_rewrite Hrz.
    setoid_rewrite Hc2.
    setoid_rewrite Ha_direct.
    unfold eqm. f_equal. ring.
  }
  split.
  - exact Hrx_result.
  - setoid_rewrite Hry.
    setoid_rewrite Hb_slope.
    setoid_rewrite Htmp.
    setoid_rewrite Hx1c2.
    setoid_rewrite Hjx.
    setoid_rewrite Hc2.
    setoid_rewrite Hrx_result.
    setoid_rewrite Hjy.
    setoid_rewrite Hc3.
    setoid_rewrite Hc2.
    setoid_rewrite Ha_direct.
    setoid_rewrite Hy3.
    setoid_rewrite Hrz.
    setoid_rewrite Ha_direct.
    unfold eqm. f_equal. ring.
Qed.

Lemma sm2_eqm_canonical_left :
  forall canonical value,
    0 <= canonical < SM2_P_Z ->
    eqm SM2_P_Z canonical value ->
    canonical = value mod SM2_P_Z.
Proof.
  intros canonical value Hcanonical Heqm.
  unfold eqm in Heqm.
  rewrite Z.mod_small in Heqm by exact Hcanonical.
  exact Heqm.
Qed.

Lemma sm2_eqm_product_nonzero :
  forall a b,
    a mod SM2_P_Z <> 0 ->
    b mod SM2_P_Z <> 0 ->
    (a * b) mod SM2_P_Z <> 0.
Proof.
  intros a b Ha Hb Hab.
  assert (Hzero : eqm SM2_P_Z (a * b) (a * 0)).
  {
    unfold eqm.
    rewrite Z.mul_0_r.
    rewrite Z.mod_0_l by (pose proof sm2_p_gt_one; lia).
    exact Hab.
  }
  pose proof (sm2_eqm_mul_cancel a b 0 Ha Hzero) as Hcancel.
  unfold eqm in Hcancel.
  rewrite Z.mod_0_l in Hcancel by (pose proof sm2_p_gt_one; lia).
  contradiction.
Qed.

(** Coqprime's generic secant branch agrees with the canonical integer
    affine formula.  This is one of the few refinement lemmas that unfolds
    [SMain.add]. *)
Lemma sm2_point_add_affine_distinct :
  forall x1 y1 x2 y2 slope x3 y3
         (Hcurve1 : sm2_affine_on_curve x1 y1)
         (Hcurve2 : sm2_affine_on_curve x2 y2)
         (Hcurve3 : sm2_affine_on_curve x3 y3),
    x1 <> x2 ->
    sm2_affine_slope (y2 - y1) (x2 - x1) slope ->
    sm2_affine_sum x1 y1 x2 slope x3 y3 ->
    sm2_point_add
      (ec_point_of_affine x1 y1 Hcurve1)
      (ec_point_of_affine x2 y2 Hcurve2) =
    ec_point_of_affine x3 y3 Hcurve3.
Proof.
  intros x1 y1 x2 y2 slope x3 y3
    Hcurve1 Hcurve2 Hcurve3 Hxneq Hslope Hsum.
  assert (Hdx : (x2 - x1) mod SM2_P_Z <> 0).
  {
    apply sm2_difference_mod_nonzero.
    - exact (proj1 Hcurve1).
    - exact (proj1 Hcurve2).
    - exact Hxneq.
  }
  assert (Hx_fe : sm2_fe_of_Z x1 <> sm2_fe_of_Z x2).
  {
    intros Hequal.
    apply Hxneq.
    rewrite <- (sm2_fe_value_of_Z x1 (proj1 Hcurve1)).
    rewrite <- (sm2_fe_value_of_Z x2 (proj1 Hcurve2)).
    now rewrite Hequal.
  }
  unfold sm2_affine_slope in Hslope.
  destruct Hslope as [_ Hslope].
  unfold sm2_affine_sum in Hsum.
  destruct Hsum as [Hx3 Hy3].
  assert (Hslope_fe :
    sm2_fe_of_Z slope =
    ZEll.pkdiv
      (ZEll.pksub (sm2_fe_of_Z y2) (sm2_fe_of_Z y1))
      (ZEll.pksub (sm2_fe_of_Z x2) (sm2_fe_of_Z x1))).
  {
    rewrite <- !sm2_fe_of_Z_sub.
    apply sm2_fe_of_Z_div_solution.
    - exact Hdx.
    - apply (proj2 (sm2_eqm_iff_sub_mod_zero _ _)).
      exact Hslope.
  }
  unfold sm2_point_add, ec_point_of_affine, SMain.add.
  destruct
    (SMain.Kdec sm2_curve_theory
      (sm2_fe_of_Z x1) (sm2_fe_of_Z x2))
    as [Hequal | Hunequal].
  - contradiction.
  - apply (SMain.curve_elt_irr sm2_curve_theory).
    + rewrite <- Hslope_fe.
      cbn [SMain.pow].
      rewrite <- sm2_fe_of_Z_mul.
      rewrite <- !sm2_fe_of_Z_sub.
      apply (proj2 (sm2_fe_of_Z_eq_iff _ _)).
      rewrite Hx3.
      rewrite Z.mod_mod by (pose proof sm2_p_gt_one; lia).
      reflexivity.
    + assert (Hcomputed_x :
        ZEll.pksub
          (ZEll.pksub
            (SMain.pow
              (ZEll.pkI SM2_P_Z) (@ZEll.pkmul SM2_P_Z)
              (ZEll.pkdiv
                (ZEll.pksub (sm2_fe_of_Z y2) (sm2_fe_of_Z y1))
                (ZEll.pksub (sm2_fe_of_Z x2) (sm2_fe_of_Z x1))) 2)
            (sm2_fe_of_Z x1))
          (sm2_fe_of_Z x2) = sm2_fe_of_Z x3).
      {
        rewrite <- Hslope_fe.
        cbn [SMain.pow].
        rewrite <- sm2_fe_of_Z_mul.
        rewrite <- !sm2_fe_of_Z_sub.
        apply (proj2 (sm2_fe_of_Z_eq_iff _ _)).
        rewrite Hx3.
        rewrite Z.mod_mod by (pose proof sm2_p_gt_one; lia).
        reflexivity.
      }
      rewrite Hcomputed_x.
      rewrite <- Hslope_fe.
      rewrite <- sm2_fe_of_Z_opp.
      rewrite <- sm2_fe_of_Z_sub.
      rewrite <- sm2_fe_of_Z_mul.
      rewrite <- sm2_fe_of_Z_sub.
      apply (proj2 (sm2_fe_of_Z_eq_iff _ _)).
      rewrite Hy3.
      rewrite Z.mod_mod by (pose proof sm2_p_gt_one; lia).
      f_equal.
      ring.
Qed.

(** Two distinct affine curve points with the same x coordinate are
    opposites, so Coqprime addition returns infinity. *)
Lemma sm2_point_add_affine_same_x_distinct :
  forall x1 y1 x2 y2
         (Hcurve1 : sm2_affine_on_curve x1 y1)
         (Hcurve2 : sm2_affine_on_curve x2 y2),
    x1 = x2 ->
    ec_point_of_affine x1 y1 Hcurve1 <>
      ec_point_of_affine x2 y2 Hcurve2 ->
    sm2_point_add
      (ec_point_of_affine x1 y1 Hcurve1)
      (ec_point_of_affine x2 y2 Hcurve2) = ECInfinity.
Proof.
  intros x1 y1 x2 y2 Hcurve1 Hcurve2 Hxeq Hneq.
  assert (Hx_fe : sm2_fe_of_Z x1 = sm2_fe_of_Z x2).
  { now rewrite Hxeq. }
  destruct
    (SMain.curve_elt_opp sm2_curve_theory
      (sm2_fe_of_Z y1) (sm2_fe_of_Z y2)
      (proj2 (proj2 Hcurve1)) (proj2 (proj2 Hcurve2)) Hx_fe)
    as [Hequal | Hopposite].
  - exfalso.
    apply Hneq.
    exact Hequal.
  - change
      (ec_point_of_affine x1 y1 Hcurve1 =
       sm2_point_negate (ec_point_of_affine x2 y2 Hcurve2))
      in Hopposite.
    rewrite Hopposite.
    rewrite sm2_point_add_commutative.
    apply sm2_point_add_negate_right.
Qed.

(** The mixed Jacobian-affine addition formula represents the abstract SM2
    sum for two finite, distinct inputs.  When the x coordinates coincide,
    distinctness and the curve equation force the inverse-point branch and
    the formula's zero z coordinate represents infinity. *)
Lemma jpoint_add_afpoint_mixed_represents :
  forall P1 P2
         jx jy jz x2 y2 z2 a b c2 c3 x1c2 d2 x1c22
         rx tmp ry rz,
    P1 <> ECInfinity ->
    P2 <> ECInfinity ->
    P1 <> P2 ->
    jpoint_represents jx jy jz P1 ->
    afpoint_represents x2 y2 P2 ->
    0 <= a < SM2_P_Z ->
    0 <= rx < SM2_P_Z ->
    0 <= ry < SM2_P_Z ->
    0 <= rz < SM2_P_Z ->
    eqm SM2_P_Z z2 (jz * jz) ->
    eqm SM2_P_Z a (x2 * z2 - jx) ->
    eqm SM2_P_Z b (y2 * z2 * jz - jy) ->
    eqm SM2_P_Z c2 (a * a) ->
    eqm SM2_P_Z c3 (c2 * a) ->
    eqm SM2_P_Z x1c2 (jx * c2) ->
    eqm SM2_P_Z d2 (b * b) ->
    eqm SM2_P_Z x1c22 (x1c2 + x1c2) ->
    eqm SM2_P_Z rx (d2 - x1c22 - c3) ->
    eqm SM2_P_Z tmp (x1c2 - rx) ->
    eqm SM2_P_Z ry (b * tmp - jy * c3) ->
    eqm SM2_P_Z rz (jz * a) ->
    jpoint_represents rx ry rz (sm2_point_add P1 P2).
Proof.
  intros P1 P2
    jx jy jz x2 y2 z2 a b c2 c3 x1c2 d2 x1c22
    rx tmp ry rz
    HP1finite HP2finite HPneq HJ HA
    Ha_bounds Hrx_bounds Hry_bounds Hrz_bounds
    Hz2 Ha Hb Hc2 Hc3 Hx1c2 Hd2 Hx1c22
    Hrx Htmp Hry Hrz.
  destruct P1 as [|point_x1_fe point_y1_fe Hcurve1_fe].
  { contradiction. }
  destruct P2 as [|point_x2_fe point_y2_fe Hcurve2_fe].
  { contradiction. }
  cbn [jpoint_represents] in HJ.
  cbn [afpoint_represents] in HA.
  destruct HJ as
    [Hjx_bounds [Hjy_bounds [Hjz_bounds
      [Hjz_nonzero [Hjx_coord Hjy_coord]]]]].
  set (point_x1 := sm2_fe_value point_x1_fe).
  set (point_y1 := sm2_fe_value point_y1_fe).
  destruct HA as [Hx2 Hy2].
  subst x2 y2.
  remember (sm2_fe_value point_x2_fe) as point_x2 eqn:Hpoint_x2.
  set (point_y2 := sm2_fe_value point_y2_fe).
  fold point_x1 point_y1 in Hjx_coord, Hjy_coord.
  fold point_y2 in Hb.
  assert (Hcurve1 : sm2_affine_on_curve point_x1 point_y1).
  {
    unfold sm2_affine_on_curve.
    split; [unfold point_x1; apply sm2_fe_value_bounds |].
    split; [unfold point_y1; apply sm2_fe_value_bounds |].
    unfold sm2_affine_equation, point_x1, point_y1.
    repeat rewrite sm2_fe_of_Z_value.
    exact Hcurve1_fe.
  }
  assert (Hcurve2 : sm2_affine_on_curve point_x2 point_y2).
  {
    unfold sm2_affine_on_curve.
    split; [rewrite Hpoint_x2; apply sm2_fe_value_bounds |].
    split; [unfold point_y2; apply sm2_fe_value_bounds |].
    unfold sm2_affine_equation, point_y2.
    rewrite Hpoint_x2.
    repeat rewrite sm2_fe_of_Z_value.
    exact Hcurve2_fe.
  }
  assert (HP1_affine :
    @SMain.curve_elt
      (ZEll.pK SM2_P_Z)
      (ZEll.pkI SM2_P_Z) (@ZEll.pkplus SM2_P_Z)
      (@ZEll.pkmul SM2_P_Z)
      (ZEll.pA SM2_A_Z SM2_P_Z) (ZEll.pB SM2_B_Z SM2_P_Z)
      point_x1_fe point_y1_fe Hcurve1_fe =
    ec_point_of_affine point_x1 point_y1 Hcurve1).
  {
    unfold ec_point_of_affine.
    apply (SMain.curve_elt_irr sm2_curve_theory).
    - symmetry. unfold point_x1. apply sm2_fe_of_Z_value.
    - symmetry. unfold point_y1. apply sm2_fe_of_Z_value.
  }
  assert (HP2_affine :
    @SMain.curve_elt
      (ZEll.pK SM2_P_Z)
      (ZEll.pkI SM2_P_Z) (@ZEll.pkplus SM2_P_Z)
      (@ZEll.pkmul SM2_P_Z)
      (ZEll.pA SM2_A_Z SM2_P_Z) (ZEll.pB SM2_B_Z SM2_P_Z)
      point_x2_fe point_y2_fe Hcurve2_fe =
    ec_point_of_affine point_x2 point_y2 Hcurve2).
  {
    unfold ec_point_of_affine.
    apply (SMain.curve_elt_irr sm2_curve_theory).
    - rewrite Hpoint_x2. symmetry. apply sm2_fe_of_Z_value.
    - symmetry. unfold point_y2. apply sm2_fe_of_Z_value.
  }
  rewrite HP1_affine, HP2_affine in HPneq |- *.
  assert (Hjx_m :
    eqm SM2_P_Z jx (point_x1 * jz * jz)).
  {
    rewrite Hjx_coord.
    unfold eqm.
    rewrite Z.mod_mod by (pose proof sm2_p_gt_one; lia).
    f_equal.
    ring.
  }
  assert (Hjy_m :
    eqm SM2_P_Z jy (point_y1 * jz * jz * jz)).
  {
    rewrite Hjy_coord.
    unfold eqm.
    rewrite Z.mod_mod by (pose proof sm2_p_gt_one; lia).
    f_equal.
    ring.
  }
  assert (Ha_direct :
    eqm SM2_P_Z a ((point_x2 - point_x1) * jz * jz)).
  {
    setoid_rewrite Ha.
    setoid_rewrite Hz2.
    setoid_rewrite Hjx_m.
    unfold eqm. f_equal. ring.
  }
  assert (Hjz_mod_nonzero : jz mod SM2_P_Z <> 0).
  {
    rewrite Z.mod_small by exact Hjz_bounds.
    exact Hjz_nonzero.
  }
  destruct (Z.eq_dec a 0) as [Ha_zero | Ha_nonzero].
  - assert (Htotal :
      eqm SM2_P_Z
        (jz * (jz * (point_x2 - point_x1)))
        (jz * 0)).
    {
      subst a.
      eapply
        (eqm_trans SM2_P_Z _
          ((point_x2 - point_x1) * jz * jz) _).
      + unfold eqm. f_equal. ring.
      + setoid_rewrite <- Ha_direct.
        unfold eqm.
        rewrite Z.mul_0_r.
        apply Z.mod_0_l.
        pose proof sm2_p_gt_one.
        lia.
    }
    pose proof
      (sm2_eqm_mul_cancel
        jz (jz * (point_x2 - point_x1)) 0
        Hjz_mod_nonzero Htotal) as Hcancel1.
    assert (Hcancel1' :
      eqm SM2_P_Z
        (jz * (point_x2 - point_x1))
        (jz * 0)).
    {
      setoid_rewrite Hcancel1.
      unfold eqm.
      rewrite !Z.mul_0_r.
      reflexivity.
    }
    pose proof
      (sm2_eqm_mul_cancel
        jz (point_x2 - point_x1) 0
        Hjz_mod_nonzero Hcancel1') as Hdx_zero.
    assert (Hxeq : point_x1 = point_x2).
    {
      destruct (Z.eq_dec point_x1 point_x2) as [Heq | Hne].
      { exact Heq. }
      exfalso.
      apply
        (sm2_difference_mod_nonzero
          point_x1 point_x2).
      - exact
          (proj1
            (sm2_point_on_curve_coordinate_bounds
              point_x1 point_y1 Hcurve1)).
      - exact
          (proj1
            (sm2_point_on_curve_coordinate_bounds
              point_x2 point_y2 Hcurve2)).
      - exact Hne.
      - unfold eqm in Hdx_zero.
        rewrite Z.mod_0_l in Hdx_zero
          by (pose proof sm2_p_gt_one; lia).
        exact Hdx_zero.
    }
    assert (Hrz_zero : rz = 0).
    {
      apply (sm2_eqm_canonical_left rz 0 Hrz_bounds).
      subst a.
      setoid_rewrite Hrz.
      unfold eqm.
      rewrite Z.mul_0_r.
      reflexivity.
    }
    rewrite
      (sm2_point_add_affine_same_x_distinct
        point_x1 point_y1 point_x2 point_y2
        Hcurve1 Hcurve2 Hxeq HPneq).
    cbn [jpoint_represents jpoint_infinity].
    repeat split; try assumption.
    all: try lia; try exact Hrz_zero.
  - assert (Ha_mod_nonzero : a mod SM2_P_Z <> 0).
    {
      rewrite Z.mod_small by exact Ha_bounds.
      exact Ha_nonzero.
    }
    assert (Hxneq : point_x1 <> point_x2).
    {
      intros Heq.
      subst point_x2.
      apply Ha_nonzero.
      apply (sm2_eqm_canonical_left a 0 Ha_bounds).
      setoid_rewrite Ha_direct.
      unfold eqm.
      rewrite <- Heq.
      rewrite Z.sub_diag, Z.mul_0_l.
      reflexivity.
    }
    assert (Hdx_mod_nonzero :
      (point_x2 - point_x1) mod SM2_P_Z <> 0).
    {
      apply sm2_difference_mod_nonzero.
      - exact
          (proj1
            (sm2_point_on_curve_coordinate_bounds
              point_x1 point_y1 Hcurve1)).
      - exact
          (proj1
            (sm2_point_on_curve_coordinate_bounds
              point_x2 point_y2 Hcurve2)).
      - exact Hxneq.
    }
    destruct
      (sm2_mod_inverse_exists
        (point_x2 - point_x1) Hdx_mod_nonzero)
      as [inverse [Hinverse_bounds Hinverse]].
    set (slope :=
      ((point_y2 - point_y1) * inverse) mod SM2_P_Z).
    assert (Hslope_m :
      eqm SM2_P_Z
        ((point_x2 - point_x1) * slope)
        (point_y2 - point_y1)).
    {
      unfold slope.
      setoid_rewrite Zmod_eqm.
      assert (Hinverse_m :
        eqm SM2_P_Z
          ((point_x2 - point_x1) * inverse) 1).
      {
        unfold eqm.
        rewrite Hinverse.
        rewrite Z.mod_small
          by (pose proof sm2_p_gt_one; lia).
        reflexivity.
      }
      eapply
        (eqm_trans SM2_P_Z _
          ((point_y2 - point_y1) *
           ((point_x2 - point_x1) * inverse)) _).
      - unfold eqm. f_equal. ring.
      - setoid_rewrite Hinverse_m.
        unfold eqm. f_equal. ring.
    }
    assert (Hslope :
      sm2_affine_slope
        (point_y2 - point_y1)
        (point_x2 - point_x1) slope).
    {
      unfold sm2_affine_slope.
      split.
      - unfold slope.
        apply Z.mod_pos_bound.
        pose proof sm2_p_gt_one.
        lia.
      - apply (proj1 (sm2_eqm_iff_sub_mod_zero _ _)).
        exact Hslope_m.
    }
    set (result_x :=
      (slope * slope - point_x1 - point_x2) mod SM2_P_Z).
    set (result_y :=
      (slope * (point_x1 - result_x) - point_y1) mod SM2_P_Z).
    assert (Hsum :
      sm2_affine_sum
        point_x1 point_y1 point_x2 slope result_x result_y).
    {
      unfold sm2_affine_sum.
      change
        (result_x =
           (slope * slope - point_x1 - point_x2) mod SM2_P_Z /\
         result_y =
           (slope * (point_x1 - result_x) - point_y1) mod SM2_P_Z).
      split; reflexivity.
    }
    assert (Hresult_curve :
      sm2_affine_on_curve result_x result_y).
    {
      apply
        (sm2_affine_sum_on_curve_distinct_x
          point_x1 point_y1 point_x2 point_y2
          slope result_x result_y);
        assumption.
    }
    assert (Hresult_x_m :
      eqm SM2_P_Z
        result_x (slope * slope - point_x1 - point_x2)).
    {
      unfold result_x.
      apply Zmod_eqm.
    }
    assert (Hresult_y_m :
      eqm SM2_P_Z
        result_y (slope * (point_x1 - result_x) - point_y1)).
    {
      unfold result_y.
      apply Zmod_eqm.
    }
    pose proof
      (sm2_mixed_add_formula_eqm
        point_x1 point_y1 point_x2 point_y2
        jz slope result_x result_y
        jx jy z2 a b c2 c3 x1c2 d2 x1c22 rx tmp ry rz
        Hjx_m Hjy_m Hz2 Ha Hb Hc2 Hc3 Hx1c2 Hd2 Hx1c22
        Hrx Htmp Hry Hrz Hslope_m Hresult_x_m Hresult_y_m)
      as [Hrx_result Hry_result].
    assert (Hrz_nonzero : rz <> 0).
    {
      assert (Hproduct_nonzero :
        (jz * a) mod SM2_P_Z <> 0).
      {
        apply sm2_eqm_product_nonzero;
          assumption.
      }
      assert (Hrz_eq : rz = (jz * a) mod SM2_P_Z).
      {
        apply
          (sm2_eqm_canonical_left rz (jz * a)
            Hrz_bounds Hrz).
      }
      rewrite Hrz_eq.
      exact Hproduct_nonzero.
    }
    rewrite
      (sm2_point_add_affine_distinct
        point_x1 point_y1 point_x2 point_y2
        slope result_x result_y
        Hcurve1 Hcurve2 Hresult_curve Hxneq Hslope Hsum).
    cbn [jpoint_represents ec_point_of_affine].
    split; [exact Hrx_bounds |].
    split; [exact Hry_bounds |].
    split; [exact Hrz_bounds |].
    split; [exact Hrz_nonzero |].
    split.
    + rewrite
        (sm2_fe_value_of_Z result_x (proj1 Hresult_curve)).
      apply
        (sm2_eqm_canonical_left
          rx (result_x * rz ^ 2) Hrx_bounds).
      setoid_rewrite Hrx_result.
      unfold eqm. f_equal. ring.
    + rewrite
        (sm2_fe_value_of_Z result_y (proj1 (proj2 Hresult_curve))).
      apply
        (sm2_eqm_canonical_left
          ry (result_y * rz ^ 3) Hry_bounds).
      setoid_rewrite Hry_result.
      unfold eqm. f_equal. ring.
Qed.

(** Exact modular equations emitted by the symbolic execution of
    [add_JPoint_and_AFPoint], bridged to the representation-level lemma
    above. *)
Lemma jpoint_add_afpoint_mixed_mod_represents :
  forall P1 P2
         jx jy jz x2 y2 z2 a b c2 c3 x1c2 d2 x1c22
         rx tmp ry rz,
    P1 <> ECInfinity ->
    P2 <> ECInfinity ->
    P1 <> P2 ->
    jpoint_represents jx jy jz P1 ->
    afpoint_represents x2 y2 P2 ->
    0 <= a < SM2_P_Z ->
    0 <= rx < SM2_P_Z ->
    0 <= ry < SM2_P_Z ->
    0 <= rz < SM2_P_Z ->
    z2 = (jz * jz) mod SM2_P_Z ->
    a = ((x2 * z2) mod SM2_P_Z - jx) mod SM2_P_Z ->
    b = (((y2 * z2) mod SM2_P_Z * jz) mod SM2_P_Z - jy)
          mod SM2_P_Z ->
    c2 = (a * a) mod SM2_P_Z ->
    c3 = (c2 * a) mod SM2_P_Z ->
    x1c2 = (jx * c2) mod SM2_P_Z ->
    d2 = (b * b) mod SM2_P_Z ->
    x1c22 = (x1c2 + x1c2) mod SM2_P_Z ->
    rx = ((d2 - x1c22) mod SM2_P_Z - c3) mod SM2_P_Z ->
    tmp = (x1c2 - rx) mod SM2_P_Z ->
    ry = ((b * tmp) mod SM2_P_Z - (jy * c3) mod SM2_P_Z)
           mod SM2_P_Z ->
    rz = (jz * a) mod SM2_P_Z ->
    jpoint_represents rx ry rz (sm2_point_add P1 P2).
Proof.
  intros P1 P2
    jx jy jz x2 y2 z2 a b c2 c3 x1c2 d2 x1c22
    rx tmp ry rz
    HP1finite HP2finite HPneq HJ HA
    Ha_bounds Hrx_bounds Hry_bounds Hrz_bounds
    Hz2 Ha Hb Hc2 Hc3 Hx1c2 Hd2 Hx1c22
    Hrx Htmp Hry Hrz.
  eapply
    (jpoint_add_afpoint_mixed_represents
      P1 P2 jx jy jz x2 y2 z2 a b c2 c3 x1c2 d2 x1c22
      rx tmp ry rz);
    try eassumption.
  - rewrite Hz2.
    apply Zmod_eqm.
  - rewrite Ha.
    eapply eqm_trans; [apply Zmod_eqm |].
    apply Zminus_eqm.
    + apply Zmod_eqm.
    + apply eqm_refl.
  - rewrite Hb.
    eapply eqm_trans; [apply Zmod_eqm |].
    apply Zminus_eqm.
    + eapply eqm_trans; [apply Zmod_eqm |].
      apply Zmult_eqm.
      * apply Zmod_eqm.
      * apply eqm_refl.
    + apply eqm_refl.
  - rewrite Hc2.
    apply Zmod_eqm.
  - rewrite Hc3.
    apply Zmod_eqm.
  - rewrite Hx1c2.
    apply Zmod_eqm.
  - rewrite Hd2.
    apply Zmod_eqm.
  - rewrite Hx1c22.
    apply Zmod_eqm.
  - rewrite Hrx.
    eapply eqm_trans; [apply Zmod_eqm |].
    apply Zminus_eqm.
    + apply Zmod_eqm.
    + apply eqm_refl.
  - rewrite Htmp.
    apply Zmod_eqm.
  - rewrite Hry.
    eapply eqm_trans; [apply Zmod_eqm |].
    apply Zminus_eqm; apply Zmod_eqm.
  - rewrite Hrz.
    apply Zmod_eqm.
Qed.

Lemma afpoint_represents_infinity_iff :
  forall x y point,
    afpoint_represents x y point ->
    (x = 0 /\ y = 0 <-> point = ECInfinity).
Proof.
  intros x y point Hrep.
  destruct point as [|point_x point_y Hcurve].
  - simpl in Hrep. tauto.
  - split.
    + intros [Hx Hy].
      simpl in Hrep.
      destruct Hrep as [Hpoint_x Hpoint_y].
      exfalso.
      apply sm2_origin_not_on_curve.
      apply ec_point_affine_coordinates_on_curve with
        (point :=
          @SMain.curve_elt
            (ZEll.pK SM2_P_Z)
            (ZEll.pkI SM2_P_Z) (@ZEll.pkplus SM2_P_Z)
            (@ZEll.pkmul SM2_P_Z)
            (ZEll.pA SM2_A_Z SM2_P_Z)
            (ZEll.pB SM2_B_Z SM2_P_Z)
            point_x point_y Hcurve).
      cbn [ec_point_affine_coordinates].
      split; lia.
    + discriminate.
Qed.

Lemma jpoint_represents_infinity_iff :
  forall x y z point,
    jpoint_represents x y z point ->
    (z = 0 <-> point = ECInfinity).
Proof.
  intros x y z point Hrep.
  destruct point as [|point_x point_y Hcurve].
  - simpl in Hrep.
    destruct Hrep as [_ [_ [_ Hz]]].
    split.
    + intros. reflexivity.
    + intros. exact Hz.
  - simpl in Hrep.
    destruct Hrep as [_ [_ [_ [Hz _]]]].
    split.
    + intros Hzero. exfalso. exact (Hz Hzero).
    + discriminate.
Qed.

Lemma jpoint_x_coordinate_represents :
  forall x y z result_x point,
    jpoint_represents x y z point ->
    ((z = 0 /\ result_x = 0) \/
     (z <> 0 /\
      exists z_inverse,
        0 <= z_inverse < SM2_P_Z /\
        (z * z_inverse) mod SM2_P_Z = 1 /\
        result_x = (x * z_inverse * z_inverse) mod SM2_P_Z)) ->
    exists result_y, afpoint_represents result_x result_y point.
Proof.
  intros x y z result_x point Hrep Hresult.
  destruct Hresult as [[Hz Hresult_x] |
    [Hz [z_inverse [Hinverse_bounds [Hinverse Hresult_x]]]]].
  - pose proof
      (proj1 (jpoint_represents_infinity_iff x y z point Hrep) Hz)
      as Hpoint.
    subst point result_x.
    exists 0.
    unfold ECInfinity.
    cbn [afpoint_represents afpoint_infinity].
    unfold afpoint_infinity.
    tauto.
  - exists ((y * z_inverse * z_inverse * z_inverse) mod SM2_P_Z).
    eapply jpoint_to_afpoint_coordinates_represents; [exact Hrep |].
    unfold jpoint_to_afpoint_coordinates.
    right.
    split; [exact Hz |].
    exists z_inverse.
    split; [exact Hinverse_bounds |].
    split; [exact Hinverse |].
    split.
    + rewrite Hresult_x, Z.pow_2_r.
      f_equal; ring.
    + f_equal.
      ring.
Qed.

(** The frontend may print a nested [JPoint] coordinate projection either as
    [point->field.v] or through the address of the embedded [u32]. *)
Lemma nested_jpoint_u32_v_addr_eq :
  forall (point : Z) (field : string),
    &((point) # "JPoint" ->ₛ field .ₛ "v") =
    &(((&(point # "JPoint" ->ₛ field))) # "u32" ->ₛ "v").
Proof.
  intros.
  csimpl.
  reflexivity.
Qed.

(** The same frontend address equivalence for a named [JPoint] object,
    such as a stack local materialized during aggregate initialization. *)
Lemma named_jpoint_u32_v_addr_eq :
  forall (name field : string),
    eval_addr_expr
      (RE_addr_of
        (LE_dot_field
          (LE_arrow_field (RE_addr_of (LE_var name)) field)
          "v")) =
    eval_addr_expr
      (RE_addr_of
        (LE_dot_field
          (LE_arrow_field
            (RE_const
              (eval_addr_expr (RE_addr_of (LE_var name)))
              (FET_alias "JPoint"))
            field)
          "v")).
Proof.
  intros.
  csimpl.
  reflexivity.
Qed.

(** * Point memory predicates *)

(** Exact P-field integers stored in an [AFPoint] object. *)
Definition store_afpoint_fields (address : addr) (x y : Z) : Assertion :=
  store_fp (&(address # "AFPoint" ->ₛ "x")) x **
  store_fp (&(address # "AFPoint" ->ₛ "y")) y.

(** Exact P-field integers stored in a [JPoint] object. *)
Definition store_jpoint_fields (address : addr) (x y z : Z) : Assertion :=
  store_fp (&(address # "JPoint" ->ₛ "x")) x **
  store_fp (&(address # "JPoint" ->ₛ "y")) y **
  store_fp (&(address # "JPoint" ->ₛ "z")) z.

Lemma store_jpoint_fields_conflict :
  forall address x1 y1 z1 x2 y2 z2,
    store_jpoint_fields address x1 y1 z1 **
    store_jpoint_fields address x2 y2 z2 |-- “ False ”.
Proof.
  intros address x1 y1 z1 x2 y2 z2.
  unfold store_jpoint_fields, store_fp, store_mod.
  Intros.
  sep_apply
    (store_u256_to_undef (&(address # "JPoint" ->ₛ "x")) x2).
  sep_apply
    (store_u256_undef_conflict (&(address # "JPoint" ->ₛ "x")) x1).
  entailer!.
Qed.

Lemma store_jpoint_fields_neq :
  forall address1 address2 x1 y1 z1 x2 y2 z2,
    store_jpoint_fields address1 x1 y1 z1 **
    store_jpoint_fields address2 x2 y2 z2 |-- “ address1 <> address2 ”.
Proof.
  intros address1 address2 x1 y1 z1 x2 y2 z2.
  destruct (Z.eq_dec address1 address2) as [Heq | Hneq].
  - subst address2.
    sep_apply
      (store_jpoint_fields_conflict address1 x1 y1 z1 x2 y2 z2).
    entailer!.
  - entailer!.
Qed.

(** A single stored coordinate is enough to distinguish two JPoint bases.
    This bridge is useful in symbolic states where the three coordinates
    have deliberately not yet been repacked as [store_jpoint_fields]. *)
Lemma store_jpoint_x_cells_neq :
  forall address1 address2 x1 x2,
    store_fp (&(address1 # "JPoint" ->ₛ "x")) x1 **
    store_fp (&(address2 # "JPoint" ->ₛ "x")) x2
    |-- “ address1 <> address2 ”.
Proof.
  intros address1 address2 x1 x2.
  destruct (Z.eq_dec address1 address2) as [Heq | Hneq].
  - subst address2.
    unfold store_fp, store_mod.
    Intros.
    sep_apply
      (store_u256_to_undef (&(address1 # "JPoint" ->ₛ "x")) x2).
    sep_apply
      (store_u256_undef_conflict (&(address1 # "JPoint" ->ₛ "x")) x1).
    entailer!.
  - entailer!.
Qed.

(** Coordinate-level companion of [store_jpoint_fields_undef_neq]. *)
Lemma store_jpoint_x_cell_undef_neq :
  forall stored_address undef_address x,
    store_fp (&(stored_address # "JPoint" ->ₛ "x")) x **
    UndefStructPredJPoint undef_address
    |-- “ stored_address <> undef_address ”.
Proof.
  intros stored_address undef_address x.
  destruct (Z.eq_dec stored_address undef_address) as [Heq | Hneq].
  - subst undef_address.
    unfold store_fp, store_mod, UndefStructPredJPoint.
    Intros.
    sep_apply
      (store_u256_undef_conflict
         (&(stored_address # "JPoint" ->ₛ "x")) x).
    entailer!.
  - entailer!.
Qed.

Lemma store_jpoint_fields_undef_conflict :
  forall address x y z,
    store_jpoint_fields address x y z **
    UndefStructPredJPoint address |-- “ False ”.
Proof.
  intros address x y z.
  unfold store_jpoint_fields, UndefStructPredJPoint, store_fp, store_mod.
  Intros.
  sep_apply
    (store_u256_undef_conflict (&(address # "JPoint" ->ₛ "x")) x).
  entailer!.
Qed.

Lemma store_jpoint_undef_fields_conflict :
  forall address x y z,
    UndefStructPredJPoint address **
    store_jpoint_fields address x y z |-- “ False ”.
Proof.
  intros address x y z.
  eapply derivable1_trans with
    (y := store_jpoint_fields address x y z **
          UndefStructPredJPoint address).
  - cancel.
  - apply store_jpoint_fields_undef_conflict.
Qed.

Lemma store_jpoint_fields_undef_neq :
  forall stored_address undef_address x y z,
    store_jpoint_fields stored_address x y z **
    UndefStructPredJPoint undef_address |--
    “ stored_address <> undef_address ”.
Proof.
  intros stored_address undef_address x y z.
  destruct (Z.eq_dec stored_address undef_address) as [Heq | Hneq].
  - subst undef_address.
    sep_apply (store_jpoint_fields_undef_conflict stored_address x y z).
    entailer!.
  - entailer!.
Qed.

Lemma store_three_jpoints_non_alias :
  forall point1 point2 point3 x1 y1 z1 x2 y2 z2 x3 y3 z3,
    store_jpoint_fields point1 x1 y1 z1 **
    store_jpoint_fields point3 x3 y3 z3 **
    store_jpoint_fields point2 x2 y2 z2 |--
    “ point1 <> point2 ” &&
    “ point1 <> point3 ” &&
    “ point2 <> point3 ”.
Proof.
  intros point1 point2 point3 x1 y1 z1 x2 y2 z2 x3 y3 z3.
  destruct (Z.eq_dec point1 point2) as [Heq | Hpoint1_point2].
  - subst point2.
    sep_lift_L ((store_jpoint_fields point1 x1 y1 z1) ::
                (store_jpoint_fields point1 x2 y2 z2) :: nil).
    sep_apply (store_jpoint_fields_conflict point1 x2 y2 z2 x1 y1 z1).
    entailer!.
  - destruct (Z.eq_dec point1 point3) as [Heq | Hpoint1_point3].
    + subst point3.
      sep_lift_L ((store_jpoint_fields point1 x1 y1 z1) ::
                  (store_jpoint_fields point1 x3 y3 z3) :: nil).
      sep_apply (store_jpoint_fields_conflict point1 x3 y3 z3 x1 y1 z1).
      entailer!.
    + destruct (Z.eq_dec point2 point3) as [Heq | Hpoint2_point3].
      * subst point3.
        sep_lift_L ((store_jpoint_fields point2 x2 y2 z2) ::
                    (store_jpoint_fields point2 x3 y3 z3) :: nil).
        sep_apply (store_jpoint_fields_conflict point2 x3 y3 z3 x2 y2 z2).
        entailer!.
      * entailer!.
Qed.

Lemma store_three_jpoints_and_undef_non_alias :
  forall result point1 point2 point3
         x1 y1 z1 x2 y2 z2 x3 y3 z3,
    store_jpoint_fields point1 x1 y1 z1 **
    store_jpoint_fields point3 x3 y3 z3 **
    store_jpoint_fields point2 x2 y2 z2 **
    UndefStructPredJPoint result |--
    “ result <> point1 ” &&
    “ result <> point2 ” &&
    “ point1 <> point2 ” &&
    “ point1 <> point3 ” &&
    “ point2 <> point3 ”.
Proof.
  intros result point1 point2 point3
         x1 y1 z1 x2 y2 z2 x3 y3 z3.
  destruct (Z.eq_dec result point1) as [Heq | Hresult_point1].
  - subst result.
    sep_lift_L ((UndefStructPredJPoint point1) ::
                (store_jpoint_fields point1 x1 y1 z1) :: nil).
    sep_apply (store_jpoint_undef_fields_conflict point1 x1 y1 z1).
    entailer!.
  - destruct (Z.eq_dec result point2) as [Heq | Hresult_point2].
    + subst result.
      sep_lift_L ((UndefStructPredJPoint point2) ::
                  (store_jpoint_fields point2 x2 y2 z2) :: nil).
      sep_apply (store_jpoint_undef_fields_conflict point2 x2 y2 z2).
      entailer!.
    + prop_apply
        (store_three_jpoints_non_alias
           point1 point2 point3
           x1 y1 z1 x2 y2 z2 x3 y3 z3).
      entailer!.
Qed.

(** Canonical field coordinates stored in Montgomery form. *)
Definition store_mont_afpoint_coords
    (address : addr) (x y : Z) : Assertion :=
  “ 0 <= x < SM2_P_Z ” &&
  “ 0 <= y < SM2_P_Z ” &&
  store_afpoint_fields address (mont_p x) (mont_p y).

Definition store_mont_jpoint_coords
    (address : addr) (x y z : Z) : Assertion :=
  “ 0 <= x < SM2_P_Z ” &&
  “ 0 <= y < SM2_P_Z ” &&
  “ 0 <= z < SM2_P_Z ” &&
  store_jpoint_fields address (mont_p x) (mont_p y) (mont_p z).

(** One ordinary affine C object representing [point]. *)
Definition store_afpoint (address : addr) (point : ec_point) : Assertion :=
  EX x y,
    “ afpoint_represents x y point ” &&
    store_afpoint_fields address x y.

Definition record_afpoint_well_formed (record : RecordAFPoint) : Prop :=
  record_u32_well_formed record.(AFPoint_x) /\
  record_u32_well_formed record.(AFPoint_y).

Lemma StructPredAFPoint_well_formed :
  forall address record,
    StructPredAFPoint address record |--
    “ record_afpoint_well_formed record ”.
Proof.
  intros address record.
  unfold StructPredAFPoint, record_afpoint_well_formed.
  prop_apply
    (StructPredu32_well_formed
      (&(address # "AFPoint" ->ₛ "x")) record.(AFPoint_x)).
  Intros.
  prop_apply
    (StructPredu32_well_formed
      (&(address # "AFPoint" ->ₛ "y")) record.(AFPoint_y)).
  entailer!.
Qed.

Lemma StructPredAFPoint_to_store_afpoint :
  forall address record point,
    afpoint_represents
      (u64_list_value record.(AFPoint_x).(u32_v))
      (u64_list_value record.(AFPoint_y).(u32_v))
      point ->
    StructPredAFPoint address record |-- store_afpoint address point.
Proof.
  intros address record point Hrepresents.
  pose proof (afpoint_represents_bounds _ _ _ Hrepresents)
    as [Hx Hy].
  unfold StructPredAFPoint, StructPredu32.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  unfold store_afpoint, store_afpoint_fields, store_fp, store_mod,
    store_u256.
  Exists
    (u64_list_value record.(AFPoint_x).(u32_v))
    (u64_list_value record.(AFPoint_y).(u32_v)).
  entailer!; csimpl; entailer!.
Qed.

Lemma store_afpoint_fields_to_StructPredAFPoint :
  forall address record,
    record_afpoint_well_formed record ->
    store_afpoint_fields address
      (u64_list_value record.(AFPoint_x).(u32_v))
      (u64_list_value record.(AFPoint_y).(u32_v)) |--
    StructPredAFPoint address record.
Proof.
  intros address record [Hx_well_formed Hy_well_formed].
  unfold store_afpoint_fields, store_fp, store_mod.
  Intros.
  unfold StructPredAFPoint.
  sep_apply
    (store_u256_to_StructPredu32
      (&(address # "AFPoint" ->ₛ "x"))
      (u64_list_value record.(AFPoint_x).(u32_v))
      record.(AFPoint_x) Hx_well_formed eq_refl).
  sep_apply
    (store_u256_to_StructPredu32
      (&(address # "AFPoint" ->ₛ "y"))
      (u64_list_value record.(AFPoint_y).(u32_v))
      record.(AFPoint_y) Hy_well_formed eq_refl).
  entailer!.
Qed.

Lemma store_afpoint_to_StructPredAFPoint :
  forall address record point,
    record_afpoint_well_formed record ->
    afpoint_represents
      (u64_list_value record.(AFPoint_x).(u32_v))
      (u64_list_value record.(AFPoint_y).(u32_v))
      point ->
    store_afpoint address point |-- StructPredAFPoint address record.
Proof.
  intros address record point Hwell_formed Hrecord_represents.
  unfold store_afpoint.
  Intros x y.
  destruct (afpoint_represents_functional
    _ _ _ _ point H Hrecord_represents) as [-> ->].
  apply store_afpoint_fields_to_StructPredAFPoint.
  exact Hwell_formed.
Qed.

(** One ordinary Jacobian C object representing [point]. *)
Definition store_jpoint (address : addr) (point : ec_point) : Assertion :=
  EX x y z,
    “ jpoint_represents x y z point ” &&
    store_jpoint_fields address x y z.

(** A Jacobian point whose infinity representation follows the API's
    distinguished [(1, 1, 0)] encoding.  Finite Jacobian coordinates remain
    unrestricted apart from [jpoint_represents]. *)
Definition store_jpoint_with_canonical_infinity
    (address : addr) (point : ec_point) : Assertion :=
  EX x y z,
    “ jpoint_represents x y z point /\
      (point = ECInfinity ->
       canonical_jpoint_infinity x y z) ” &&
    store_jpoint_fields address x y z.

Lemma store_jpoint_fields_to_store_jpoint_with_canonical_infinity :
  forall address x y z point,
    jpoint_represents x y z point ->
    (point = ECInfinity -> canonical_jpoint_infinity x y z) ->
    store_jpoint_fields address x y z |--
    store_jpoint_with_canonical_infinity address point.
Proof.
  intros address x y z point Hrep Hcanonical.
  unfold store_jpoint_with_canonical_infinity.
  Exists x y z.
  entailer!.
Qed.

Lemma store_jpoint_with_canonical_infinity_forget :
  forall address point,
    store_jpoint_with_canonical_infinity address point |--
    store_jpoint address point.
Proof.
  intros address point.
  unfold store_jpoint_with_canonical_infinity, store_jpoint.
  Intros x y z.
  Exists x y z.
  entailer!.
Qed.

Lemma store_jpoint_noninfinity_is_canonical :
  forall address point,
    point <> ECInfinity ->
    store_jpoint address point |--
    store_jpoint_with_canonical_infinity address point.
Proof.
  intros address point Hfinite.
  unfold store_jpoint, store_jpoint_with_canonical_infinity.
  Intros x y z.
  Exists x y z.
  entailer!.
Qed.

(** One Montgomery-encoded affine C object representing [point]. *)
Definition store_mont_afpoint (address : addr) (point : ec_point) : Assertion :=
  EX x y,
    “ afpoint_represents x y point ” &&
    store_mont_afpoint_coords address x y.

(** One Montgomery-encoded Jacobian C object representing [point]. *)
Definition store_mont_jpoint (address : addr) (point : ec_point) : Assertion :=
  EX x y z,
    “ jpoint_represents x y z point ” &&
    store_mont_jpoint_coords address x y z.

(** * Global curve and point constants *)

Definition store_sm2_a : Assertion :=
  store_fp (&("SM2_a")) SM2_A_Z.

Definition store_sm2_b : Assertion :=
  store_fp (&("SM2_b")) SM2_B_Z.

Definition store_jpoint_zero : Assertion :=
  store_jpoint_fields (&("JPoint_ZERO")) 1 1 0.

Lemma jpoint_zero_arrays_fold :
  forall xs ys zs,
    u64_list_value xs = 1 ->
    u64_list_value ys = 1 ->
    u64_list_value zs = 0 ->
    UInt64Array.full (&(( &("JPoint_ZERO")) ->ₛ "z" .ₛ "v")) 4 zs **
    UInt64Array.full (&(( &("JPoint_ZERO")) ->ₛ "y" .ₛ "v")) 4 ys **
    UInt64Array.full (&(( &("JPoint_ZERO")) ->ₛ "x" .ₛ "v")) 4 xs
    |-- store_jpoint_zero.
Proof.
  intros xs ys zs Hx Hy Hz.
  do 3 sep_apply uint64_full4_to_store_u256_limbs.
  rewrite Hx, Hy, Hz.
  unfold store_jpoint_zero, store_jpoint_fields,
    store_fp, store_mod, store_u256.
  pose proof sm2_p_gt_one.
  entailer!.
  csimpl.
  cancel.
Qed.

Definition store_sm2_inv2p : Assertion :=
  store_fp (&("SM2_inv2P")) SM2_P_INV2_Z.

Definition MONTG_ONE_Z : Z := mont_p 1.

Lemma montg_one_eq_sm2_rhop :
  MONTG_ONE_Z = SM2_RHOP_Z.
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition store_bn_zero : Assertion :=
  store_u256_limbs (&("BN_ZERO")) 0.

Definition store_montg_one : Assertion :=
  store_u256_limbs (&("MONTG_ONE")) MONTG_ONE_Z.
