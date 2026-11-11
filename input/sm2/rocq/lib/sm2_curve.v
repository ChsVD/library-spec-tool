(** Coqprime-backed mathematical model of the standard SM2 curve. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From Coqprime Require Import elliptic.SMain elliptic.ZEll.
Require Import Coqprime.PrimalityTest.EGroup.
From SimpleC.EE.Applications_human.sm2.lib
  Require Export sm2_curve_params.
From SimpleC.EE.Applications_human.sm2.lib
  Require Import sm2_primality.

Local Open Scope Z_scope.

(** * Prime-field curve instance *)

Lemma sm2_p_not_divides_two :
  ~ (2 | SM2_P_Z).
Proof.
  intros Hdivides.
  pose proof
    (proj2 (Z.mod_divide SM2_P_Z 2 ltac:(lia)) Hdivides) as Hmod.
  vm_compute in Hmod.
  discriminate.
Qed.

Lemma sm2_curve_nonsingular :
  rel_prime SM2_P_Z
    (4 * SM2_A_Z * SM2_A_Z * SM2_A_Z +
     27 * SM2_B_Z * SM2_B_Z).
Proof.
  apply prime_rel_prime.
  - exact sm2_p_prime.
  - intros Hdivides.
    assert (Hp_nonzero : SM2_P_Z <> 0) by
      (pose proof sm2_p_gt_one; lia).
    pose proof
      (proj2
        (Z.mod_divide
          (4 * SM2_A_Z * SM2_A_Z * SM2_A_Z +
           27 * SM2_B_Z * SM2_B_Z)
          SM2_P_Z Hp_nonzero)
        Hdivides) as Hmod.
    vm_compute in Hmod.
    discriminate.
Qed.

Definition sm2_curve_theory :=
  ZEll.pell_theory
    SM2_A_Z SM2_B_Z
    sm2_p_not_divides_two
    sm2_curve_nonsingular
    sm2_p_prime
    (Z.divide_refl SM2_P_Z).

(** * Field values and abstract points *)

Definition sm2_fe : Set := ZEll.pK SM2_P_Z.

Definition sm2_fe_of_Z (value : Z) : sm2_fe :=
  @GZnZ.mkznz
    SM2_P_Z (value mod SM2_P_Z) (GZnZ.modz SM2_P_Z value).

Definition sm2_fe_value (value : sm2_fe) : Z :=
  @GZnZ.val SM2_P_Z value.

Lemma sm2_fe_value_bounds :
  forall value,
    0 <= sm2_fe_value value < SM2_P_Z.
Proof.
  intros [value Hvalue].
  unfold sm2_fe_value.
  cbn.
  rewrite Hvalue.
  apply Z.mod_pos_bound.
  pose proof sm2_p_gt_one.
  lia.
Qed.

Lemma sm2_fe_value_of_Z :
  forall value,
    0 <= value < SM2_P_Z ->
    sm2_fe_value (sm2_fe_of_Z value) = value.
Proof.
  intros value Hvalue.
  unfold sm2_fe_value, sm2_fe_of_Z.
  cbn.
  apply Z.mod_small.
  exact Hvalue.
Qed.

Lemma sm2_fe_of_Z_value :
  forall value,
    sm2_fe_of_Z (sm2_fe_value value) = value.
Proof.
  intros [value Hvalue].
  unfold sm2_fe_of_Z, sm2_fe_value.
  cbn.
  apply GZnZ.zirr.
  symmetry.
  exact Hvalue.
Qed.

Lemma sm2_fe_of_Z_eq_iff :
  forall left right,
    sm2_fe_of_Z left = sm2_fe_of_Z right <->
    left mod SM2_P_Z = right mod SM2_P_Z.
Proof.
  intros left right.
  split.
  - intros Hequal.
    exact (@GZnZ.znz_inj SM2_P_Z _ _ Hequal).
  - intros Hequal.
    unfold sm2_fe_of_Z.
    apply GZnZ.zirr.
    exact Hequal.
Qed.

Lemma sm2_fe_of_Z_add :
  forall left right,
    sm2_fe_of_Z (left + right) =
    ZEll.pkplus (sm2_fe_of_Z left) (sm2_fe_of_Z right).
Proof.
  intros left right.
  unfold sm2_fe_of_Z, ZEll.pkplus, GZnZ.add.
  apply GZnZ.zirr.
  cbn.
  rewrite Z.add_mod by (pose proof sm2_p_gt_one; lia).
  reflexivity.
Qed.

Lemma sm2_fe_of_Z_mul :
  forall left right,
    sm2_fe_of_Z (left * right) =
    ZEll.pkmul (sm2_fe_of_Z left) (sm2_fe_of_Z right).
Proof.
  intros left right.
  unfold sm2_fe_of_Z, ZEll.pkmul, GZnZ.mul.
  apply GZnZ.zirr.
  cbn.
  rewrite Z.mul_mod by (pose proof sm2_p_gt_one; lia).
  reflexivity.
Qed.

Lemma sm2_fe_of_Z_sub :
  forall left right,
    sm2_fe_of_Z (left - right) =
    ZEll.pksub (sm2_fe_of_Z left) (sm2_fe_of_Z right).
Proof.
  intros left right.
  unfold sm2_fe_of_Z, ZEll.pksub, GZnZ.sub.
  apply GZnZ.zirr.
  cbn.
  rewrite Zminus_mod by (pose proof sm2_p_gt_one; lia).
  reflexivity.
Qed.

Lemma sm2_fe_of_Z_opp :
  forall value,
    sm2_fe_of_Z (- value) = ZEll.pkopp (sm2_fe_of_Z value).
Proof.
  intros value.
  unfold sm2_fe_of_Z, ZEll.pkopp, GZnZ.opp.
  apply GZnZ.zirr.
  cbn.
  replace (- value) with (0 - value) by ring.
  replace (- (value mod SM2_P_Z))
    with (0 - value mod SM2_P_Z) by ring.
  rewrite Zminus_mod by (pose proof sm2_p_gt_one; lia).
  rewrite Z.mod_0_l by (pose proof sm2_p_gt_one; lia).
  reflexivity.
Qed.

Lemma sm2_fe_of_Z_one :
  sm2_fe_of_Z 1 = ZEll.pkI SM2_P_Z.
Proof. reflexivity. Qed.

Lemma sm2_fe_of_Z_two :
  sm2_fe_of_Z 2 =
  ZEll.pkplus (ZEll.pkI SM2_P_Z) (ZEll.pkI SM2_P_Z).
Proof.
  replace 2 with (1 + 1) by reflexivity.
  rewrite sm2_fe_of_Z_add, sm2_fe_of_Z_one.
  reflexivity.
Qed.

Lemma sm2_fe_of_Z_three :
  sm2_fe_of_Z 3 =
  ZEll.pkplus
    (ZEll.pkplus (ZEll.pkI SM2_P_Z) (ZEll.pkI SM2_P_Z))
    (ZEll.pkI SM2_P_Z).
Proof.
  replace 3 with ((1 + 1) + 1) by reflexivity.
  rewrite !sm2_fe_of_Z_add, sm2_fe_of_Z_one.
  reflexivity.
Qed.

(** A modular integer solution of a nonzero linear equation is the field
    quotient used by Coqprime.  This is the only fact clients need about
    [ZEll.pkdiv]; its extended-Euclidean implementation stays hidden. *)
Lemma sm2_fe_of_Z_div_solution :
  forall numerator denominator quotient,
    denominator mod SM2_P_Z <> 0 ->
    eqm SM2_P_Z (denominator * quotient) numerator ->
    sm2_fe_of_Z quotient =
      ZEll.pkdiv
        (sm2_fe_of_Z numerator) (sm2_fe_of_Z denominator).
Proof.
  intros numerator denominator quotient Hdenominator Hrelation.
  assert (Hdenominator_fe :
    sm2_fe_of_Z denominator <> ZEll.pkO SM2_P_Z).
  {
    intros Hzero.
    apply Hdenominator.
    apply (proj1 (sm2_fe_of_Z_eq_iff denominator 0)).
    change (sm2_fe_of_Z denominator = sm2_fe_of_Z 0).
    rewrite Hzero.
    reflexivity.
  }
  assert (Hproduct :
    ZEll.pkmul
      (sm2_fe_of_Z denominator) (sm2_fe_of_Z quotient) =
    sm2_fe_of_Z numerator).
  {
    rewrite <- sm2_fe_of_Z_mul.
    apply (proj2 (sm2_fe_of_Z_eq_iff _ _)).
    exact Hrelation.
  }
  rewrite
    (Field_theory.Fdiv_def (sm2_curve_theory.(SMain.Kfth))).
  rewrite <- Hproduct.
  rewrite
    ((sm2_curve_theory.(SMain.Kfth)).(Field_theory.F_R).(Ring_theory.Rmul_comm)
      (sm2_fe_of_Z denominator) (sm2_fe_of_Z quotient)).
  rewrite <-
    ((sm2_curve_theory.(SMain.Kfth)).(Field_theory.F_R).(Ring_theory.Rmul_assoc)
      (sm2_fe_of_Z quotient) (sm2_fe_of_Z denominator)
      (ZEll.pkinv (sm2_fe_of_Z denominator))).
  rewrite
    ((sm2_curve_theory.(SMain.Kfth)).(Field_theory.F_R).(Ring_theory.Rmul_comm)
      (sm2_fe_of_Z denominator)
      (ZEll.pkinv (sm2_fe_of_Z denominator))).
  rewrite
    ((sm2_curve_theory.(SMain.Kfth)).(Field_theory.Finv_l)
      (sm2_fe_of_Z denominator) Hdenominator_fe).
  rewrite
    ((sm2_curve_theory.(SMain.Kfth)).(Field_theory.F_R).(Ring_theory.Rmul_comm)
      (sm2_fe_of_Z quotient) (ZEll.pkI SM2_P_Z)).
  symmetry.
  apply
    ((sm2_curve_theory.(SMain.Kfth)).(Field_theory.F_R).(Ring_theory.Rmul_1_l)).
Qed.

Lemma sm2_curve_a_as_fe :
  ZEll.pA SM2_A_Z SM2_P_Z = sm2_fe_of_Z SM2_A_Z.
Proof.
  unfold ZEll.pA, sm2_fe_of_Z.
  apply GZnZ.zirr.
  reflexivity.
Qed.

Lemma sm2_curve_b_as_fe :
  ZEll.pB SM2_B_Z SM2_P_Z = sm2_fe_of_Z SM2_B_Z.
Proof.
  unfold ZEll.pB, sm2_fe_of_Z.
  apply GZnZ.zirr.
  reflexivity.
Qed.

Definition ec_point : Set :=
  SMain.elt
    (ZEll.pkI SM2_P_Z)
    (@ZEll.pkplus SM2_P_Z)
    (@ZEll.pkmul SM2_P_Z)
    (ZEll.pA SM2_A_Z SM2_P_Z)
    (ZEll.pB SM2_B_Z SM2_P_Z).

Definition ECInfinity : ec_point :=
  SMain.inf_elt
    (ZEll.pkI SM2_P_Z)
    (@ZEll.pkplus SM2_P_Z)
    (@ZEll.pkmul SM2_P_Z)
    (ZEll.pA SM2_A_Z SM2_P_Z)
    (ZEll.pB SM2_B_Z SM2_P_Z).

Definition sm2_affine_equation (x y : Z) : Prop :=
  SMain.pow
    (ZEll.pkI SM2_P_Z) (@ZEll.pkmul SM2_P_Z) (sm2_fe_of_Z y) 2 =
  ZEll.pkplus
    (ZEll.pkplus
      (SMain.pow
        (ZEll.pkI SM2_P_Z) (@ZEll.pkmul SM2_P_Z) (sm2_fe_of_Z x) 3)
      (ZEll.pkmul (ZEll.pA SM2_A_Z SM2_P_Z) (sm2_fe_of_Z x)))
    (ZEll.pB SM2_B_Z SM2_P_Z).

Definition sm2_affine_on_curve (x y : Z) : Prop :=
  0 <= x < SM2_P_Z /\
  0 <= y < SM2_P_Z /\
  sm2_affine_equation x y.

Lemma sm2_affine_equation_iff :
  forall x y,
    sm2_affine_equation x y <->
    (y * y) mod SM2_P_Z =
    (x * x * x + SM2_A_Z * x + SM2_B_Z) mod SM2_P_Z.
Proof.
  intros x y.
  unfold sm2_affine_equation.
  rewrite sm2_curve_a_as_fe, sm2_curve_b_as_fe.
  cbn [SMain.pow].
  repeat rewrite <- sm2_fe_of_Z_mul.
  repeat rewrite <- sm2_fe_of_Z_add.
  rewrite sm2_fe_of_Z_eq_iff.
  replace (x * (x * x)) with (x * x * x) by ring.
  reflexivity.
Qed.

Definition ec_point_of_affine
    (x y : Z) (Hon_curve : sm2_affine_on_curve x y) : ec_point :=
  @SMain.curve_elt
    (ZEll.pK SM2_P_Z)
    (ZEll.pkI SM2_P_Z)
    (@ZEll.pkplus SM2_P_Z)
    (@ZEll.pkmul SM2_P_Z)
    (ZEll.pA SM2_A_Z SM2_P_Z)
    (ZEll.pB SM2_B_Z SM2_P_Z)
    (sm2_fe_of_Z x) (sm2_fe_of_Z y)
    (proj2 (proj2 Hon_curve)).

Definition ec_point_affine_coordinates
    (point : ec_point) (x y : Z) : Prop :=
  match point with
  | SMain.inf_elt _ _ _ _ _ => False
  | @SMain.curve_elt _ _ _ _ _ _ point_x point_y _ =>
      x = sm2_fe_value point_x /\
      y = sm2_fe_value point_y
  end.

Lemma ec_point_of_affine_coordinates :
  forall x y Hon_curve,
    ec_point_affine_coordinates
      (ec_point_of_affine x y Hon_curve) x y.
Proof.
  intros x y Hon_curve.
  unfold ec_point_affine_coordinates, ec_point_of_affine.
  cbn.
  split.
  - symmetry. apply sm2_fe_value_of_Z. exact (proj1 Hon_curve).
  - symmetry. apply sm2_fe_value_of_Z. exact (proj1 (proj2 Hon_curve)).
Qed.

Lemma ec_point_affine_coordinates_bounds :
  forall point x y,
    ec_point_affine_coordinates point x y ->
    0 <= x < SM2_P_Z /\ 0 <= y < SM2_P_Z.
Proof.
  intros point x y Hcoordinates.
  destruct point as [|point_x point_y Hcurve].
  - contradiction.
  - cbn [ec_point_affine_coordinates] in Hcoordinates.
    destruct Hcoordinates as [-> ->].
    split; apply sm2_fe_value_bounds.
Qed.

Lemma ec_point_affine_coordinates_functional :
  forall point x1 y1 x2 y2,
    ec_point_affine_coordinates point x1 y1 ->
    ec_point_affine_coordinates point x2 y2 ->
    x1 = x2 /\ y1 = y2.
Proof.
  intros point x1 y1 x2 y2 Hcoordinates1 Hcoordinates2.
  destruct point as [|point_x point_y Hcurve].
  - contradiction.
  - cbn [ec_point_affine_coordinates] in
      Hcoordinates1, Hcoordinates2.
    destruct Hcoordinates1 as [Hx1 Hy1].
    destruct Hcoordinates2 as [Hx2 Hy2].
    split; congruence.
Qed.

Lemma ec_point_affine_coordinates_on_curve :
  forall point x y,
    ec_point_affine_coordinates point x y ->
    sm2_affine_on_curve x y.
Proof.
  intros point x y Hcoordinates.
  destruct point as [|point_x point_y Hcurve].
  - contradiction.
  - cbn [ec_point_affine_coordinates] in Hcoordinates.
    destruct Hcoordinates as [-> ->].
    unfold sm2_affine_on_curve.
    split; [apply sm2_fe_value_bounds |].
    split; [apply sm2_fe_value_bounds |].
    unfold sm2_affine_equation.
    repeat rewrite sm2_fe_of_Z_value.
    exact Hcurve.
Qed.

Lemma ec_point_of_affine_complete :
  forall point x y (Hon_curve : sm2_affine_on_curve x y),
    ec_point_affine_coordinates point x y ->
    point = ec_point_of_affine x y Hon_curve.
Proof.
  intros point x y Hon_curve Hcoordinates.
  destruct point as [|point_x point_y Hcurve].
  - contradiction.
  - cbn [ec_point_affine_coordinates] in Hcoordinates.
    destruct Hcoordinates as [Hx Hy].
    unfold ec_point_of_affine.
    apply (SMain.curve_elt_irr sm2_curve_theory).
    + rewrite Hx. symmetry. apply sm2_fe_of_Z_value.
    + rewrite Hy. symmetry. apply sm2_fe_of_Z_value.
Qed.

Lemma ec_point_of_affine_proof_irrelevant :
  forall x y
         (Hcurve1 Hcurve2 : sm2_affine_on_curve x y),
    ec_point_of_affine x y Hcurve1 =
    ec_point_of_affine x y Hcurve2.
Proof.
  intros x y Hcurve1 Hcurve2.
  apply ec_point_of_affine_complete.
  apply ec_point_of_affine_coordinates.
Qed.

Lemma sm2_g_affine_equation :
  sm2_affine_equation SM2_G_X_Z SM2_G_Y_Z.
Proof.
  vm_compute.
  apply GZnZ.zirr.
  reflexivity.
Qed.

Lemma sm2_g_on_curve :
  sm2_affine_on_curve SM2_G_X_Z SM2_G_Y_Z.
Proof.
  unfold sm2_affine_on_curve.
  split; [exact sm2_g_x_bounds |].
  split; [exact sm2_g_y_bounds |].
  exact sm2_g_affine_equation.
Qed.

Definition SM2_G_POINT : ec_point :=
  ec_point_of_affine SM2_G_X_Z SM2_G_Y_Z sm2_g_on_curve.

Lemma sm2_g_not_infinity :
  SM2_G_POINT <> ECInfinity.
Proof. discriminate. Qed.

(** * Group operations *)

Definition sm2_point_add (left right : ec_point) : ec_point :=
  SMain.add sm2_curve_theory left right.

Definition sm2_point_double (point : ec_point) : ec_point :=
  sm2_point_add point point.

Definition sm2_point_negate (point : ec_point) : ec_point :=
  SMain.opp sm2_curve_theory point.

Definition sm2_group : FGroup.FGroup sm2_point_add :=
  @ZEll.pG
    SM2_P_Z SM2_A_Z SM2_B_Z
    sm2_p_not_divides_two
    sm2_curve_nonsingular
    SM2_P_Z sm2_p_prime
    (Z.divide_refl SM2_P_Z).

Lemma ec_point_in_sm2_group :
  forall point,
    List.In point sm2_group.(FGroup.s).
Proof.
  intros point.
  unfold sm2_group, ZEll.pG.
  apply SMain.FELLK_in.
Qed.

Definition sm2_point_mul (scalar : Z) (point : ec_point) : ec_point :=
  EGroup.gpow point sm2_group scalar.

Definition sm2_ec_point_dec :
  forall left right : ec_point, {left = right} + {left <> right} :=
  SMain.ceqb sm2_curve_theory.

Lemma sm2_group_identity :
  sm2_group.(FGroup.e) = ECInfinity.
Proof. reflexivity. Qed.

Lemma sm2_point_add_infinity_left :
  forall point,
    sm2_point_add ECInfinity point = point.
Proof.
  apply SMain.add_0_l.
Qed.

Lemma sm2_point_add_infinity_right :
  forall point,
    sm2_point_add point ECInfinity = point.
Proof.
  apply SMain.add_0_r.
Qed.

Lemma sm2_point_add_associative :
  forall point1 point2 point3,
    sm2_point_add point1 (sm2_point_add point2 point3) =
    sm2_point_add (sm2_point_add point1 point2) point3.
Proof.
  exact (SMain.add_assoc sm2_curve_theory).
Qed.

Lemma sm2_point_add_commutative :
  forall point1 point2,
    sm2_point_add point1 point2 = sm2_point_add point2 point1.
Proof.
  exact (SMain.add_comm sm2_curve_theory).
Qed.

Lemma sm2_point_add_cancel_left :
  forall fixed point1 point2,
    sm2_point_add fixed point1 = sm2_point_add fixed point2 ->
    point1 = point2.
Proof.
  exact (SMain.cancel sm2_curve_theory).
Qed.

Lemma sm2_point_add_negate_right :
  forall point,
    sm2_point_add point (sm2_point_negate point) = ECInfinity.
Proof.
  exact (SMain.add_opp sm2_curve_theory).
Qed.

Lemma sm2_point_negate_involutive :
  forall point,
    sm2_point_negate (sm2_point_negate point) = point.
Proof.
  exact (SMain.opp_opp sm2_curve_theory).
Qed.

Lemma sm2_point_mul_zero :
  forall point,
    sm2_point_mul 0 point = ECInfinity.
Proof.
  intros point.
  unfold sm2_point_mul.
  rewrite EGroup.gpow_0.
  reflexivity.
Qed.

Lemma sm2_point_mul_one :
  forall point,
    sm2_point_mul 1 point = point.
Proof.
  intros point.
  unfold sm2_point_mul.
  apply EGroup.gpow_1.
  apply ec_point_in_sm2_group.
Qed.

Lemma sm2_point_mul_add :
  forall point left right,
    0 <= left ->
    0 <= right ->
    sm2_point_mul (left + right) point =
    sm2_point_add
      (sm2_point_mul left point)
      (sm2_point_mul right point).
Proof.
  intros point left right Hleft Hright.
  unfold sm2_point_mul.
  apply EGroup.gpow_add.
  - apply ec_point_in_sm2_group.
  - exact Hleft.
  - exact Hright.
Qed.

Lemma sm2_point_mul_two :
  forall point,
    sm2_point_mul 2 point = sm2_point_double point.
Proof.
  intros point.
  replace 2 with (1 + 1) by lia.
  rewrite sm2_point_mul_add by lia.
  rewrite !sm2_point_mul_one.
  reflexivity.
Qed.

Lemma sm2_point_mul_three :
  forall point,
    sm2_point_mul 3 point =
    sm2_point_add (sm2_point_double point) point.
Proof.
  intros point.
  replace 3 with (2 + 1) by lia.
  rewrite sm2_point_mul_add by lia.
  rewrite sm2_point_mul_two, sm2_point_mul_one.
  reflexivity.
Qed.

Lemma sm2_point_mul_mul :
  forall point left right,
    0 <= left ->
    0 <= right ->
    sm2_point_mul (left * right) point =
    sm2_point_mul right (sm2_point_mul left point).
Proof.
  intros point left right Hleft Hright.
  unfold sm2_point_mul.
  apply EGroup.gpow_gpow.
  - apply ec_point_in_sm2_group.
  - exact Hleft.
  - exact Hright.
Qed.
