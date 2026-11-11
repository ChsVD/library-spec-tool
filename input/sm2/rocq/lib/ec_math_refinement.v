Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.setoid_ring.Ring.
From SimpleC.EE.Applications_human.sm2.lib
  Require Export ecc.
From SimpleC.EE.Applications_human.sm2.lib
  Require Import fieldOp_lib sm2_primality.

Local Open Scope Z_scope.

(** Pure refinement from the executable Jacobian doubling schedule to the
    single abstract point semantics exported by [ecc.v]. *)

Definition jpoint_double_coordinates
    (x y z result_x result_y result_z : Z) : Prop :=
  let slope := (3 * (x * x - z ^ 4)) mod SM2_P_Z in
  result_x =
    (slope * slope - 8 * x * y * y) mod SM2_P_Z /\
  result_y =
    (slope * (4 * x * y * y - result_x) - 8 * y ^ 4) mod SM2_P_Z /\
  result_z = (2 * y * z) mod SM2_P_Z.

(** The unique ordinary-domain trace shared by the direct and Montgomery
    implementations of Jacobian doubling.  Operand order follows the
    Montgomery C schedule; the refinement proof below discharges the two
    commutativity differences from the direct schedule. *)
Definition jdouble_trace_s2 (y : Z) : Z :=
  (2 * y) mod SM2_P_Z.
Definition jdouble_trace_z2 (z : Z) : Z :=
  (z * z) mod SM2_P_Z.
Definition jdouble_trace_m4 (y : Z) : Z :=
  (jdouble_trace_s2 y * jdouble_trace_s2 y) mod SM2_P_Z.
Definition jdouble_trace_t16 (y : Z) : Z :=
  (jdouble_trace_m4 y * jdouble_trace_m4 y) mod SM2_P_Z.
Definition jdouble_trace_s4 (x y : Z) : Z :=
  (jdouble_trace_m4 y * x) mod SM2_P_Z.
Definition jdouble_trace_t8 (y : Z) : Z :=
  fp_div2 (jdouble_trace_t16 y).
Definition jdouble_trace_sum (x z : Z) : Z :=
  (x + jdouble_trace_z2 z) mod SM2_P_Z.
Definition jdouble_trace_diff (x z : Z) : Z :=
  (x - jdouble_trace_z2 z) mod SM2_P_Z.
Definition jdouble_trace_prod (x z : Z) : Z :=
  (jdouble_trace_diff x z * jdouble_trace_sum x z) mod SM2_P_Z.
Definition jdouble_trace_slope (x z : Z) : Z :=
  (3 * jdouble_trace_prod x z) mod SM2_P_Z.
Definition jdouble_trace_slope_sq (x z : Z) : Z :=
  (jdouble_trace_slope x z * jdouble_trace_slope x z) mod SM2_P_Z.
Definition jdouble_trace_u8 (x y : Z) : Z :=
  (2 * jdouble_trace_s4 x y) mod SM2_P_Z.
Definition jdouble_trace_rx (x y z : Z) : Z :=
  (jdouble_trace_slope_sq x z - jdouble_trace_u8 x y) mod SM2_P_Z.
Definition jdouble_trace_tmp (x y z : Z) : Z :=
  (jdouble_trace_s4 x y - jdouble_trace_rx x y z) mod SM2_P_Z.
Definition jdouble_trace_tmp2 (x y z : Z) : Z :=
  (jdouble_trace_slope x z * jdouble_trace_tmp x y z) mod SM2_P_Z.
Definition jdouble_trace_ry (x y z : Z) : Z :=
  (jdouble_trace_tmp2 x y z - jdouble_trace_t8 y) mod SM2_P_Z.

Lemma canonical_infinity_represents_ECInfinity :
  jpoint_represents 1 1 0 ECInfinity.
Proof.
  cbn [jpoint_represents jpoint_infinity].
  pose proof sm2_p_gt_one.
  repeat split; lia.
Qed.

Lemma canonical_infinity_representation :
  jpoint_represents 1 1 0 ECInfinity /\
  jpoint_canonical_infinity_encoding 1 1 0 ECInfinity.
Proof.
  split.
  - apply canonical_infinity_represents_ECInfinity.
  - unfold jpoint_canonical_infinity_encoding, canonical_jpoint_infinity.
    intros _.
    repeat split; reflexivity.
Qed.

Lemma jpoint_represents_z0_only_infinity :
  forall x y point,
    jpoint_represents x y 0 point ->
    point = ECInfinity.
Proof.
  intros x y point Hrep.
  apply (proj1 (jpoint_represents_infinity_iff x y 0 point Hrep)).
  reflexivity.
Qed.

Lemma sm2_point_double_infinity :
  sm2_point_double ECInfinity = ECInfinity.
Proof.
  unfold sm2_point_double.
  apply sm2_point_add_infinity_left.
Qed.

(** Divisibility-form congruence used only by the coordinate algebra below. *)

Definition congr_mod (p a b : Z) : Prop := Z.divide p (a - b).

Lemma congr_mod_refl : forall p a, congr_mod p a a.
Proof. intros; exists 0; ring. Qed.

Lemma congr_mod_sym : forall p a b,
  congr_mod p a b -> congr_mod p b a.
Proof. intros p a b [k H]; exists (-k); lia. Qed.

Lemma congr_mod_trans : forall p a b c,
  congr_mod p a b -> congr_mod p b c -> congr_mod p a c.
Proof. intros p a b c [k Hk] [l Hl]; exists (k + l); lia. Qed.

Lemma congr_mod_add : forall p a b c d,
  congr_mod p a b -> congr_mod p c d -> congr_mod p (a + c) (b + d).
Proof. intros p a b c d [k Hk] [l Hl]; exists (k + l); lia. Qed.

Lemma congr_mod_sub : forall p a b c d,
  congr_mod p a b -> congr_mod p c d -> congr_mod p (a - c) (b - d).
Proof. intros p a b c d [k Hk] [l Hl]; exists (k - l); lia. Qed.

Lemma congr_mod_mul : forall p a b c d,
  congr_mod p a b -> congr_mod p c d -> congr_mod p (a * c) (b * d).
Proof.
  intros p a b c d [k Hk] [l Hl].
  exists (k * c + b * l).
  nia.
Qed.

Lemma congr_mod_pow2 : forall p a b,
  congr_mod p a b -> congr_mod p (a ^ 2) (b ^ 2).
Proof.
  intros p a b Hab.
  replace (a ^ 2) with (a * a) by ring.
  replace (b ^ 2) with (b * b) by ring.
  apply congr_mod_mul; assumption.
Qed.

Lemma congr_mod_pow3 : forall p a b,
  congr_mod p a b -> congr_mod p (a ^ 3) (b ^ 3).
Proof.
  intros p a b Hab.
  replace (a ^ 3) with ((a ^ 2) * a) by ring.
  replace (b ^ 3) with ((b ^ 2) * b) by ring.
  apply congr_mod_mul; [apply congr_mod_pow2 |]; assumption.
Qed.

Lemma congr_mod_pow4 : forall p a b,
  congr_mod p a b -> congr_mod p (a ^ 4) (b ^ 4).
Proof.
  intros p a b Hab.
  replace (a ^ 4) with ((a ^ 2) * (a ^ 2)) by ring.
  replace (b ^ 4) with ((b ^ 2) * (b ^ 2)) by ring.
  apply congr_mod_mul; apply congr_mod_pow2; assumption.
Qed.

Lemma congr_mod_pow6 : forall p a b,
  congr_mod p a b -> congr_mod p (a ^ 6) (b ^ 6).
Proof.
  intros p a b Hab.
  replace (a ^ 6) with ((a ^ 3) * (a ^ 3)) by ring.
  replace (b ^ 6) with ((b ^ 3) * (b ^ 3)) by ring.
  apply congr_mod_mul; apply congr_mod_pow3; assumption.
Qed.

Lemma congr_mod_scale : forall p k a b,
  congr_mod p a b -> congr_mod p (k * a) (k * b).
Proof.
  intros p k a b Hab.
  apply congr_mod_mul; [apply congr_mod_refl | exact Hab].
Qed.

Lemma congr_mod_mod : forall p a,
  p <> 0 -> congr_mod p (a mod p) a.
Proof.
  intros p a Hp.
  unfold congr_mod.
  exists (-(a / p)).
  rewrite Z.mod_eq by exact Hp.
  ring.
Qed.

Lemma congr_mod_of_mod_eq : forall p a b,
  p <> 0 -> a mod p = b mod p -> congr_mod p a b.
Proof.
  intros p a b Hp Hmod.
  eapply congr_mod_trans.
  - apply congr_mod_sym, congr_mod_mod; exact Hp.
  - rewrite Hmod. apply congr_mod_mod; exact Hp.
Qed.

Lemma congr_mod_to_mod_eq : forall p a b,
  p <> 0 -> congr_mod p a b -> a mod p = b mod p.
Proof.
  intros p a b Hp [k Hk].
  replace a with (b + k * p) by lia.
  apply Z.mod_add; exact Hp.
Qed.

Lemma congr_mod_eq_canonical : forall p a b,
  0 < p ->
  0 <= a < p ->
  0 <= b < p ->
  congr_mod p a b ->
  a = b.
Proof.
  intros p a b Hp Ha Hb Hcongr.
  pose proof (congr_mod_to_mod_eq p a b ltac:(lia) Hcongr) as Hmod.
  rewrite Z.mod_small in Hmod by exact Ha.
  rewrite Z.mod_small in Hmod by exact Hb.
  exact Hmod.
Qed.

(** Every nonzero canonical field element has a canonical multiplicative
    inverse.  This is the field bridge needed to interpret finite Jacobian
    coordinates as affine mathematical points; it is independent of the C
    inversion routines. *)

Lemma sm2_nonzero_inverse_exists :
  forall a,
    0 <= a < SM2_P_Z ->
    a <> 0 ->
    exists inverse,
      0 <= inverse < SM2_P_Z /\
      congr_mod SM2_P_Z (a * inverse) 1.
Proof.
  intros a Ha Ha0.
  destruct (sm2_mod_inverse_exists a) as [inverse [Hinverse_range Hinverse]].
  - rewrite Z.mod_small by exact Ha.
    exact Ha0.
  - exists inverse.
    split; [exact Hinverse_range|].
    apply congr_mod_of_mod_eq.
    + pose proof sm2_p_gt_one. lia.
    + rewrite Hinverse.
      symmetry.
      apply Z.mod_small.
      pose proof sm2_p_gt_one. lia.
Qed.

Lemma sm2_congr_mod_cancel_nonzero_right :
  forall a b c,
    0 <= c < SM2_P_Z ->
    c <> 0 ->
    congr_mod SM2_P_Z (a * c) (b * c) ->
    congr_mod SM2_P_Z a b.
Proof.
  intros a b c Hc Hc0 Habc.
  destruct (sm2_nonzero_inverse_exists c Hc Hc0)
    as [cinv [_ Hcinv]].
  pose proof (congr_mod_mul SM2_P_Z (a * c) (b * c)
      cinv cinv Habc (congr_mod_refl SM2_P_Z cinv)) as Hscaled.
  assert (Ha : congr_mod SM2_P_Z (a * (c * cinv)) a).
  { replace a with (a * 1) at 2 by ring.
    apply congr_mod_mul; [apply congr_mod_refl | exact Hcinv]. }
  assert (Hb : congr_mod SM2_P_Z (b * (c * cinv)) b).
  { replace b with (b * 1) at 2 by ring.
    apply congr_mod_mul; [apply congr_mod_refl | exact Hcinv]. }
  replace ((a * c) * cinv) with (a * (c * cinv)) in Hscaled by ring.
  replace ((b * c) * cinv) with (b * (c * cinv)) in Hscaled by ring.
  eapply congr_mod_trans.
  - apply congr_mod_sym; exact Ha.
  - eapply congr_mod_trans; [exact Hscaled | exact Hb].
Qed.

Lemma sm2_congruence_division_exists :
  forall denominator numerator,
    ~ congr_mod SM2_P_Z denominator 0 ->
    exists quotient,
      0 <= quotient < SM2_P_Z /\
      congr_mod SM2_P_Z (denominator * quotient) numerator.
Proof.
  intros denominator numerator Hnonzero.
  assert (Hp : SM2_P_Z <> 0)
    by (pose proof sm2_p_montgomery_bounds; lia).
  set (d := denominator mod SM2_P_Z).
  assert (Hd_range : 0 <= d < SM2_P_Z).
  { unfold d. apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds; lia. }
  assert (Hd0 : d <> 0).
  { intro Hd0; apply Hnonzero.
    apply congr_mod_of_mod_eq; [exact Hp|].
    unfold d in Hd0.
    rewrite Hd0, Z.mod_0_l by exact Hp.
    reflexivity. }
  destruct (sm2_nonzero_inverse_exists d Hd_range Hd0)
    as [dinv [Hdinv_range Hdinv]].
  exists ((numerator * dinv) mod SM2_P_Z).
  split.
  - apply Z.mod_pos_bound.
    pose proof sm2_p_montgomery_bounds; lia.
  - assert (Hden : congr_mod SM2_P_Z denominator d).
    { unfold d. apply congr_mod_sym, congr_mod_mod; exact Hp. }
    assert (Hquot : congr_mod SM2_P_Z
        ((numerator * dinv) mod SM2_P_Z) (numerator * dinv)).
    { apply congr_mod_mod; exact Hp. }
    assert (Hproduct := congr_mod_mul SM2_P_Z
      denominator d
      ((numerator * dinv) mod SM2_P_Z) (numerator * dinv)
      Hden Hquot).
    eapply congr_mod_trans; [exact Hproduct|].
    replace (d * (numerator * dinv)) with
      (numerator * (d * dinv)) by ring.
    replace numerator with (numerator * 1) at 2 by ring.
    apply congr_mod_scale.
    exact Hdinv.
Qed.

(** Canonicalize any affine-coordinate pair satisfying the SM2 curve equation
    modulo [p]. *)

Lemma sm2_canonicalize_curve_point :
  forall raw_x raw_y,
    congr_mod SM2_P_Z (raw_y * raw_y)
      (raw_x * raw_x * raw_x + SM2_A_Z * raw_x + SM2_B_Z) ->
    sm2_affine_on_curve
      (raw_x mod SM2_P_Z) (raw_y mod SM2_P_Z).
Proof.
  intros raw_x raw_y Hcurve.
  unfold sm2_affine_on_curve.
  change
    (0 <= raw_x mod SM2_P_Z < SM2_P_Z /\
     0 <= raw_y mod SM2_P_Z < SM2_P_Z /\
     sm2_affine_equation
       (raw_x mod SM2_P_Z) (raw_y mod SM2_P_Z)).
  assert (Hp : SM2_P_Z <> 0) by (pose proof sm2_p_gt_one; lia).
  split.
  - apply Z.mod_pos_bound. pose proof sm2_p_gt_one; lia.
  - split.
    + apply Z.mod_pos_bound. pose proof sm2_p_gt_one; lia.
    + apply sm2_affine_equation_iff.
      apply congr_mod_to_mod_eq; [exact Hp|].
      assert (Hx : congr_mod SM2_P_Z (raw_x mod SM2_P_Z) raw_x)
        by (apply congr_mod_mod; exact Hp).
      assert (Hy : congr_mod SM2_P_Z (raw_y mod SM2_P_Z) raw_y)
        by (apply congr_mod_mod; exact Hp).
      eapply congr_mod_trans.
      * apply congr_mod_mul; exact Hy.
      * eapply congr_mod_trans; [exact Hcurve|].
        apply congr_mod_sym.
        apply congr_mod_add.
        -- apply congr_mod_add.
           ++ apply congr_mod_mul.
              ** apply congr_mod_mul; exact Hx.
              ** exact Hx.
           ++ apply congr_mod_mul; [apply congr_mod_refl|exact Hx].
        -- apply congr_mod_refl.
Qed.

Lemma sm2_canonical_product_mod_nonzero :
  forall a b,
    0 <= a < SM2_P_Z -> a <> 0 ->
    0 <= b < SM2_P_Z -> b <> 0 ->
    (a * b) mod SM2_P_Z <> 0.
Proof.
  intros a b Ha Ha0 Hb Hb0 Hab0.
  destruct (sm2_nonzero_inverse_exists a Ha Ha0)
    as [ainv [Hainv_range Hainv]].
  assert (Hp : SM2_P_Z <> 0)
    by (pose proof sm2_p_montgomery_bounds; lia).
  assert (Hab : congr_mod SM2_P_Z (a * b) 0).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Hab0, Z.mod_0_l by exact Hp; reflexivity. }
  assert (Hscaled := congr_mod_scale SM2_P_Z ainv _ _ Hab).
  assert (Hcancel : congr_mod SM2_P_Z (ainv * (a * b)) b).
  { replace (ainv * (a * b)) with ((a * ainv) * b) by ring.
    replace b with (1 * b) at 2 by ring.
    apply congr_mod_mul.
    - exact Hainv.
    - apply congr_mod_refl. }
  assert (Hbcongr : congr_mod SM2_P_Z b 0).
  { apply congr_mod_sym in Hcancel.
    eapply congr_mod_trans; [exact Hcancel|].
    replace (ainv * 0) with 0 in Hscaled by ring.
    exact Hscaled. }
  assert (b = 0).
  { apply (congr_mod_eq_canonical SM2_P_Z b 0).
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact Hb.
    - pose proof sm2_p_montgomery_bounds; lia.
    - exact Hbcongr. }
  contradiction.
Qed.

Lemma sm2_double_y_z4_mod_nonzero :
  forall y z,
    0 <= y < SM2_P_Z -> y <> 0 ->
    0 <= z < SM2_P_Z -> z <> 0 ->
    (2 * y * z ^ 4) mod SM2_P_Z <> 0.
Proof.
  intros y z Hy Hy0 Hz Hz0.
  assert (H2 : 0 <= 2 < SM2_P_Z)
    by (cbv [SM2_P_Z]; lia).
  assert (Hrp2 : rel_prime 2 SM2_P_Z).
  { apply Zgcd_1_rel_prime.
    now apply sm2_p_nonzero_gcd_one. }
  assert (Hrpy : rel_prime y SM2_P_Z).
  { apply Zgcd_1_rel_prime.
    now apply sm2_p_nonzero_gcd_one. }
  assert (Hrpz : rel_prime z SM2_P_Z).
  { apply Zgcd_1_rel_prime.
    now apply sm2_p_nonzero_gcd_one. }
  assert (Hprod : rel_prime (2 * y * z ^ 4) SM2_P_Z).
  { apply rel_prime_sym.
    replace (2 * y * z ^ 4) with ((((2 * y) * z) * z) * z * z)
      by ring.
    repeat apply rel_prime_mult.
    - apply rel_prime_sym; exact Hrp2.
    - apply rel_prime_sym; exact Hrpy.
    - apply rel_prime_sym; exact Hrpz.
    - apply rel_prime_sym; exact Hrpz.
    - apply rel_prime_sym; exact Hrpz.
    - apply rel_prime_sym; exact Hrpz. }
  apply Zrel_prime_neq_mod_0.
  - pose proof sm2_p_montgomery_bounds; lia.
  - exact Hprod.
Qed.

Lemma mont_p_add : forall x y,
  Zmod (mont_p x + mont_p y) SM2_P_Z = mont_p (x + y).
Proof.
  intros x y.
  symmetry.
  unfold mont_p, Zmod.
  apply Montgomery.mont_add.
  pose proof sm2_p_montgomery_bounds.
  lia.
Qed.

Lemma mont_p_mod : forall x,
  mont_p (Zmod x SM2_P_Z) = mont_p x.
Proof.
  intros x.
  unfold mont_p, Montgomery.mont.
  rewrite Z.mul_mod_idemp_l by
    (pose proof sm2_p_montgomery_bounds; lia).
  reflexivity.
Qed.

Lemma mont_p_sub : forall x y,
  Zmod (mont_p x - mont_p y) SM2_P_Z = mont_p (x - y).
Proof.
  intros x y.
  symmetry.
  unfold mont_p, Zmod.
  apply Montgomery.mont_sub.
  pose proof sm2_p_montgomery_bounds.
  lia.
Qed.

Lemma mont_p_double : forall x,
  Zmod (2 * mont_p x) SM2_P_Z = mont_p (2 * x).
Proof.
  intros x.
  replace (2 * mont_p x) with (mont_p x + mont_p x) by ring.
  rewrite mont_p_add.
  f_equal; ring.
Qed.

Lemma mont_p_triple : forall x,
  Zmod (3 * mont_p x) SM2_P_Z = mont_p (3 * x).
Proof.
  intros x.
  replace (3 * x) with (2 * x + x) by ring.
  rewrite <- mont_p_add.
  rewrite <- mont_p_double.
  replace (3 * mont_p x) with (2 * mont_p x + mont_p x) by ring.
  rewrite <- Z.add_mod_idemp_l by
    (pose proof sm2_p_montgomery_bounds; lia).
  reflexivity.
Qed.

Lemma sm2_congr_mod_cancel_two : forall a b,
  congr_mod SM2_P_Z (2 * a) (2 * b) ->
  congr_mod SM2_P_Z a b.
Proof.
  intros a b H.
  unfold congr_mod in H |- *.
  destruct H as [q Hq].
  exists (SM2_P_INV2_Z * q - (a - b)).
  assert (Hinv : 2 * SM2_P_INV2_Z = SM2_P_Z + 1)
    by (vm_compute; reflexivity).
  lia.
Qed.

Lemma fp_div2_congr_half : forall x k,
  congr_mod SM2_P_Z x (2 * k) ->
  congr_mod SM2_P_Z (fp_div2 x) k.
Proof.
  intros x k Hx.
  apply sm2_congr_mod_cancel_two.
  eapply congr_mod_trans; [|exact Hx].
  rewrite <- fp_div2_adjusted_twice.
  unfold fp_div2_adjusted, congr_mod.
  destruct (Z.even x).
  - exists 0. lia.
  - exists 1. lia.
Qed.

Lemma fp_div2_mont : forall x,
  fp_div2 (mont_p x) = mont_p (fp_div2 x).
Proof.
  intros x.
  assert (Hp : SM2_P_Z <> 0) by
    (pose proof sm2_p_montgomery_bounds; lia).
  assert (Hxhalf : congr_mod SM2_P_Z x (2 * fp_div2 x)).
  {
    rewrite <- fp_div2_adjusted_twice.
    unfold fp_div2_adjusted, congr_mod.
    destruct (Z.even x).
    - exists 0; lia.
    - exists (-1); lia.
  }
  assert (Hmx : congr_mod SM2_P_Z (mont_p x) (x * U256_MOD)).
  {
    unfold mont_p, Montgomery.mont.
    apply congr_mod_mod; exact Hp.
  }
  assert (Hmf : congr_mod SM2_P_Z
      (mont_p (fp_div2 x)) (fp_div2 x * U256_MOD)).
  {
    unfold mont_p, Montgomery.mont.
    apply congr_mod_mod; exact Hp.
  }
  assert (Hscaled : congr_mod SM2_P_Z
      (x * U256_MOD) (2 * (fp_div2 x * U256_MOD))).
  {
    eapply congr_mod_trans.
    - apply congr_mod_mul; [exact Hxhalf|apply congr_mod_refl].
    - replace ((2 * fp_div2 x) * U256_MOD)
        with (2 * (fp_div2 x * U256_MOD)) by ring.
      apply congr_mod_refl.
  }
  assert (Hinput : congr_mod SM2_P_Z
      (mont_p x) (2 * mont_p (fp_div2 x))).
  {
    eapply congr_mod_trans; [exact Hmx|].
    eapply congr_mod_trans; [exact Hscaled|].
    apply congr_mod_mul; [apply congr_mod_refl|].
    apply congr_mod_sym; exact Hmf.
  }
  apply congr_mod_eq_canonical with (p := SM2_P_Z).
  - pose proof sm2_p_montgomery_bounds; lia.
  - apply fp_div2_bounds, mont_p_range.
  - apply mont_p_range.
  - apply fp_div2_congr_half; exact Hinput.
Qed.

Lemma zpow4_mul : forall a : Z, a ^ 4 = a * a * a * a.
Proof.
  intros a. replace 4 with (2 + 2) by lia.
  rewrite Z.pow_add_r by lia.
  rewrite !Z.pow_2_r. ring.
Qed.

Lemma jpoint_double_trace_coordinates :
  forall x y z s2 z2 m4 rz t16 s4 t8 sum diff slope u8 rx tmp tmp2 ry,
    s2 = (2 * y) mod SM2_P_Z ->
    z2 = (z * z) mod SM2_P_Z ->
    m4 = (s2 * s2) mod SM2_P_Z ->
    rz = (s2 * z) mod SM2_P_Z ->
    t16 = (m4 * m4) mod SM2_P_Z ->
    s4 = (m4 * x) mod SM2_P_Z ->
    t8 = fp_div2 t16 ->
    sum = (z2 + x) mod SM2_P_Z ->
    diff = (x - z2) mod SM2_P_Z ->
    slope = (3 * ((sum * diff) mod SM2_P_Z)) mod SM2_P_Z ->
    u8 = (2 * s4) mod SM2_P_Z ->
    rx = (((slope * slope) mod SM2_P_Z) - u8) mod SM2_P_Z ->
    tmp = (s4 - rx) mod SM2_P_Z ->
    tmp2 = (tmp * slope) mod SM2_P_Z ->
    ry = (tmp2 - t8) mod SM2_P_Z ->
    jpoint_double_coordinates x y z rx ry rz.
Proof.
  intros x y z s2 z2 m4 rz t16 s4 t8 sum diff slope u8
    rx tmp tmp2 ry Hs2 Hz2 Hm4 Hrz Ht16 Hs4 Ht8 Hsum Hdiff
    Hslope Hu8 Hrx Htmp Htmp2 Hry.
  assert (Hp : SM2_P_Z <> 0) by (vm_compute; discriminate).
  assert (Cs2 : congr_mod SM2_P_Z s2 (2 * y)).
  { rewrite Hs2. apply congr_mod_mod; exact Hp. }
  assert (Cz2 : congr_mod SM2_P_Z z2 (z * z)).
  { rewrite Hz2. apply congr_mod_mod; exact Hp. }
  assert (Cm4 : congr_mod SM2_P_Z m4 (4 * y * y)).
  {
    eapply congr_mod_trans.
    - rewrite Hm4. apply congr_mod_mod; exact Hp.
    - eapply congr_mod_trans.
      + apply congr_mod_mul; exact Cs2.
      + replace (2 * y * (2 * y)) with (4 * y * y) by ring.
        apply congr_mod_refl.
  }
  assert (Ct16 : congr_mod SM2_P_Z t16 (16 * y ^ 4)).
  {
    eapply congr_mod_trans.
    - rewrite Ht16. apply congr_mod_mod; exact Hp.
    - eapply congr_mod_trans.
      + apply congr_mod_mul; exact Cm4.
      + replace ((4 * y * y) * (4 * y * y)) with (16 * y ^ 4).
        2:{ rewrite zpow4_mul. ring. }
        apply congr_mod_refl.
  }
  assert (Ct8 : congr_mod SM2_P_Z t8 (8 * y ^ 4)).
  {
    rewrite Ht8.
    apply fp_div2_congr_half.
    eapply congr_mod_trans; [exact Ct16|].
    replace (2 * (8 * y ^ 4)) with (16 * y ^ 4) by ring.
    apply congr_mod_refl.
  }
  assert (Cs4 : congr_mod SM2_P_Z s4 (4 * x * y * y)).
  {
    eapply congr_mod_trans.
    - rewrite Hs4. apply congr_mod_mod; exact Hp.
    - eapply congr_mod_trans.
      + apply congr_mod_mul; [exact Cm4|apply congr_mod_refl].
      + replace (4 * y * y * x) with (4 * x * y * y) by ring.
        apply congr_mod_refl.
  }
  assert (Csum : congr_mod SM2_P_Z sum (z * z + x)).
  {
    eapply congr_mod_trans.
    - rewrite Hsum. apply congr_mod_mod; exact Hp.
    - apply congr_mod_add; [exact Cz2|apply congr_mod_refl].
  }
  assert (Cdiff : congr_mod SM2_P_Z diff (x - z * z)).
  {
    eapply congr_mod_trans.
    - rewrite Hdiff. apply congr_mod_mod; exact Hp.
    - apply congr_mod_sub; [apply congr_mod_refl|exact Cz2].
  }
  assert (Cslope : congr_mod SM2_P_Z slope
      (3 * (x * x - z ^ 4))).
  {
    eapply congr_mod_trans.
    - rewrite Hslope. apply congr_mod_mod; exact Hp.
    - apply congr_mod_mul; [apply congr_mod_refl|].
      eapply congr_mod_trans.
      + apply congr_mod_mod; exact Hp.
      + eapply congr_mod_trans.
        * apply congr_mod_mul; [exact Csum|exact Cdiff].
        * replace ((z * z + x) * (x - z * z)) with (x * x - z ^ 4).
          2:{ rewrite zpow4_mul. ring. }
          apply congr_mod_refl.
  }
  assert (Cu8 : congr_mod SM2_P_Z u8 (8 * x * y * y)).
  {
    eapply congr_mod_trans.
    - rewrite Hu8. apply congr_mod_mod; exact Hp.
    - eapply congr_mod_trans.
      + apply congr_mod_mul; [apply congr_mod_refl|exact Cs4].
      + replace (2 * (4 * x * y * y)) with (8 * x * y * y) by ring.
        apply congr_mod_refl.
  }
  assert (Crx : congr_mod SM2_P_Z rx
      (3 * (x * x - z ^ 4) * (3 * (x * x - z ^ 4)) -
       8 * x * y * y)).
  {
    eapply congr_mod_trans.
    - rewrite Hrx. apply congr_mod_mod; exact Hp.
    - apply congr_mod_sub.
      + eapply congr_mod_trans.
        * apply congr_mod_mod; exact Hp.
        * apply congr_mod_mul; exact Cslope.
      + exact Cu8.
  }
  assert (Ctmp : congr_mod SM2_P_Z tmp (4 * x * y * y - rx)).
  {
    eapply congr_mod_trans.
    - rewrite Htmp. apply congr_mod_mod; exact Hp.
    - apply congr_mod_sub; [exact Cs4|apply congr_mod_refl].
  }
  assert (Ctmp2 : congr_mod SM2_P_Z tmp2
      (3 * (x * x - z ^ 4) * (4 * x * y * y - rx))).
  {
    eapply congr_mod_trans.
    - rewrite Htmp2. apply congr_mod_mod; exact Hp.
    - eapply congr_mod_trans.
      + apply congr_mod_mul; [exact Ctmp|exact Cslope].
      + replace ((4 * x * y * y - rx) * (3 * (x * x - z ^ 4)))
          with (3 * (x * x - z ^ 4) * (4 * x * y * y - rx)) by ring.
        apply congr_mod_refl.
  }
  assert (Cm : congr_mod SM2_P_Z
      ((3 * (x * x - z ^ 4)) mod SM2_P_Z)
      (3 * (x * x - z ^ 4))).
  { apply congr_mod_mod; exact Hp. }
  assert (Cslope_m : congr_mod SM2_P_Z slope
      ((3 * (x * x - z ^ 4)) mod SM2_P_Z)).
  { eapply congr_mod_trans; [exact Cslope|apply congr_mod_sym; exact Cm]. }
  unfold jpoint_double_coordinates.
  set (m := (3 * (x * x - z ^ 4)) mod SM2_P_Z).
  split.
  - rewrite Hrx.
    apply congr_mod_to_mod_eq; [exact Hp|].
    apply congr_mod_sub.
    + eapply congr_mod_trans.
      * apply congr_mod_mod; exact Hp.
      * apply congr_mod_mul; exact Cslope_m.
    + exact Cu8.
  - split.
    + rewrite Hry.
      apply congr_mod_to_mod_eq; [exact Hp|].
      apply congr_mod_sub; [|exact Ct8].
      eapply congr_mod_trans; [exact Ctmp2|].
      apply congr_mod_mul.
      * apply congr_mod_sym. exact Cm.
      * apply congr_mod_refl.
    + rewrite Hrz.
      apply congr_mod_to_mod_eq; [exact Hp|].
      apply congr_mod_mul; [exact Cs2|apply congr_mod_refl].
Qed.

Lemma jdouble_trace_coordinates :
  forall x y z,
    jpoint_double_coordinates x y z
      (jdouble_trace_rx x y z)
      (jdouble_trace_ry x y z)
      ((jdouble_trace_s2 y * z) mod SM2_P_Z).
Proof.
  intros x y z.
  eapply jpoint_double_trace_coordinates with
    (s2 := jdouble_trace_s2 y)
    (z2 := jdouble_trace_z2 z)
    (m4 := jdouble_trace_m4 y)
    (t16 := jdouble_trace_t16 y)
    (s4 := jdouble_trace_s4 x y)
    (t8 := jdouble_trace_t8 y)
    (sum := jdouble_trace_sum x z)
    (diff := jdouble_trace_diff x z)
    (slope := jdouble_trace_slope x z)
    (u8 := jdouble_trace_u8 x y)
    (tmp := jdouble_trace_tmp x y z)
    (tmp2 := jdouble_trace_tmp2 x y z);
    unfold jdouble_trace_s2, jdouble_trace_z2, jdouble_trace_m4,
      jdouble_trace_t16, jdouble_trace_s4, jdouble_trace_t8,
      jdouble_trace_sum, jdouble_trace_diff, jdouble_trace_prod,
      jdouble_trace_slope, jdouble_trace_slope_sq, jdouble_trace_u8,
      jdouble_trace_rx, jdouble_trace_tmp, jdouble_trace_tmp2,
      jdouble_trace_ry;
    try reflexivity.
  - unfold jdouble_trace_z2. f_equal; ring.
  - unfold jdouble_trace_prod, jdouble_trace_sum, jdouble_trace_diff.
    f_equal. f_equal. f_equal. apply Z.mul_comm.
  - unfold jdouble_trace_tmp2, jdouble_trace_slope, jdouble_trace_tmp.
    f_equal. apply Z.mul_comm.
Qed.


Lemma ec_double_denominator_nonzero :
  forall px py,
    sm2_affine_on_curve px py ->
    py <> 0 ->
    ~ congr_mod SM2_P_Z (2 * py) 0.
Proof.
  intros px py Hvalid Hpy Htwo.
  change (congr_mod SM2_P_Z (2 * py) 0) in Htwo.
  replace 0 with (2 * 0) in Htwo by ring.
  pose proof (sm2_congr_mod_cancel_two py 0 Htwo) as Hzero.
  destruct Hvalid as [_ [Hpy_range _]].
  assert (py = 0).
  { eapply congr_mod_eq_canonical; [|exact Hpy_range| |exact Hzero].
    - exact (proj1 (proj1 sm2_p_montgomery_bounds)).
    - split.
      + lia.
      + exact (proj1 (proj1 sm2_p_montgomery_bounds)). }
  contradiction.
Qed.

Lemma ec_tangent_slope_exists :
  forall px py,
    sm2_affine_on_curve px py ->
    py <> 0 ->
    exists lambda,
      0 <= lambda < SM2_P_Z /\
      congr_mod SM2_P_Z ((2 * py) * lambda) (3 * px * px + SM2_A_Z).
Proof.
  intros px py Hvalid Hpy.
  pose proof (ec_double_denominator_nonzero px py Hvalid Hpy) as Hnonzero.
  change (~ congr_mod SM2_P_Z (2 * py) 0) in Hnonzero.
  destruct (sm2_congruence_division_exists
      (2 * py) (3 * px * px + SM2_A_Z) Hnonzero)
    as [lambda [Hlambda Hslope]].
  exists lambda; split; [exact Hlambda|].
  exact Hslope.
Qed.

Lemma ec_tangent_curve_identity :
  forall (A B x y lambda : Z),
    (lambda * (x - (lambda * lambda - 2 * x)) - y) *
      (lambda * (x - (lambda * lambda - 2 * x)) - y) -
      ((lambda * lambda - 2 * x) * (lambda * lambda - 2 * x) *
       (lambda * lambda - 2 * x) + A * (lambda * lambda - 2 * x) + B) =
    (y * y - (x * x * x + A * x + B)) -
    (x - (lambda * lambda - 2 * x)) *
      ((2 * y) * lambda - (3 * x * x + A)).
Proof. intros A B x y lambda; ring. Qed.

Lemma ec_combine_congruence_witness :
  forall kc ks d p,
    kc * p - d * (ks * p) = (kc - d * ks) * p.
Proof. intros; ring. Qed.

Lemma ec_tangent_raw_preserves_curve_generic :
  forall p A B x y lambda,
    congr_mod p (y * y) (x * x * x + A * x + B) ->
    congr_mod p ((2 * y) * lambda) (3 * x * x + A) ->
    let x3 := lambda * lambda - 2 * x in
    let y3 := lambda * (x - x3) - y in
    congr_mod p (y3 * y3) (x3 * x3 * x3 + A * x3 + B).
Proof.
  intros p A B x y lambda Hcurve Hslope.
  unfold congr_mod in Hcurve, Hslope |- *.
  destruct Hcurve as [kc Hcurve].
  destruct Hslope as [ks Hslope].
  cbn beta zeta.
  exists (kc - (x - (lambda * lambda - 2 * x)) * ks).
  rewrite ec_tangent_curve_identity.
  rewrite Hcurve, Hslope.
  apply ec_combine_congruence_witness.
Qed.

Local Opaque SM2_P_Z SM2_A_Z SM2_B_Z.

Lemma ec_tangent_raw_preserves_curve :
  forall x y lambda,
    sm2_affine_on_curve x y ->
    congr_mod SM2_P_Z ((2 * y) * lambda) (3 * x * x + SM2_A_Z) ->
    let x3 := lambda * lambda - 2 * x in
    let y3 := lambda * (x - x3) - y in
    congr_mod SM2_P_Z (y3 * y3)
      (x3 * x3 * x3 + SM2_A_Z * x3 + SM2_B_Z).
Proof.
  intros x y lambda Hcurve Hslope.
  unfold sm2_affine_on_curve in Hcurve.
  destruct Hcurve as [_ [_ Hcurve]].
  apply sm2_affine_equation_iff in Hcurve.
  apply congr_mod_of_mod_eq in Hcurve.
  2: pose proof sm2_p_montgomery_bounds; lia.
  change (congr_mod SM2_P_Z ((2 * y) * lambda)
    (3 * x * x + SM2_A_Z)) in Hslope.
  now apply ec_tangent_raw_preserves_curve_generic.
Qed.

(** Coqprime's tangent branch agrees with the canonical integer doubling
    formula.  All unfolding of [SMain.add] for finite doubling is confined
    to this lemma. *)
Lemma sm2_point_double_affine :
  forall px py lambda qx qy
         (Hcurve : sm2_affine_on_curve px py)
         (Hqcurve : sm2_affine_on_curve qx qy),
    py <> 0 ->
    eqm SM2_P_Z ((2 * py) * lambda)
      (3 * px * px + SM2_A_Z) ->
    qx = (lambda * lambda - 2 * px) mod SM2_P_Z ->
    qy = (lambda * (px - qx) - py) mod SM2_P_Z ->
    sm2_point_double (ec_point_of_affine px py Hcurve) =
      ec_point_of_affine qx qy Hqcurve.
Proof.
  intros px py lambda qx qy Hcurve Hqcurve
    Hpy Hslope Hqx Hqy.
  assert (Hdenominator : (2 * py) mod SM2_P_Z <> 0).
  {
    apply sm2_eqm_product_nonzero.
    - change (2 <> 0). lia.
    - rewrite Z.mod_small by exact (proj1 (proj2 Hcurve)).
      exact Hpy.
  }
  pose proof
    (sm2_fe_of_Z_div_solution
      (3 * px * px + SM2_A_Z) (2 * py) lambda
      Hdenominator Hslope) as Hslope_fe.
  rewrite sm2_fe_of_Z_add, !sm2_fe_of_Z_mul,
    sm2_fe_of_Z_two, sm2_fe_of_Z_three,
    <- sm2_curve_a_as_fe in Hslope_fe.
  assert (Hy_not_opp :
    sm2_fe_of_Z py <> ZEll.pkopp (sm2_fe_of_Z py)).
  {
    intros Hequal.
    pose proof
      (SMain.Keq_opp_is_zero sm2_curve_theory Hequal) as Hzero.
    apply Hpy.
    assert (Hmod : py mod SM2_P_Z = 0 mod SM2_P_Z).
    {
      apply (proj1 (sm2_fe_of_Z_eq_iff py 0)).
      change (sm2_fe_of_Z py = sm2_fe_of_Z 0).
      rewrite Hzero.
      reflexivity.
    }
    rewrite Z.mod_small in Hmod by exact (proj1 (proj2 Hcurve)).
    rewrite Z.mod_0_l in Hmod by (pose proof sm2_p_gt_one; lia).
    exact Hmod.
  }
  unfold sm2_point_double, sm2_point_add, ec_point_of_affine, SMain.add.
  destruct
    (SMain.Kdec sm2_curve_theory
      (sm2_fe_of_Z px) (sm2_fe_of_Z px))
    as [Hxeq | Hxneq].
  - destruct
      (SMain.Kdec sm2_curve_theory
        (sm2_fe_of_Z py) (ZEll.pkopp (sm2_fe_of_Z py)))
      as [Hyopp | Hyopp].
    + exfalso. apply Hy_not_opp. exact Hyopp.
    + apply (SMain.curve_elt_irr sm2_curve_theory).
      * rewrite <- Hslope_fe.
        cbn [SMain.pow].
        rewrite <- sm2_fe_of_Z_mul.
        rewrite <- sm2_fe_of_Z_two.
        rewrite <- sm2_fe_of_Z_mul.
        rewrite <- sm2_fe_of_Z_sub.
        apply (proj2 (sm2_fe_of_Z_eq_iff _ _)).
        rewrite Hqx.
        rewrite Z.mod_mod by (pose proof sm2_p_gt_one; lia).
        reflexivity.
      * assert (Hcomputed_x :
          ZEll.pksub
            (SMain.pow
              (ZEll.pkI SM2_P_Z) (@ZEll.pkmul SM2_P_Z)
              (ZEll.pkdiv
                (ZEll.pkplus
                  (ZEll.pkmul
                    (ZEll.pkmul
                      (ZEll.pkplus
                        (ZEll.pkplus
                          (ZEll.pkI SM2_P_Z) (ZEll.pkI SM2_P_Z))
                        (ZEll.pkI SM2_P_Z))
                      (sm2_fe_of_Z px))
                    (sm2_fe_of_Z px))
                  (ZEll.pA SM2_A_Z SM2_P_Z))
                (ZEll.pkmul
                  (ZEll.pkplus
                    (ZEll.pkI SM2_P_Z) (ZEll.pkI SM2_P_Z))
                  (sm2_fe_of_Z py))) 2)
            (ZEll.pkmul
              (ZEll.pkplus
                (ZEll.pkI SM2_P_Z) (ZEll.pkI SM2_P_Z))
              (sm2_fe_of_Z px)) = sm2_fe_of_Z qx).
        {
          rewrite <- Hslope_fe.
          cbn [SMain.pow].
          rewrite <- sm2_fe_of_Z_mul.
          rewrite <- sm2_fe_of_Z_two.
          rewrite <- sm2_fe_of_Z_mul.
          rewrite <- sm2_fe_of_Z_sub.
          apply (proj2 (sm2_fe_of_Z_eq_iff _ _)).
          rewrite Hqx.
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
        rewrite Hqy.
        rewrite Z.mod_mod by (pose proof sm2_p_gt_one; lia).
        f_equal.
        ring.
  - exfalso. apply Hxneq. reflexivity.
Qed.

Lemma ec_double_finite_nonzero_construct :
  forall px py,
    forall (HPvalid : sm2_affine_on_curve px py),
    py <> 0 ->
    exists lambda qx qy,
      exists HQvalid : sm2_affine_on_curve qx qy,
        sm2_point_double (ec_point_of_affine px py HPvalid) =
          ec_point_of_affine qx qy HQvalid /\
        congr_mod SM2_P_Z qx (lambda * lambda - 2 * px) /\
        congr_mod SM2_P_Z qy (lambda * (px - qx) - py) /\
        congr_mod SM2_P_Z ((2 * py) * lambda)
          (3 * px * px + SM2_A_Z).
Proof.
  intros px py HPvalid Hpy.
  destruct (ec_tangent_slope_exists px py HPvalid Hpy)
    as [lambda [Hlambda Hslope]].
  set (raw_x := lambda * lambda - 2 * px).
  set (raw_y := lambda * (px - raw_x) - py).
  set (qx := raw_x mod SM2_P_Z).
  set (qy := raw_y mod SM2_P_Z).
  assert (Hqx_def : qx = raw_x mod SM2_P_Z) by reflexivity.
  assert (Hqy_def : qy = raw_y mod SM2_P_Z) by reflexivity.
  assert (Hraw_curve : congr_mod SM2_P_Z (raw_y * raw_y)
      (raw_x * raw_x * raw_x + SM2_A_Z * raw_x + SM2_B_Z)).
  { unfold raw_x, raw_y.
    apply ec_tangent_raw_preserves_curve.
    - exact HPvalid.
    - exact Hslope. }
  assert (HQvalid : sm2_affine_on_curve qx qy).
  { unfold qx, qy.
    now apply sm2_canonicalize_curve_point. }
  assert (Hqx : congr_mod SM2_P_Z qx raw_x).
  { unfold qx.
    apply congr_mod_mod.
    pose proof sm2_p_montgomery_bounds; lia. }
  assert (Hqy : congr_mod SM2_P_Z qy raw_y).
  { unfold qy.
    apply congr_mod_mod.
    pose proof sm2_p_montgomery_bounds; lia. }
  assert (Hqy_qx : congr_mod SM2_P_Z qy (lambda * (px - qx) - py)).
  { change (congr_mod SM2_P_Z qy raw_y) in Hqy.
    change (congr_mod SM2_P_Z qx raw_x) in Hqx.
    change (congr_mod SM2_P_Z qy (lambda * (px - qx) - py)).
    eapply congr_mod_trans; [exact Hqy|].
    unfold raw_y.
    apply congr_mod_sub.
    - apply congr_mod_scale.
      apply congr_mod_sub.
      + apply congr_mod_refl.
      + apply congr_mod_sym; exact Hqx.
    - apply congr_mod_refl. }
  assert (Hslope_eqm :
    eqm SM2_P_Z ((2 * py) * lambda)
      (3 * px * px + SM2_A_Z)).
  {
    unfold eqm.
    apply congr_mod_to_mod_eq.
    - pose proof sm2_p_gt_one. lia.
    - exact Hslope.
  }
  assert (Hqy_formula :
    qy = (lambda * (px - qx) - py) mod SM2_P_Z).
  {
    pose proof
      (congr_mod_to_mod_eq
        SM2_P_Z qy (lambda * (px - qx) - py)
        ltac:(pose proof sm2_p_gt_one; lia) Hqy_qx) as Heq.
    rewrite Z.mod_small in Heq by exact (proj1 (proj2 HQvalid)).
    exact Heq.
  }
  exists lambda, qx, qy, HQvalid.
  split.
  - apply
      (sm2_point_double_affine
        px py lambda qx qy HPvalid HQvalid);
      try assumption.
  - split.
    + unfold raw_x in Hqx; exact Hqx.
    + split; [exact Hqy_qx | exact Hslope].
Qed.

Local Transparent SM2_P_Z SM2_A_Z SM2_B_Z.

(** [a = -3] in the SM2 base field. *)
Lemma sm2_a_minus_three_congruence :
  forall t,
    congr_mod SM2_P_Z (t - 3) (t + SM2_A_Z).
Proof.
  intros t; unfold congr_mod, SM2_A_Z.
  exists (-1); lia.
Qed.

(** The Jacobian formula's numerator [3*(X^2-Z^4)] is the affine tangent
    slope multiplied by the output scale [RZ]. *)
Lemma sm2_jacobian_slope_matches_affine :
  forall x y z px py lambda m rz,
    congr_mod SM2_P_Z x (px * z ^ 2) ->
    congr_mod SM2_P_Z y (py * z ^ 3) ->
    congr_mod SM2_P_Z ((2 * py) * lambda) (3 * px * px + SM2_A_Z) ->
    congr_mod SM2_P_Z m (3 * (x * x - z ^ 4)) ->
    congr_mod SM2_P_Z rz (2 * y * z) ->
    congr_mod SM2_P_Z m (lambda * rz).
Proof.
  intros x y z px py lambda m rz Hx Hy Hslope Hm Hrz.
  change (congr_mod SM2_P_Z ((2 * py) * lambda)
    (3 * px * px + SM2_A_Z)) in Hslope.
  assert (Hx2 : congr_mod SM2_P_Z (x * x)
      ((px * px) * z ^ 4)).
  { pose proof (congr_mod_mul SM2_P_Z x (px * z ^ 2)
      x (px * z ^ 2) Hx Hx) as H.
    replace ((px * z ^ 2) * (px * z ^ 2)) with
      ((px * px) * z ^ 4) in H by ring.
    exact H. }
  assert (Hdiff : congr_mod SM2_P_Z (x * x - z ^ 4)
      ((px * px - 1) * z ^ 4)).
  { pose proof (congr_mod_sub SM2_P_Z
      (x * x) ((px * px) * z ^ 4)
      (z ^ 4) (z ^ 4) Hx2 (congr_mod_refl _ _)) as H.
    replace ((px * px) * z ^ 4 - z ^ 4) with
      ((px * px - 1) * z ^ 4) in H by ring.
    exact H. }
  assert (Hnum : congr_mod SM2_P_Z (3 * (x * x - z ^ 4))
      ((3 * px * px - 3) * z ^ 4)).
  { pose proof (congr_mod_scale SM2_P_Z 3 _ _ Hdiff) as H.
    replace (3 * ((px * px - 1) * z ^ 4)) with
      ((3 * px * px - 3) * z ^ 4) in H by ring.
    exact H. }
  assert (HA : congr_mod SM2_P_Z
      (3 * px * px - 3) (3 * px * px + SM2_A_Z)).
  { apply sm2_a_minus_three_congruence. }
  assert (Hnum_slope : congr_mod SM2_P_Z
      ((3 * px * px - 3) * z ^ 4)
      (((2 * py) * lambda) * z ^ 4)).
  { apply congr_mod_mul.
    - eapply congr_mod_trans; [exact HA|].
      apply congr_mod_sym; exact Hslope.
    - apply congr_mod_refl. }
  assert (Hrz_scaled : congr_mod SM2_P_Z rz (2 * py * z ^ 4)).
  { eapply congr_mod_trans; [exact Hrz|].
    pose proof (congr_mod_scale SM2_P_Z 2 _ _ Hy) as H.
    replace (2 * (py * z ^ 3)) with (2 * py * z ^ 3) in H by ring.
    pose proof (congr_mod_mul SM2_P_Z
      (2 * y) (2 * py * z ^ 3) z z H (congr_mod_refl _ _)) as Hzmul.
    replace ((2 * py * z ^ 3) * z) with (2 * py * z ^ 4)
      in Hzmul by ring.
    exact Hzmul. }
  eapply congr_mod_trans; [exact Hm|].
  eapply congr_mod_trans; [exact Hnum|].
  eapply congr_mod_trans; [exact Hnum_slope|].
  replace (((2 * py) * lambda) * z ^ 4) with
    (lambda * (2 * py * z ^ 4)) by ring.
  apply congr_mod_scale.
  apply congr_mod_sym; exact Hrz_scaled.
Qed.

Lemma sm2_jacobian_rz_matches_affine_scale :
  forall y z py rz,
    congr_mod SM2_P_Z y (py * z ^ 3) ->
    congr_mod SM2_P_Z rz (2 * y * z) ->
    congr_mod SM2_P_Z rz (2 * py * z ^ 4).
Proof.
  intros y z py rz Hy Hrz.
  eapply congr_mod_trans; [exact Hrz|].
  pose proof (congr_mod_scale SM2_P_Z 2 _ _ Hy) as H2.
  pose proof (congr_mod_mul SM2_P_Z
    (2 * y) (2 * (py * z ^ 3)) z z H2 (congr_mod_refl _ _)) as H.
  replace ((2 * (py * z ^ 3)) * z) with (2 * py * z ^ 4) in H by ring.
  exact H.
Qed.

Lemma sm2_jacobian_rx_matches_affine :
  forall x y z px py lambda m rz qx rx,
    congr_mod SM2_P_Z x (px * z ^ 2) ->
    congr_mod SM2_P_Z y (py * z ^ 3) ->
    congr_mod SM2_P_Z m (lambda * rz) ->
    congr_mod SM2_P_Z rz (2 * py * z ^ 4) ->
    congr_mod SM2_P_Z qx (lambda * lambda - 2 * px) ->
    congr_mod SM2_P_Z rx (m * m - 8 * x * y * y) ->
    congr_mod SM2_P_Z rx (qx * rz ^ 2).
Proof.
  intros x y z px py lambda m rz qx rx
    Hx Hy Hm Hrz Hqx Hrx.
  change (congr_mod SM2_P_Z qx (lambda * lambda - 2 * px)) in Hqx.
  assert (Hm2 : congr_mod SM2_P_Z (m * m)
      ((lambda * lambda) * rz ^ 2)).
  { pose proof (congr_mod_mul SM2_P_Z m (lambda * rz)
      m (lambda * rz) Hm Hm) as H.
    replace ((lambda * rz) * (lambda * rz)) with
      ((lambda * lambda) * rz ^ 2) in H by ring.
    exact H. }
  assert (Hy2 : congr_mod SM2_P_Z (y * y)
      ((py * py) * z ^ 6)).
  { pose proof (congr_mod_mul SM2_P_Z y (py * z ^ 3)
      y (py * z ^ 3) Hy Hy) as H.
    replace ((py * z ^ 3) * (py * z ^ 3)) with
      ((py * py) * z ^ 6) in H by ring.
    exact H. }
  assert (Hxy2 : congr_mod SM2_P_Z (x * y * y)
      (px * py * py * z ^ 8)).
  { pose proof (congr_mod_mul SM2_P_Z x (px * z ^ 2)
      (y * y) ((py * py) * z ^ 6) Hx Hy2) as H.
    replace ((px * z ^ 2) * ((py * py) * z ^ 6)) with
      (px * py * py * z ^ 8) in H by ring.
    replace (x * (y * y)) with (x * y * y) in H by ring.
    exact H. }
  assert (Hrz2 : congr_mod SM2_P_Z (rz ^ 2)
      (4 * py * py * z ^ 8)).
  { pose proof (congr_mod_pow2 SM2_P_Z rz (2 * py * z ^ 4) Hrz) as H.
    replace ((2 * py * z ^ 4) ^ 2) with
      (4 * py * py * z ^ 8) in H by ring.
    exact H. }
  assert (Hterm : congr_mod SM2_P_Z (8 * x * y * y)
      ((2 * px) * rz ^ 2)).
  { pose proof (congr_mod_scale SM2_P_Z 8 _ _ Hxy2) as Hleft.
    pose proof (congr_mod_scale SM2_P_Z (2 * px) _ _ Hrz2) as Hright.
    replace (8 * (x * y * y)) with (8 * x * y * y) in Hleft by ring.
    replace (8 * (px * py * py * z ^ 8)) with
      (8 * px * py * py * z ^ 8) in Hleft by ring.
    replace ((2 * px) * (4 * py * py * z ^ 8)) with
      (8 * px * py * py * z ^ 8) in Hright by ring.
    eapply congr_mod_trans; [exact Hleft|].
    apply congr_mod_sym; exact Hright. }
  assert (Hraw : congr_mod SM2_P_Z
      (m * m - 8 * x * y * y)
      ((lambda * lambda - 2 * px) * rz ^ 2)).
  { pose proof (congr_mod_sub SM2_P_Z
      (m * m) ((lambda * lambda) * rz ^ 2)
      (8 * x * y * y) ((2 * px) * rz ^ 2)
      Hm2 Hterm) as H.
    replace ((lambda * lambda) * rz ^ 2 - (2 * px) * rz ^ 2) with
      ((lambda * lambda - 2 * px) * rz ^ 2) in H by ring.
    exact H. }
  assert (Hqscaled : congr_mod SM2_P_Z (qx * rz ^ 2)
      ((lambda * lambda - 2 * px) * rz ^ 2)).
  { apply congr_mod_mul; [exact Hqx|apply congr_mod_refl]. }
  eapply congr_mod_trans; [exact Hrx|].
  eapply congr_mod_trans; [exact Hraw|].
  apply congr_mod_sym; exact Hqscaled.
Qed.

Lemma sm2_jacobian_ry_matches_affine :
  forall x y z px py lambda m rz qx qy rx ry,
    congr_mod SM2_P_Z x (px * z ^ 2) ->
    congr_mod SM2_P_Z y (py * z ^ 3) ->
    congr_mod SM2_P_Z m (lambda * rz) ->
    congr_mod SM2_P_Z rz (2 * py * z ^ 4) ->
    congr_mod SM2_P_Z rx (qx * rz ^ 2) ->
    congr_mod SM2_P_Z qy (lambda * (px - qx) - py) ->
    congr_mod SM2_P_Z ry
      (m * (4 * x * y * y - rx) - 8 * y ^ 4) ->
    congr_mod SM2_P_Z ry (qy * rz ^ 3).
Proof.
  intros x y z px py lambda m rz qx qy rx ry
    Hx Hy Hm Hrz Hrx Hqy Hry.
  change (congr_mod SM2_P_Z qy (lambda * (px - qx) - py)) in Hqy.
  assert (Hy2 : congr_mod SM2_P_Z (y * y)
      ((py * py) * z ^ 6)).
  { pose proof (congr_mod_mul SM2_P_Z y (py * z ^ 3)
      y (py * z ^ 3) Hy Hy) as H.
    replace ((py * z ^ 3) * (py * z ^ 3)) with
      ((py * py) * z ^ 6) in H by ring.
    exact H. }
  assert (Hxy2 : congr_mod SM2_P_Z (x * y * y)
      (px * py * py * z ^ 8)).
  { pose proof (congr_mod_mul SM2_P_Z x (px * z ^ 2)
      (y * y) ((py * py) * z ^ 6) Hx Hy2) as H.
    replace (x * (y * y)) with (x * y * y) in H by ring.
    replace ((px * z ^ 2) * ((py * py) * z ^ 6)) with
      (px * py * py * z ^ 8) in H by ring.
    exact H. }
  assert (Hrz2 : congr_mod SM2_P_Z (rz ^ 2)
      (4 * py * py * z ^ 8)).
  { pose proof (congr_mod_pow2 SM2_P_Z rz (2 * py * z ^ 4) Hrz) as H.
    replace ((2 * py * z ^ 4) ^ 2) with
      (4 * py * py * z ^ 8) in H by ring.
    exact H. }
  assert (Hfour : congr_mod SM2_P_Z (4 * x * y * y)
      (px * rz ^ 2)).
  { pose proof (congr_mod_scale SM2_P_Z 4 _ _ Hxy2) as Hleft.
    replace (4 * (x * y * y)) with (4 * x * y * y) in Hleft by ring.
    replace (4 * (px * py * py * z ^ 8)) with
      (4 * px * py * py * z ^ 8) in Hleft by ring.
    pose proof (congr_mod_scale SM2_P_Z px _ _ Hrz2) as Hright.
    replace (px * (4 * py * py * z ^ 8)) with
      (4 * px * py * py * z ^ 8) in Hright by ring.
    eapply congr_mod_trans; [exact Hleft|].
    apply congr_mod_sym; exact Hright. }
  assert (Hinside : congr_mod SM2_P_Z (4 * x * y * y - rx)
      ((px - qx) * rz ^ 2)).
  { pose proof (congr_mod_sub SM2_P_Z
      (4 * x * y * y) (px * rz ^ 2)
      rx (qx * rz ^ 2) Hfour Hrx) as H.
    replace (px * rz ^ 2 - qx * rz ^ 2) with
      ((px - qx) * rz ^ 2) in H by ring.
    exact H. }
  assert (Hfirst : congr_mod SM2_P_Z
      (m * (4 * x * y * y - rx))
      ((lambda * (px - qx)) * rz ^ 3)).
  { pose proof (congr_mod_mul SM2_P_Z m (lambda * rz)
      (4 * x * y * y - rx) ((px - qx) * rz ^ 2)
      Hm Hinside) as H.
    replace ((lambda * rz) * ((px - qx) * rz ^ 2)) with
      ((lambda * (px - qx)) * rz ^ 3) in H by ring.
    exact H. }
  assert (Hy4 : congr_mod SM2_P_Z (y ^ 4)
      (py ^ 4 * z ^ 12)).
  { pose proof (congr_mod_pow4 SM2_P_Z y (py * z ^ 3) Hy) as H.
    replace ((py * z ^ 3) ^ 4) with (py ^ 4 * z ^ 12) in H by ring.
    exact H. }
  assert (Hrz3 : congr_mod SM2_P_Z (rz ^ 3)
      (8 * py ^ 3 * z ^ 12)).
  { pose proof (congr_mod_pow3 SM2_P_Z rz (2 * py * z ^ 4) Hrz) as H.
    replace ((2 * py * z ^ 4) ^ 3) with
      (8 * py ^ 3 * z ^ 12) in H by ring.
    exact H. }
  assert (Heighth : congr_mod SM2_P_Z (8 * y ^ 4)
      (py * rz ^ 3)).
  { pose proof (congr_mod_scale SM2_P_Z 8 _ _ Hy4) as Hleft.
    pose proof (congr_mod_scale SM2_P_Z py _ _ Hrz3) as Hright.
    replace (8 * (py ^ 4 * z ^ 12)) with
      (8 * py ^ 4 * z ^ 12) in Hleft by ring.
    replace (py * (8 * py ^ 3 * z ^ 12)) with
      (8 * py ^ 4 * z ^ 12) in Hright by ring.
    eapply congr_mod_trans; [exact Hleft|].
    apply congr_mod_sym; exact Hright. }
  assert (Hraw : congr_mod SM2_P_Z
      (m * (4 * x * y * y - rx) - 8 * y ^ 4)
      ((lambda * (px - qx) - py) * rz ^ 3)).
  { pose proof (congr_mod_sub SM2_P_Z
      (m * (4 * x * y * y - rx))
        ((lambda * (px - qx)) * rz ^ 3)
      (8 * y ^ 4) (py * rz ^ 3)
      Hfirst Heighth) as H.
    replace ((lambda * (px - qx)) * rz ^ 3 - py * rz ^ 3) with
      ((lambda * (px - qx) - py) * rz ^ 3) in H by ring.
    exact H. }
  assert (Hqscaled : congr_mod SM2_P_Z (qy * rz ^ 3)
      ((lambda * (px - qx) - py) * rz ^ 3)).
  { apply congr_mod_mul; [exact Hqy|apply congr_mod_refl]. }
  eapply congr_mod_trans; [exact Hry|].
  eapply congr_mod_trans; [exact Hraw|].
  apply congr_mod_sym; exact Hqscaled.
Qed.


Lemma jpoint_double_coordinates_ranges :
  forall x y z result_x result_y result_z,
    jpoint_double_coordinates x y z result_x result_y result_z ->
    0 <= result_x < SM2_P_Z /\
    0 <= result_y < SM2_P_Z /\
    0 <= result_z < SM2_P_Z.
Proof.
  intros x y z result_x result_y result_z Hcoordinates.
  unfold jpoint_double_coordinates in Hcoordinates.
  destruct Hcoordinates as [Hx [Hy Hz]].
  subst result_x result_y result_z.
  repeat split; apply Z.mod_pos_bound; pose proof sm2_p_gt_one; lia.
Qed.

Lemma jpoint_double_coordinates_refines_point :
  forall x y z result_x result_y result_z point,
    jpoint_represents x y z point ->
    jpoint_double_coordinates x y z result_x result_y result_z ->
    jpoint_represents
      result_x result_y result_z (sm2_point_double point).
Proof.
  intros x y z result_x result_y result_z point Hinput Hcoordinates.
  pose proof
    (jpoint_double_coordinates_ranges
       x y z result_x result_y result_z Hcoordinates)
    as [Hresult_x [Hresult_y Hresult_z]].
  destruct point as [|point_x_fe point_y_fe Hpoint_curve_fe].
  - cbn [jpoint_represents] in Hinput.
    destruct Hinput as [Hx [Hy [Hz Hzero]]].
    unfold jpoint_double_coordinates in Hcoordinates.
    destruct Hcoordinates as [_ [_ Hresult_zero]].
    unfold jpoint_infinity in Hzero.
    subst z.
    rewrite Z.mul_0_r, Z.mod_0_l in Hresult_zero
      by (pose proof sm2_p_gt_one; lia).
    change (jpoint_represents result_x result_y result_z ECInfinity).
    cbn [jpoint_represents jpoint_infinity].
    split; [exact Hresult_x|].
    split; [exact Hresult_y|].
    split; [exact Hresult_z|].
    exact Hresult_zero.
  - cbn [jpoint_represents] in Hinput.
    destruct Hinput as
      [Hx [Hy [Hz [Hz_nonzero [Hx_scale Hy_scale]]]]].
    set (point_x := sm2_fe_value point_x_fe).
    set (point_y := sm2_fe_value point_y_fe).
    assert (Hpoint_curve : sm2_affine_on_curve point_x point_y).
    {
      unfold sm2_affine_on_curve.
      split; [unfold point_x; apply sm2_fe_value_bounds |].
      split; [unfold point_y; apply sm2_fe_value_bounds |].
      unfold sm2_affine_equation, point_x, point_y.
      repeat rewrite sm2_fe_of_Z_value.
      exact Hpoint_curve_fe.
    }
    pose proof (sm2_point_on_curve_coordinate_bounds
      point_x point_y Hpoint_curve) as
      [Hpoint_x_range Hpoint_y_range].
    pose proof
      (sm2_point_on_curve_y_nonzero point_x point_y Hpoint_curve)
      as Hpoint_y_nonzero.
    destruct
      (ec_double_finite_nonzero_construct
         point_x point_y Hpoint_curve Hpoint_y_nonzero)
      as [slope [qx [qy
        [Hresult_curve [Hdouble [Hqx [Hqy Hslope]]]]]]].
    assert (Hpoint_affine :
      @SMain.curve_elt
        (ZEll.pK SM2_P_Z)
        (ZEll.pkI SM2_P_Z) (@ZEll.pkplus SM2_P_Z)
        (@ZEll.pkmul SM2_P_Z)
        (ZEll.pA SM2_A_Z SM2_P_Z)
        (ZEll.pB SM2_B_Z SM2_P_Z)
        point_x_fe point_y_fe Hpoint_curve_fe =
      ec_point_of_affine point_x point_y Hpoint_curve).
    {
      unfold ec_point_of_affine.
      apply (SMain.curve_elt_irr sm2_curve_theory).
      - symmetry. unfold point_x. apply sm2_fe_of_Z_value.
      - symmetry. unfold point_y. apply sm2_fe_of_Z_value.
    }
    assert (Hp : SM2_P_Z <> 0) by (pose proof sm2_p_gt_one; lia).
    assert (Hx_congr :
      congr_mod SM2_P_Z x (point_x * z ^ 2)).
    {
      apply congr_mod_of_mod_eq; [exact Hp|].
      rewrite Z.mod_small by exact Hx.
      exact Hx_scale.
    }
    assert (Hy_congr :
      congr_mod SM2_P_Z y (point_y * z ^ 3)).
    {
      apply congr_mod_of_mod_eq; [exact Hp|].
      rewrite Z.mod_small by exact Hy.
      exact Hy_scale.
    }
    set (m := (3 * (x * x - z ^ 4)) mod SM2_P_Z).
    assert (Hm_raw : congr_mod SM2_P_Z m (3 * (x * x - z ^ 4))).
    { unfold m. apply congr_mod_mod; exact Hp. }
    unfold jpoint_double_coordinates in Hcoordinates.
    fold m in Hcoordinates.
    destruct Hcoordinates as [Hrx_eq [Hry_eq Hrz_eq]].
    assert (Hrx_raw : congr_mod SM2_P_Z result_x
      (m * m - 8 * x * y * y)).
    { rewrite Hrx_eq. apply congr_mod_mod; exact Hp. }
    assert (Hry_raw : congr_mod SM2_P_Z result_y
      (m * (4 * x * y * y - result_x) - 8 * y ^ 4)).
    { rewrite Hry_eq. apply congr_mod_mod; exact Hp. }
    assert (Hrz_raw : congr_mod SM2_P_Z result_z (2 * y * z)).
    { rewrite Hrz_eq. apply congr_mod_mod; exact Hp. }
    assert (Hrz_scale :
      congr_mod SM2_P_Z result_z (2 * point_y * z ^ 4)).
    {
      eapply sm2_jacobian_rz_matches_affine_scale;
        [exact Hy_congr|exact Hrz_raw].
    }
    assert (Hm_scale : congr_mod SM2_P_Z m (slope * result_z)).
    {
      eapply sm2_jacobian_slope_matches_affine;
        [exact Hx_congr|exact Hy_congr|exact Hslope|
         exact Hm_raw|exact Hrz_raw].
    }
    assert (Hrx_projective :
      congr_mod SM2_P_Z result_x (qx * result_z ^ 2)).
    {
      eapply sm2_jacobian_rx_matches_affine;
        [exact Hx_congr|exact Hy_congr|exact Hm_scale|exact Hrz_scale|
         exact Hqx|exact Hrx_raw].
    }
    assert (Hry_projective :
      congr_mod SM2_P_Z result_y (qy * result_z ^ 3)).
    {
      eapply sm2_jacobian_ry_matches_affine;
        [exact Hx_congr|exact Hy_congr|exact Hm_scale|exact Hrz_scale|
         exact Hrx_projective|exact Hqy|exact Hry_raw].
    }
    assert (Hresult_z_nonzero : result_z <> 0).
    {
      pose proof
        (sm2_double_y_z4_mod_nonzero
           point_y z
           Hpoint_y_range Hpoint_y_nonzero
           Hz Hz_nonzero)
        as Hraw_nonzero.
      intro Hzero.
      pose proof
        (congr_mod_to_mod_eq
           SM2_P_Z result_z (2 * point_y * z ^ 4) Hp Hrz_scale)
        as Heq.
      rewrite Z.mod_small in Heq by exact Hresult_z.
      rewrite Hzero in Heq.
      apply Hraw_nonzero.
      symmetry; exact Heq.
    }
    rewrite Hpoint_affine, Hdouble.
    cbn [jpoint_represents ec_point_of_affine].
    split; [exact Hresult_x|].
    split; [exact Hresult_y|].
    split; [exact Hresult_z|].
    split; [exact Hresult_z_nonzero|].
    split.
    + pose proof
        (congr_mod_to_mod_eq
           SM2_P_Z result_x (qx * result_z ^ 2) Hp Hrx_projective)
        as Heq.
      rewrite Z.mod_small in Heq by exact Hresult_x.
      rewrite
        (sm2_fe_value_of_Z qx (proj1 Hresult_curve)).
      exact Heq.
    + pose proof
        (congr_mod_to_mod_eq
           SM2_P_Z result_y (qy * result_z ^ 3) Hp Hry_projective)
        as Heq.
      rewrite Z.mod_small in Heq by exact Hresult_y.
      rewrite
        (sm2_fe_value_of_Z qy (proj1 (proj2 Hresult_curve))).
      exact Heq.
Qed.

Lemma jpoint_double_point_of_trace :
  forall x y z P,
    jpoint_represents x y z P ->
    jpoint_represents
      (jdouble_trace_rx x y z)
      (jdouble_trace_ry x y z)
      ((jdouble_trace_s2 y * z) mod SM2_P_Z)
      (sm2_point_double P).
Proof.
  intros x y z P Hrep.
  eapply jpoint_double_coordinates_refines_point;
    [exact Hrep | apply jdouble_trace_coordinates].
Qed.

Lemma jdouble_trace_finite_result_z_nonzero :
  forall x y z point,
    point <> ECInfinity ->
    jpoint_represents x y z point ->
    (jdouble_trace_s2 y * z) mod SM2_P_Z <> 0.
Proof.
  intros x y z point Hfinite Hrep.
  destruct point as [|point_x_fe point_y_fe Hpoint_curve_fe].
  { contradiction. }
  cbn [jpoint_represents] in Hrep.
  destruct Hrep as
    [Hx [Hy [Hz [Hz_nonzero [_ Hy_scale]]]]].
  set (point_x := sm2_fe_value point_x_fe).
  set (point_y := sm2_fe_value point_y_fe).
  assert (Hcurve : sm2_affine_on_curve point_x point_y).
  {
    unfold sm2_affine_on_curve.
    split; [unfold point_x; apply sm2_fe_value_bounds |].
    split; [unfold point_y; apply sm2_fe_value_bounds |].
    unfold sm2_affine_equation, point_x, point_y.
    repeat rewrite sm2_fe_of_Z_value.
    exact Hpoint_curve_fe.
  }
  pose proof (sm2_point_on_curve_coordinate_bounds
    point_x point_y Hcurve) as [_ Hpoint_y_range].
  pose proof
    (sm2_point_on_curve_y_nonzero point_x point_y Hcurve)
    as Hpoint_y_nonzero.
  assert (Hp : SM2_P_Z <> 0)
    by (pose proof sm2_p_montgomery_bounds; lia).
  assert (Hy_congr : congr_mod SM2_P_Z y (point_y * z ^ 3)).
  { apply congr_mod_of_mod_eq; [exact Hp|].
    rewrite Z.mod_small by exact Hy.
    exact Hy_scale. }
  set (rz := (jdouble_trace_s2 y * z) mod SM2_P_Z).
  assert (Hrz_raw : congr_mod SM2_P_Z rz (2 * y * z)).
  { unfold rz, jdouble_trace_s2.
    eapply congr_mod_trans.
    - apply congr_mod_mod; exact Hp.
    - pose proof (congr_mod_mul SM2_P_Z
        ((2 * y) mod SM2_P_Z) (2 * y) z z
        (congr_mod_mod _ _ Hp) (congr_mod_refl _ _)) as H.
      exact H. }
  assert (Hrz_scale : congr_mod SM2_P_Z rz (2 * point_y * z ^ 4))
    by (eapply sm2_jacobian_rz_matches_affine_scale; eauto).
  assert (Hraw : (2 * point_y * z ^ 4) mod SM2_P_Z <> 0)
    by (eapply sm2_double_y_z4_mod_nonzero; eauto).
  intro Hrz0; apply Hraw.
  pose proof (congr_mod_to_mod_eq SM2_P_Z rz
    (2 * point_y * z ^ 4) Hp Hrz_scale) as Heq.
  rewrite Hrz0, Z.mod_0_l in Heq by exact Hp.
  symmetry; exact Heq.
Qed.

Lemma jdouble_trace_preserves_canonical_infinity :
  forall x y z P R,
    jpoint_represents x y z P ->
    jpoint_canonical_infinity_encoding x y z P ->
    jpoint_represents
      (jdouble_trace_rx x y z)
      (jdouble_trace_ry x y z)
      ((jdouble_trace_s2 y * z) mod SM2_P_Z) R ->
    jpoint_canonical_infinity_encoding
      (jdouble_trace_rx x y z)
      (jdouble_trace_ry x y z)
      ((jdouble_trace_s2 y * z) mod SM2_P_Z) R.
Proof.
  intros x y z P R Hinput Hcanonical Hresult.
  unfold jpoint_canonical_infinity_encoding in Hcanonical |- *.
  intro HR; subst R.
  destruct P as [|point_x point_y Hpoint_curve].
  - specialize (Hcanonical eq_refl).
    unfold canonical_jpoint_infinity in Hcanonical.
    destruct Hcanonical as [Hx [Hy Hz]].
    subst x y z.
    unfold jdouble_trace_rx, jdouble_trace_ry, jdouble_trace_s2,
      jdouble_trace_z2, jdouble_trace_m4, jdouble_trace_t16,
      jdouble_trace_s4, jdouble_trace_t8, jdouble_trace_sum,
      jdouble_trace_diff, jdouble_trace_prod, jdouble_trace_slope,
      jdouble_trace_slope_sq, jdouble_trace_u8, jdouble_trace_tmp,
      jdouble_trace_tmp2, canonical_jpoint_infinity, fp_div2.
    vm_compute.
    repeat split; reflexivity.
  - pose proof
      (jdouble_trace_finite_result_z_nonzero
         x y z
         (@SMain.curve_elt
           (ZEll.pK SM2_P_Z)
           (ZEll.pkI SM2_P_Z) (@ZEll.pkplus SM2_P_Z)
           (@ZEll.pkmul SM2_P_Z)
           (ZEll.pA SM2_A_Z SM2_P_Z)
           (ZEll.pB SM2_B_Z SM2_P_Z)
           point_x point_y Hpoint_curve)
         ltac:(discriminate) Hinput) as Hz_nonzero.
    cbn [jpoint_represents jpoint_infinity] in Hresult.
    exfalso.
    apply Hz_nonzero.
    exact (proj2 (proj2 (proj2 Hresult))).
Qed.
