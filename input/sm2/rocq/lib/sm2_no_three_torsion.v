(** The standard SM2 curve has no nontrivial point of order three. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
From Coqprime Require Import elliptic.ZEll.
Require Import Coqprime.PrimalityTest.EGroup.
From SimpleC.EE.Applications_human.sm2.lib Require Import
  sm2_primality sm2_curve sm2_generator_order.

Local Open Scope Z_scope.

Definition sm2_point_order (point : ec_point) : Z :=
  EGroup.e_order sm2_ec_point_dec point sm2_group.

Lemma sm2_point_order_pos :
  forall point, 0 < sm2_point_order point.
Proof.
  intros point.
  unfold sm2_point_order.
  apply EGroup.e_order_pos.
Qed.

Lemma sm2_point_order_divides_scalar :
  forall point scalar,
    0 <= scalar ->
    sm2_point_mul scalar point = ECInfinity ->
    (sm2_point_order point | scalar).
Proof.
  intros point scalar Hscalar Hmul.
  unfold sm2_point_order.
  eapply EGroup.e_order_divide_gpow.
  - apply ec_point_in_sm2_group.
  - exact Hscalar.
  - unfold sm2_point_mul in Hmul.
    rewrite sm2_group_identity.
    exact Hmul.
Qed.

Lemma sm2_point_order_mul_identity :
  forall point,
    sm2_point_mul (sm2_point_order point) point = ECInfinity.
Proof.
  intros point.
  unfold sm2_point_mul, sm2_point_order.
  rewrite EGroup.gpow_e_order_is_e by apply ec_point_in_sm2_group.
  apply sm2_group_identity.
Qed.

Lemma sm2_point_order_divides_group :
  forall point,
    (sm2_point_order point | FGroup.g_order sm2_group).
Proof.
  intros point.
  unfold sm2_point_order.
  apply EGroup.e_order_divide_g_order.
  apply ec_point_in_sm2_group.
Qed.

Lemma sm2_group_order_bound :
  FGroup.g_order sm2_group <= 2 * SM2_P_Z + 1.
Proof.
  exact (@ZEll.gorder_pG
    SM2_P_Z SM2_A_Z SM2_B_Z
    sm2_p_not_divides_two sm2_curve_nonsingular
    SM2_P_Z sm2_p_prime (Z.divide_refl SM2_P_Z)).
Qed.

Lemma sm2_generator_point_order :
  sm2_point_order SM2_G_POINT = SM2_N_Z.
Proof.
  unfold sm2_point_order.
  exact sm2_generator_order_value.
Qed.

Lemma group_order_arithmetic_no_three :
  forall p n generator_order group_order,
    0 < n ->
    generator_order = n ->
    0 < group_order ->
    group_order <= 2 * p + 1 ->
    2 * p + 1 < 3 * n ->
    n mod 3 = 1 ->
    (generator_order | group_order) ->
    ~ (3 | group_order).
Proof.
  intros p n generator_order group_order Hn_pos Hgenerator_order
    Hgroup_pos Hgroup_bound Hthree_n_above_bound Hn_mod_three
    Hgenerator_divides_group Hthree_divides_group.
  assert (Hthree_not_divides_n : ~ (3 | n)).
  {
    intros Hdivide.
    pose proof
      (proj2 (Z.mod_divide n 3 ltac:(lia)) Hdivide) as Hmod.
    lia.
  }
  assert (Hthree_not_divides_two_n : ~ (3 | 2 * n)).
  {
    intros Hdivide.
    pose proof
      (proj2 (Z.mod_divide (2 * n) 3 ltac:(lia)) Hdivide) as Hmod.
    rewrite Z.mul_mod, Hn_mod_three in Hmod by lia.
    vm_compute in Hmod.
    discriminate.
  }
  destruct Hgenerator_divides_group as [multiple Hgroup].
  rewrite Hgenerator_order in Hgroup.
  assert (0 < multiple) by nia.
  assert (multiple < 3) by nia.
  assert (multiple = 1 \/ multiple = 2) as [-> | ->] by lia.
  - apply Hthree_not_divides_n.
    rewrite Hgroup in Hthree_divides_group.
    replace (1 * n) with n in Hthree_divides_group by ring.
    exact Hthree_divides_group.
  - apply Hthree_not_divides_two_n.
    rewrite Hgroup in Hthree_divides_group.
    exact Hthree_divides_group.
Qed.

Lemma sm2_group_bound_lt_three_n :
  2 * SM2_P_Z + 1 < 3 * SM2_N_Z.
Proof. vm_compute. reflexivity. Qed.

Lemma sm2_n_mod_three :
  SM2_N_Z mod 3 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma sm2_group_order_not_divisible_by_three :
  ~ (3 | FGroup.g_order sm2_group).
Proof.
  eapply group_order_arithmetic_no_three
    with (p := SM2_P_Z)
         (n := SM2_N_Z)
         (generator_order := sm2_point_order SM2_G_POINT).
  - pose proof sm2_n_bounds. lia.
  - exact sm2_generator_point_order.
  - apply FGroup.g_order_pos.
  - exact sm2_group_order_bound.
  - exact sm2_group_bound_lt_three_n.
  - exact sm2_n_mod_three.
  - apply sm2_point_order_divides_group.
Qed.

Lemma positive_nonone_divisor_of_three :
  forall order,
    0 < order ->
    order <> 1 ->
    (order | 3) ->
    order = 3.
Proof.
  intros order Hpositive Hnot_one Hdivide.
  assert (Horder_le : order <= 3).
  {
    apply Z.divide_pos_le.
    - lia.
    - exact Hdivide.
  }
  destruct Hdivide as [quotient Hquotient].
  assert (order = 1 \/ order = 2 \/ order = 3)
    as [Hone | [Htwo | Hthree]] by lia.
  - exfalso. exact (Hnot_one Hone).
  - rewrite Htwo in Hquotient. nia.
  - exact Hthree.
Qed.

Theorem sm2_point_mul_three_noninfinity :
  forall point,
    point <> ECInfinity ->
    sm2_point_mul 3 point <> ECInfinity.
Proof.
  intros point Hpoint Htriple.
  pose proof (sm2_point_order_pos point) as Horder_pos.
  pose proof
    (sm2_point_order_divides_scalar point 3 ltac:(lia) Htriple)
    as Horder_divides_three.
  assert (Horder_not_one : sm2_point_order point <> 1).
  {
    intros Horder_one.
    pose proof (sm2_point_order_mul_identity point) as Hpoint_order.
    rewrite Horder_one, sm2_point_mul_one in Hpoint_order.
    exact (Hpoint Hpoint_order).
  }
  pose proof
    (positive_nonone_divisor_of_three
      (sm2_point_order point)
      Horder_pos Horder_not_one Horder_divides_three)
    as Horder_three.
  apply sm2_group_order_not_divisible_by_three.
  pose proof (sm2_point_order_divides_group point) as Hdivide.
  rewrite Horder_three in Hdivide.
  exact Hdivide.
Qed.
