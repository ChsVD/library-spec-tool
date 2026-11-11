Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.Applications_human.sm2.lib Require Import add_JPoint_lib.
From SimpleC.EE.Applications_human.sm2.lib Require Import
  ec_math_refinement fieldOp_lib.

Import Snaive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.

Ltac finish_spatial_trace :=
  entailer!;
  rewrite <- derivable1_wand_sepcon_adjoint;
  entailer!.

Ltac finish_mont_trace trace_definition :=
  unfold trace_definition;
  rewrite ec_math_refinement.mont_p_mod;
  finish_spatial_trace.

Ltac solve_mont_mod_trace trace_definition :=
  pre_process_default;
  finish_mont_trace trace_definition.

Ltac solve_mont_add_trace trace_definition :=
  pre_process_default;
  rewrite ec_math_refinement.mont_p_add;
  finish_mont_trace trace_definition.

Ltac solve_mont_sub_trace trace_definition :=
  pre_process_default;
  rewrite ec_math_refinement.mont_p_sub;
  finish_mont_trace trace_definition.

Ltac solve_aj_trace_range trace_definition :=
  pre_process_default;
  unfold trace_definition;
  match goal with
  | |- context [Zmod ?value SM2_P_Z] =>
      let Hrange := fresh "Hrange" in
      pose proof (aj_mod_range value) as Hrange
  end;
  entailer!.

Lemma montg_add_equal_points :
  forall x1 y1 z1 x2 y2 z2 P1 P2,
    jpoint_represents x1 y1 z1 P1 ->
    jpoint_represents x2 y2 z2 P2 ->
    z1 <> 0 -> z2 <> 0 ->
    mont_p (aj_u1 x1 z2) = mont_p (aj_u2 x2 z1) ->
    mont_p (aj_s1 y1 z2) = mont_p (aj_s2 y2 z1) ->
    P1 = P2.
Proof.
  intros x1 y1 z1 x2 y2 z2 P1 P2 HR1 HR2 Hz1 Hz2 Hu Hs.
  apply (aj_same_u_same_s_points_equal
    x1 y1 z1 x2 y2 z2 P1 P2 HR1 HR2 Hz1 Hz2).
  - eapply mont_p_injective.
    + unfold aj_u1; apply aj_mod_range.
    + unfold aj_u2; apply aj_mod_range.
    + exact Hu.
  - eapply mont_p_injective.
    + unfold aj_s1; apply aj_mod_range.
    + unfold aj_s2; apply aj_mod_range.
    + exact Hs.
Qed.

Lemma montg_add_generic_formula_represents :
  forall x1 y1 z1 x2 y2 z2 P1 P2,
    jpoint_represents x1 y1 z1 P1 ->
    jpoint_represents x2 y2 z2 P2 ->
    z1 <> 0 -> z2 <> 0 ->
    (mont_p (aj_u1 x1 z2) <> mont_p (aj_u2 x2 z1) \/
     (mont_p (aj_u1 x1 z2) = mont_p (aj_u2 x2 z1) /\
      mont_p (aj_s1 y1 z2) <> mont_p (aj_s2 y2 z1))) ->
    jpoint_represents
      (aj_rx x1 y1 z1 x2 y2 z2)
      (aj_ry x1 y1 z1 x2 y2 z2)
      (aj_rz x1 z1 x2 z2)
      (sm2_point_add P1 P2).
Proof.
  intros x1 y1 z1 x2 y2 z2 P1 P2 HR1 HR2 Hz1 Hz2 Hcase.
  destruct Hcase as [Hu | [Hu Hs]].
  - assert (Hu' : aj_u1 x1 z2 <> aj_u2 x2 z1).
    {
      intro Heq; apply Hu; now rewrite Heq.
    }
    exact (proj1 (aj_result_refines_finite_distinct
      x1 y1 z1 x2 y2 z2 P1 P2 HR1 HR2 Hu' Hz1 Hz2)).
  - assert (Hu' : aj_u1 x1 z2 = aj_u2 x2 z1).
    {
      eapply mont_p_injective.
      + unfold aj_u1; apply aj_mod_range.
      + unfold aj_u2; apply aj_mod_range.
      + exact Hu.
    }
    assert (Hs' : aj_s1 y1 z2 <> aj_s2 y2 z1).
    {
      intro Heq; apply Hs; now rewrite Heq.
    }
    pose proof (aj_same_u_different_s_implies_s_sum_zero
      x1 y1 z1 x2 y2 z2 P1 P2 HR1 HR2 Hz1 Hz2 Hu' Hs') as Hsum.
    pose proof (aj_same_u_s_sum_zero_adds_infinity
      x1 y1 z1 x2 y2 z2 P1 P2 HR1 HR2 Hz1 Hz2 Hu' Hsum) as Hadd.
    assert (Hrx :
      0 <= aj_rx x1 y1 z1 x2 y2 z2 < SM2_P_Z).
    { unfold aj_rx; apply aj_mod_range. }
    assert (Hry :
      0 <= aj_ry x1 y1 z1 x2 y2 z2 < SM2_P_Z).
    { unfold aj_ry; apply aj_mod_range. }
    assert (Hrz :
      0 <= aj_rz x1 z1 x2 z2 < SM2_P_Z).
    { unfold aj_rz; apply aj_mod_range. }
    assert (Hrz0 : aj_rz x1 z1 x2 z2 = 0).
    {
      unfold aj_rz, aj_h.
      rewrite Hu'.
      rewrite Z.sub_diag, Z.mod_0_l.
      - rewrite Z.mul_0_r, Z.mod_0_l.
        + reflexivity.
        + pose proof sm2_p_gt_one; lia.
      - pose proof sm2_p_gt_one; lia.
    }
    rewrite Hadd.
    unfold jpoint_represents, ECInfinity, jpoint_infinity.
    cbn.
    repeat split.
    all: first
      [ exact (proj1 Hrx) | exact (proj2 Hrx)
      | exact (proj1 Hry) | exact (proj2 Hry)
      | exact (proj1 Hrz) | exact (proj2 Hrz)
      | exact Hrz0 ].
Qed.

Lemma fp_div2_eq_inv2_mod :
  forall x,
    0 <= x < SM2_P_Z ->
    fp_div2 x = Zmod (x * SM2_P_INV2_Z) SM2_P_Z.
Proof.
  intros x Hx.
  apply congr_mod_eq_canonical with (p := SM2_P_Z).
  - pose proof sm2_p_montgomery_bounds; lia.
  - exact (fp_div2_bounds x Hx).
  - apply aj_mod_range.
  - apply congr_mod_sym.
    apply aj_inv2_congr_half.
    rewrite <- fp_div2_adjusted_twice.
    unfold fp_div2_adjusted, congr_mod.
    destruct (Z.even x).
    + exists 0; lia.
    + exists (-1); lia.
Qed.

Lemma montg_add_right_y_mont :
  forall x1 y1 z1 x2 y2 z2,
    mont_p
      (aj_s_sum y1 z1 y2 z2 *
       Zmod (aj_h2 x1 z1 x2 z2 * aj_h x1 z1 x2 z2) SM2_P_Z) =
    mont_p (aj_right_y x1 y1 z1 x2 y2 z2).
Proof.
  intros.
  unfold aj_right_y.
  rewrite ec_math_refinement.mont_p_mod.
  unfold mont_p, Montgomery.mont.
  replace
    (aj_s_sum y1 z1 y2 z2 *
       Zmod (aj_h2 x1 z1 x2 z2 * aj_h x1 z1 x2 z2) SM2_P_Z *
       U256_MOD)
    with
    ((aj_s_sum y1 z1 y2 z2 * U256_MOD) *
       Zmod (aj_h2 x1 z1 x2 z2 * aj_h x1 z1 x2 z2) SM2_P_Z)
    by ring.
  rewrite Z.mul_mod_idemp_r by (pose proof sm2_p_gt_one; lia).
  f_equal; ring.
Qed.

Lemma montg_add_ry_mont :
  forall x1 y1 z1 x2 y2 z2,
    mont_p (fp_div2 (aj_y_num x1 y1 z1 x2 y2 z2)) =
    mont_p (aj_ry x1 y1 z1 x2 y2 z2).
Proof.
  intros.
  unfold aj_ry.
  rewrite <- fp_div2_eq_inv2_mod.
  - reflexivity.
  - unfold aj_y_num; apply aj_mod_range.
Qed.
