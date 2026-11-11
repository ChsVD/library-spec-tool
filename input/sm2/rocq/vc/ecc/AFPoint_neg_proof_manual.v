Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import AFPoint_neg_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import AFPoint_neg_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Local Open Scope sac.

Lemma proof_of_AFPoint_neg_return_wit_1_split_goal_1 : AFPoint_neg_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply Z.mod_pos_bound.
  pose proof sm2_p_gt_one.
  lia.
Qed.

Lemma proof_of_AFPoint_neg_return_wit_1_split_goal_2 : AFPoint_neg_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply Z.mod_pos_bound.
  pose proof sm2_p_gt_one.
  lia.
Qed.

Lemma proof_of_AFPoint_neg_return_wit_1_split_goal_3 : AFPoint_neg_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (sm2_p_minus_nonzero Y_non_alias ltac:(lia)) as [_ Hmod].
  destruct sm2_p_limbs as [_ [_ [_ [_ Hp]]]].
  rewrite u64_list_value_four in PreH5.
  rewrite <- Hp in PreH5.
  rewrite PreH6 in PreH5.
  assert (Hborrow : borrow = 0 \/ borrow = 1) by
    (clear - PreH3 PreH4; lia).
  destruct Hborrow as [Hborrow | Hborrow].
  - subst borrow.
    rewrite Z.mul_0_l, Z.sub_0_r in PreH5.
    rewrite <- Hmod.
    symmetry.
    exact PreH5.
  - subst borrow.
    rewrite Z.mul_1_l in PreH5.
    assert (Hpositive : 0 < SM2_P_Z - Y_non_alias) by
      (clear - PreH9 PreH16; lia).
    assert (Hnegative : S - U256_MOD < 0) by
      (clear - PreH2; lia).
    clear - PreH5 Hpositive Hnegative.
    lia.
Qed.

Lemma proof_of_AFPoint_neg_return_wit_1_split_goal_4 : AFPoint_neg_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_AFPoint_neg_return_wit_1 : AFPoint_neg_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_AFPoint_neg_return_wit_1_split_goal_1.
  Goal_apply proof_of_AFPoint_neg_return_wit_1_split_goal_2.
  Goal_apply proof_of_AFPoint_neg_return_wit_1_split_goal_3.
  Goal_apply proof_of_AFPoint_neg_return_wit_1_split_goal_4.
Qed. 

Lemma proof_of_AFPoint_neg_derive_mont_point_non_alias_by_non_alias : AFPoint_neg_derive_mont_point_non_alias_by_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : P_mont_point_non_alias <> ECInfinity |- _ =>
      rename H into Hfinite
  end.
  unfold store_mont_afpoint at 1.
  Intros X Y.
  match goal with
  | H : afpoint_represents X Y P_mont_point_non_alias |- _ =>
      rename H into Hrep
  end.
  unfold store_mont_afpoint_coords at 1.
  Intros_p HX.
  Intros_p HY.
  pose proof
    (afpoint_represents_noninfinity_y_nonzero
       X Y P_mont_point_non_alias Hrep Hfinite) as HYnonzero.
  assert (HmontYnonzero : mont_p Y <> 0).
  {
    intros Hzero.
    apply HYnonzero.
    apply (proj1 (mont_p_eq_zero_iff Y HY)).
    exact Hzero.
  }
  Exists (mont_p X) (mont_p Y).
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    unfold store_mont_afpoint, store_mont_afpoint_coords.
    Exists X Y X ((-Y) mod SM2_P_Z).
    pose proof
      (afpoint_represents_negate_noninfinity
         X Y P_mont_point_non_alias Hrep Hfinite) as Hneg.
    pose proof (Z.mod_pos_bound (-Y) SM2_P_Z ltac:(
      pose proof sm2_p_gt_one; lia)) as HnegY.
    rewrite mont_p_neg_mod.
    entailer!.
Qed. 

Lemma proof_of_AFPoint_neg_derive_point_non_alias_by_non_alias : AFPoint_neg_derive_point_non_alias_by_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : P_point_non_alias <> ECInfinity |- _ =>
      rename H into Hfinite
  end.
  unfold store_afpoint at 1.
  Intros X Y.
  match goal with
  | H : afpoint_represents X Y P_point_non_alias |- _ =>
      rename H into Hrep
  end.
  pose proof
    (afpoint_represents_noninfinity_y_nonzero
       X Y P_point_non_alias Hrep Hfinite) as HYnonzero.
  Exists X Y.
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    unfold store_afpoint.
    Exists X Y X ((-Y) mod SM2_P_Z).
    pose proof
      (afpoint_represents_negate_noninfinity
         X Y P_point_non_alias Hrep Hfinite) as Hneg.
    entailer!.
Qed. 
