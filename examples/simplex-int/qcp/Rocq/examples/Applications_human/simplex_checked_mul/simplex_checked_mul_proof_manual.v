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
From SimpleC.EE.Applications_human.simplex_checked_mul Require Import simplex_checked_mul_goal.
From SimpleC.EE.Applications_human.simplex_checked_mul Require Import simplex_checked_mul_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_checked_mul.simplex_checked_mul_lib.
Local Open Scope sac.

Lemma proof_of_checked_mul_safety_wit_73_split_goal_1 : checked_mul_safety_wit_73_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_neq by lia. rewrite Z.abs_neq by lia. exact PreH1. }
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_neq by lia; lia).
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_73_split_goal_2 : checked_mul_safety_wit_73_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_checked_mul_safety_wit_73 : checked_mul_safety_wit_73.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_73_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_73_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_safety_wit_74_split_goal_1 : checked_mul_safety_wit_74_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_neq by lia. rewrite Z.abs_neq by lia. exact PreH1. }
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_neq by lia; lia).
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_74_split_goal_2 : checked_mul_safety_wit_74_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_checked_mul_safety_wit_74 : checked_mul_safety_wit_74.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_74_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_74_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_safety_wit_75_split_goal_1 : checked_mul_safety_wit_75_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_checked_mul_safety_wit_75_split_goal_2 : checked_mul_safety_wit_75_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_eq by lia. rewrite Z.abs_neq by lia. exact PreH1. }
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_neq by lia; lia).
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_75 : checked_mul_safety_wit_75.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_75_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_75_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_safety_wit_76_split_goal_1 : checked_mul_safety_wit_76_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_checked_mul_safety_wit_76_split_goal_2 : checked_mul_safety_wit_76_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_eq by lia. rewrite Z.abs_neq by lia. exact PreH1. }
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_neq by lia; lia).
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_76 : checked_mul_safety_wit_76.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_76_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_76_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_safety_wit_77_split_goal_1 : checked_mul_safety_wit_77_split_goal_1.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_neq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_77_split_goal_2 : checked_mul_safety_wit_77_split_goal_2.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_neq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_77 : checked_mul_safety_wit_77.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_77_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_77_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_safety_wit_78_split_goal_1 : checked_mul_safety_wit_78_split_goal_1.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_neq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_78_split_goal_2 : checked_mul_safety_wit_78_split_goal_2.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_neq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_78 : checked_mul_safety_wit_78.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_78_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_78_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_safety_wit_79_split_goal_1 : checked_mul_safety_wit_79_split_goal_1.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_eq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_79_split_goal_2 : checked_mul_safety_wit_79_split_goal_2.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_eq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_79 : checked_mul_safety_wit_79.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_79_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_79_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_safety_wit_80_split_goal_1 : checked_mul_safety_wit_80_split_goal_1.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_eq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_80_split_goal_2 : checked_mul_safety_wit_80_split_goal_2.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_eq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_80 : checked_mul_safety_wit_80.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_80_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_80_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_return_wit_1_split_goal_1 : checked_mul_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- 1 = checked_mul_flag ?x ?y =>
      symmetry; exact (proj1 (checked_mul_zero_success x y ltac:(lia) ltac:(lia) ltac:(lia)))
  end.
Qed.

Lemma proof_of_checked_mul_return_wit_1 : checked_mul_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_2_split_goal_1 : checked_mul_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- 1 = checked_mul_flag ?x ?y =>
      symmetry; exact (proj1 (checked_mul_zero_success x y ltac:(lia) ltac:(lia) ltac:(lia)))
  end.
Qed.

Lemma proof_of_checked_mul_return_wit_2 : checked_mul_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_2_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_3_split_goal_1 : checked_mul_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  eapply (proj1 (checked_mul_zero_success x_pre y_pre ltac:(lia) ltac:(lia) ltac:(auto))).
Qed.

Lemma proof_of_checked_mul_return_wit_3 : checked_mul_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_3_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_4_split_goal_1 : checked_mul_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  eapply (proj1 (checked_mul_zero_success x_pre y_pre ltac:(lia) ltac:(lia) ltac:(auto))).
Qed.

Lemma proof_of_checked_mul_return_wit_4 : checked_mul_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_4_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_5_split_goal_1 : checked_mul_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_success_iff.
  split; [lia|]. split; [lia|].
  apply (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) ltac:(rewrite Z.abs_neq; lia))).
  rewrite Z.abs_neq by lia.
  rewrite Z.abs_neq by lia.
  assumption.
Qed.

Lemma proof_of_checked_mul_return_wit_5 : checked_mul_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_5_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_6_split_goal_1 : checked_mul_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_success_iff.
  split; [lia|]. split; [lia|].
  apply (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) ltac:(rewrite Z.abs_neq; lia))).
  rewrite Z.abs_neq by lia.
  rewrite Z.abs_neq by lia.
  assumption.
Qed.

Lemma proof_of_checked_mul_return_wit_6 : checked_mul_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_6_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_7_split_goal_1 : checked_mul_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_success_iff.
  split; [lia|]. split; [lia|].
  apply (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) ltac:(rewrite Z.abs_neq; lia))).
  rewrite Z.abs_eq by lia.
  rewrite Z.abs_neq by lia.
  assumption.
Qed.

Lemma proof_of_checked_mul_return_wit_7 : checked_mul_return_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_7_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_8_split_goal_1 : checked_mul_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_success_iff.
  split; [lia|]. split; [lia|].
  apply (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) ltac:(rewrite Z.abs_neq; lia))).
  rewrite Z.abs_eq by lia.
  rewrite Z.abs_neq by lia.
  assumption.
Qed.

Lemma proof_of_checked_mul_return_wit_8 : checked_mul_return_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_8_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_9_split_goal_1 : checked_mul_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_success_iff.
  split; [lia |]. split; [lia |].
  match goal with
  | |- Z.abs (?x * ?y) <= _ =>
      apply (proj1 (abs_product_quot_iff 2147483647 x y ltac:(lia) ltac:(rewrite Z.abs_eq by lia; lia)));
      rewrite (Z.abs_neq x) by lia;
      rewrite (Z.abs_eq y) by lia; assumption
  end.
Qed.

Lemma proof_of_checked_mul_return_wit_9 : checked_mul_return_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_9_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_10_split_goal_1 : checked_mul_return_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_success_iff.
  split; [lia |]. split; [lia |].
  match goal with
  | |- Z.abs (?x * ?y) <= _ =>
      apply (proj1 (abs_product_quot_iff 2147483647 x y ltac:(lia) ltac:(rewrite Z.abs_eq by lia; lia)));
      rewrite (Z.abs_neq x) by lia;
      rewrite (Z.abs_eq y) by lia; assumption
  end.
Qed.

Lemma proof_of_checked_mul_return_wit_10 : checked_mul_return_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_10_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_11_split_goal_1 : checked_mul_return_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_success_iff.
  split; [lia |]. split; [lia |].
  match goal with
  | |- Z.abs (?x * ?y) <= _ =>
      apply (proj1 (abs_product_quot_iff 2147483647 x y ltac:(lia) ltac:(rewrite Z.abs_eq by lia; lia)));
      rewrite (Z.abs_eq x) by lia;
      rewrite (Z.abs_eq y) by lia; assumption
  end.
Qed.

Lemma proof_of_checked_mul_return_wit_11 : checked_mul_return_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_11_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_12_split_goal_1 : checked_mul_return_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_success_iff.
  split; [lia |]. split; [lia |].
  match goal with
  | |- Z.abs (?x * ?y) <= _ =>
      apply (proj1 (abs_product_quot_iff 2147483647 x y ltac:(lia) ltac:(rewrite Z.abs_eq by lia; lia)));
      rewrite (Z.abs_eq x) by lia;
      rewrite (Z.abs_eq y) by lia; assumption
  end.
Qed.

Lemma proof_of_checked_mul_return_wit_12 : checked_mul_return_wit_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_12_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_13_split_goal_1 : checked_mul_return_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_failure_iff. right; right.
  apply Z.nle_gt. intro Hproduct.
  assert (Hyabs : Z.abs y_pre <> 0).
  { rewrite Z.abs_neq by lia. lia. }
  pose proof (proj2 (abs_product_quot_iff 2147483647 x_pre y_pre
    ltac:(lia) Hyabs) Hproduct) as Hquot.
  rewrite Z.abs_neq in Hquot by lia.
  rewrite Z.abs_neq in Hquot by lia.
  lia.
Qed.

Lemma proof_of_checked_mul_return_wit_13 : checked_mul_return_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_13_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_14_split_goal_1 : checked_mul_return_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_failure_iff. right; right.
  apply Z.nle_gt. intro Hproduct.
  assert (Hyabs : Z.abs y_pre <> 0).
  { rewrite Z.abs_neq by lia. lia. }
  pose proof (proj2 (abs_product_quot_iff 2147483647 x_pre y_pre
    ltac:(lia) Hyabs) Hproduct) as Hquot.
  rewrite Z.abs_neq in Hquot by lia.
  rewrite Z.abs_neq in Hquot by lia.
  lia.
Qed.

Lemma proof_of_checked_mul_return_wit_14 : checked_mul_return_wit_14.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_14_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_15_split_goal_1 : checked_mul_return_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_failure_iff. right; right.
  apply Z.nle_gt. intro Hproduct.
  assert (Hyabs : Z.abs y_pre <> 0).
  { rewrite Z.abs_neq by lia. lia. }
  pose proof (proj2 (abs_product_quot_iff 2147483647 x_pre y_pre
    ltac:(lia) Hyabs) Hproduct) as Hquot.
  rewrite Z.abs_eq in Hquot by lia.
  rewrite Z.abs_neq in Hquot by lia.
  lia.
Qed.

Lemma proof_of_checked_mul_return_wit_15 : checked_mul_return_wit_15.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_15_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_16_split_goal_1 : checked_mul_return_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_failure_iff. right; right.
  apply Z.nle_gt. intro Hproduct.
  assert (Hyabs : Z.abs y_pre <> 0).
  { rewrite Z.abs_neq by lia. lia. }
  pose proof (proj2 (abs_product_quot_iff 2147483647 x_pre y_pre
    ltac:(lia) Hyabs) Hproduct) as Hquot.
  rewrite Z.abs_eq in Hquot by lia.
  rewrite Z.abs_neq in Hquot by lia.
  lia.
Qed.

Lemma proof_of_checked_mul_return_wit_16 : checked_mul_return_wit_16.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_16_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_17_split_goal_1 : checked_mul_return_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (-x_pre > Z.quot 2147483647 y_pre) in PreH1.
  symmetry. apply checked_mul_flag_failure_iff. right; right.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hguard : Z.quot 2147483647 (Z.abs y_pre) < Z.abs x_pre).
  { rewrite Z.abs_eq by lia. rewrite Z.abs_neq by lia. lia. }
  destruct (Z_le_dec (Z.abs (x_pre*y_pre)) 2147483647) as [Hp|Hp]; [|lia].
  pose proof (proj2 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hp).
  lia.
Qed.

Lemma proof_of_checked_mul_return_wit_17 : checked_mul_return_wit_17.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_17_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_18_split_goal_1 : checked_mul_return_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (-x_pre > Z.quot 2147483647 y_pre) in PreH1.
  symmetry. apply checked_mul_flag_failure_iff. right; right.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hguard : Z.quot 2147483647 (Z.abs y_pre) < Z.abs x_pre).
  { rewrite Z.abs_eq by lia. rewrite Z.abs_neq by lia. lia. }
  destruct (Z_le_dec (Z.abs (x_pre*y_pre)) 2147483647) as [Hp|Hp]; [|lia].
  pose proof (proj2 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hp).
  lia.
Qed.

Lemma proof_of_checked_mul_return_wit_18 : checked_mul_return_wit_18.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_18_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_19_split_goal_1 : checked_mul_return_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (x_pre > Z.quot 2147483647 y_pre) in PreH1.
  symmetry. apply checked_mul_flag_failure_iff. right; right.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hguard : Z.quot 2147483647 (Z.abs y_pre) < Z.abs x_pre).
  { rewrite Z.abs_eq by lia. rewrite Z.abs_eq by lia. lia. }
  destruct (Z_le_dec (Z.abs (x_pre*y_pre)) 2147483647) as [Hp|Hp]; [|lia].
  pose proof (proj2 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hp).
  lia.
Qed.

Lemma proof_of_checked_mul_return_wit_19 : checked_mul_return_wit_19.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_19_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_20_split_goal_1 : checked_mul_return_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (x_pre > Z.quot 2147483647 y_pre) in PreH1.
  symmetry. apply checked_mul_flag_failure_iff. right; right.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hguard : Z.quot 2147483647 (Z.abs y_pre) < Z.abs x_pre).
  { rewrite Z.abs_eq by lia. rewrite Z.abs_eq by lia. lia. }
  destruct (Z_le_dec (Z.abs (x_pre*y_pre)) 2147483647) as [Hp|Hp]; [|lia].
  pose proof (proj2 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hp).
  lia.
Qed.

Lemma proof_of_checked_mul_return_wit_20 : checked_mul_return_wit_20.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_20_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_21_split_goal_1 : checked_mul_return_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_min_rejected.
  left. lia.
Qed.

Lemma proof_of_checked_mul_return_wit_21 : checked_mul_return_wit_21.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_21_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_22_split_goal_1 : checked_mul_return_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_min_rejected.
  left. lia.
Qed.

Lemma proof_of_checked_mul_return_wit_22 : checked_mul_return_wit_22.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_22_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_23_split_goal_1 : checked_mul_return_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (y_pre = -2147483648) in PreH1.
  symmetry. apply checked_mul_min_rejected. right. lia.
Qed.

Lemma proof_of_checked_mul_return_wit_23 : checked_mul_return_wit_23.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_23_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_24_split_goal_1 : checked_mul_return_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (y_pre = -2147483648) in PreH1.
  symmetry. apply checked_mul_min_rejected. right. lia.
Qed.

Lemma proof_of_checked_mul_return_wit_24 : checked_mul_return_wit_24.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_24_split_goal_1.
Qed. 

