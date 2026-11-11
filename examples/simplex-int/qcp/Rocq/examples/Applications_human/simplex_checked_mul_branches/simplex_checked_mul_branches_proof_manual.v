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
From SimpleC.EE.Applications_human.simplex_checked_mul_branches Require Import simplex_checked_mul_branches_goal.
From SimpleC.EE.Applications_human.simplex_checked_mul_branches Require Import simplex_checked_mul_branches_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_checked_mul.simplex_checked_mul_lib.
Local Open Scope sac.

Lemma proof_of_checked_mul_safety_wit_73_out_known_split_goal_1 : checked_mul_safety_wit_73_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_neq by lia. rewrite Z.abs_neq by lia. exact PreH1. }
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_neq by lia; lia).
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_73_out_known_split_goal_2 : checked_mul_safety_wit_73_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_checked_mul_safety_wit_73_out_known : checked_mul_safety_wit_73_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_73_out_known_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_73_out_known_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_safety_wit_74_out_undef_split_goal_1 : checked_mul_safety_wit_74_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_neq by lia. rewrite Z.abs_neq by lia. exact PreH1. }
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_neq by lia; lia).
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_74_out_undef_split_goal_2 : checked_mul_safety_wit_74_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_checked_mul_safety_wit_74_out_undef : checked_mul_safety_wit_74_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_74_out_undef_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_74_out_undef_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_safety_wit_75_out_known_split_goal_1 : checked_mul_safety_wit_75_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_checked_mul_safety_wit_75_out_known_split_goal_2 : checked_mul_safety_wit_75_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_eq by lia. rewrite Z.abs_neq by lia. exact PreH1. }
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_neq by lia; lia).
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_75_out_known : checked_mul_safety_wit_75_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_75_out_known_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_75_out_known_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_safety_wit_76_out_undef_split_goal_1 : checked_mul_safety_wit_76_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_checked_mul_safety_wit_76_out_undef_split_goal_2 : checked_mul_safety_wit_76_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_eq by lia. rewrite Z.abs_neq by lia. exact PreH1. }
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_neq by lia; lia).
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_76_out_undef : checked_mul_safety_wit_76_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_76_out_undef_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_76_out_undef_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_safety_wit_77_out_known_split_goal_1 : checked_mul_safety_wit_77_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_neq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_77_out_known_split_goal_2 : checked_mul_safety_wit_77_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_neq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_77_out_known : checked_mul_safety_wit_77_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_77_out_known_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_77_out_known_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_safety_wit_78_out_undef_split_goal_1 : checked_mul_safety_wit_78_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_neq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_78_out_undef_split_goal_2 : checked_mul_safety_wit_78_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_neq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_78_out_undef : checked_mul_safety_wit_78_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_78_out_undef_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_78_out_undef_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_safety_wit_79_out_known_split_goal_1 : checked_mul_safety_wit_79_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_eq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_79_out_known_split_goal_2 : checked_mul_safety_wit_79_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_eq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_79_out_known : checked_mul_safety_wit_79_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_79_out_known_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_79_out_known_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_safety_wit_80_out_undef_split_goal_1 : checked_mul_safety_wit_80_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_eq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_80_out_undef_split_goal_2 : checked_mul_safety_wit_80_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial.
  assert (Hy : Z.abs y_pre <> 0) by (rewrite Z.abs_eq; lia).
  assert (Hg : Z.abs x_pre <= Z.quot 2147483647 (Z.abs y_pre)).
  { rewrite Z.abs_eq, Z.abs_eq by lia. exact PreH1. }
  pose proof (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) Hy) Hg) as Hp.
  apply Z.abs_le in Hp. lia.
Qed.

Lemma proof_of_checked_mul_safety_wit_80_out_undef : checked_mul_safety_wit_80_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_checked_mul_safety_wit_80_out_undef_split_goal_1.
  - Goal_apply proof_of_checked_mul_safety_wit_80_out_undef_split_goal_2.
Qed. 

Lemma proof_of_checked_mul_return_wit_1_out_undef_split_goal_1 : checked_mul_return_wit_1_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- 1 = checked_mul_flag ?x ?y =>
      symmetry; exact (proj1 (checked_mul_zero_success x y ltac:(lia) ltac:(lia) ltac:(lia)))
  end.
Qed.

Lemma proof_of_checked_mul_return_wit_1_out_undef : checked_mul_return_wit_1_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_1_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_2_out_known_split_goal_1 : checked_mul_return_wit_2_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | |- 1 = checked_mul_flag ?x ?y =>
      symmetry; exact (proj1 (checked_mul_zero_success x y ltac:(lia) ltac:(lia) ltac:(lia)))
  end.
Qed.

Lemma proof_of_checked_mul_return_wit_2_out_known : checked_mul_return_wit_2_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_2_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_3_out_undef_split_goal_1 : checked_mul_return_wit_3_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  eapply (proj1 (checked_mul_zero_success x_pre y_pre ltac:(lia) ltac:(lia) ltac:(auto))).
Qed.

Lemma proof_of_checked_mul_return_wit_3_out_undef : checked_mul_return_wit_3_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_3_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_4_out_known_split_goal_1 : checked_mul_return_wit_4_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry.
  eapply (proj1 (checked_mul_zero_success x_pre y_pre ltac:(lia) ltac:(lia) ltac:(auto))).
Qed.

Lemma proof_of_checked_mul_return_wit_4_out_known : checked_mul_return_wit_4_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_4_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_5_out_known_split_goal_1 : checked_mul_return_wit_5_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_success_iff.
  split; [lia|]. split; [lia|].
  apply (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) ltac:(rewrite Z.abs_neq; lia))).
  rewrite Z.abs_neq by lia.
  rewrite Z.abs_neq by lia.
  assumption.
Qed.

Lemma proof_of_checked_mul_return_wit_5_out_known : checked_mul_return_wit_5_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_5_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_6_out_undef_split_goal_1 : checked_mul_return_wit_6_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_success_iff.
  split; [lia|]. split; [lia|].
  apply (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) ltac:(rewrite Z.abs_neq; lia))).
  rewrite Z.abs_neq by lia.
  rewrite Z.abs_neq by lia.
  assumption.
Qed.

Lemma proof_of_checked_mul_return_wit_6_out_undef : checked_mul_return_wit_6_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_6_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_7_out_known_split_goal_1 : checked_mul_return_wit_7_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_success_iff.
  split; [lia|]. split; [lia|].
  apply (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) ltac:(rewrite Z.abs_neq; lia))).
  rewrite Z.abs_eq by lia.
  rewrite Z.abs_neq by lia.
  assumption.
Qed.

Lemma proof_of_checked_mul_return_wit_7_out_known : checked_mul_return_wit_7_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_7_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_8_out_undef_split_goal_1 : checked_mul_return_wit_8_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_flag_success_iff.
  split; [lia|]. split; [lia|].
  apply (proj1 (abs_product_quot_iff 2147483647 x_pre y_pre ltac:(lia) ltac:(rewrite Z.abs_neq; lia))).
  rewrite Z.abs_eq by lia.
  rewrite Z.abs_neq by lia.
  assumption.
Qed.

Lemma proof_of_checked_mul_return_wit_8_out_undef : checked_mul_return_wit_8_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_8_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_9_out_known_split_goal_1 : checked_mul_return_wit_9_out_known_split_goal_1.
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

Lemma proof_of_checked_mul_return_wit_9_out_known : checked_mul_return_wit_9_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_9_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_10_out_undef_split_goal_1 : checked_mul_return_wit_10_out_undef_split_goal_1.
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

Lemma proof_of_checked_mul_return_wit_10_out_undef : checked_mul_return_wit_10_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_10_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_11_out_known_split_goal_1 : checked_mul_return_wit_11_out_known_split_goal_1.
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

Lemma proof_of_checked_mul_return_wit_11_out_known : checked_mul_return_wit_11_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_11_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_12_out_undef_split_goal_1 : checked_mul_return_wit_12_out_undef_split_goal_1.
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

Lemma proof_of_checked_mul_return_wit_12_out_undef : checked_mul_return_wit_12_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_12_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_13_out_known_split_goal_1 : checked_mul_return_wit_13_out_known_split_goal_1.
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

Lemma proof_of_checked_mul_return_wit_13_out_known : checked_mul_return_wit_13_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_13_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_14_out_undef_split_goal_1 : checked_mul_return_wit_14_out_undef_split_goal_1.
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

Lemma proof_of_checked_mul_return_wit_14_out_undef : checked_mul_return_wit_14_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_14_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_15_out_known_split_goal_1 : checked_mul_return_wit_15_out_known_split_goal_1.
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

Lemma proof_of_checked_mul_return_wit_15_out_known : checked_mul_return_wit_15_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_15_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_16_out_undef_split_goal_1 : checked_mul_return_wit_16_out_undef_split_goal_1.
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

Lemma proof_of_checked_mul_return_wit_16_out_undef : checked_mul_return_wit_16_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_16_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_17_out_known_split_goal_1 : checked_mul_return_wit_17_out_known_split_goal_1.
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

Lemma proof_of_checked_mul_return_wit_17_out_known : checked_mul_return_wit_17_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_17_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_18_out_undef_split_goal_1 : checked_mul_return_wit_18_out_undef_split_goal_1.
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

Lemma proof_of_checked_mul_return_wit_18_out_undef : checked_mul_return_wit_18_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_18_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_19_out_known_split_goal_1 : checked_mul_return_wit_19_out_known_split_goal_1.
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

Lemma proof_of_checked_mul_return_wit_19_out_known : checked_mul_return_wit_19_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_19_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_20_out_undef_split_goal_1 : checked_mul_return_wit_20_out_undef_split_goal_1.
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

Lemma proof_of_checked_mul_return_wit_20_out_undef : checked_mul_return_wit_20_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_20_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_21_out_undef_split_goal_1 : checked_mul_return_wit_21_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_min_rejected.
  left. lia.
Qed.

Lemma proof_of_checked_mul_return_wit_21_out_undef : checked_mul_return_wit_21_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_21_out_undef_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_22_out_known_split_goal_1 : checked_mul_return_wit_22_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply checked_mul_min_rejected.
  left. lia.
Qed.

Lemma proof_of_checked_mul_return_wit_22_out_known : checked_mul_return_wit_22_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_22_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_23_out_known_split_goal_1 : checked_mul_return_wit_23_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (y_pre = -2147483648) in PreH1.
  symmetry. apply checked_mul_min_rejected. right. lia.
Qed.

Lemma proof_of_checked_mul_return_wit_23_out_known : checked_mul_return_wit_23_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_23_out_known_split_goal_1.
Qed. 

Lemma proof_of_checked_mul_return_wit_24_out_undef_split_goal_1 : checked_mul_return_wit_24_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (y_pre = -2147483648) in PreH1.
  symmetry. apply checked_mul_min_rejected. right. lia.
Qed.

Lemma proof_of_checked_mul_return_wit_24_out_undef : checked_mul_return_wit_24_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_checked_mul_return_wit_24_out_undef_split_goal_1.
Qed. 

