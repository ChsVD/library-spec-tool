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
From SimpleC.EE.Applications_human.simplex_rat_div Require Import simplex_rat_div_goal.
From SimpleC.EE.Applications_human.simplex_rat_div Require Import simplex_rat_div_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_checked_mul.simplex_checked_mul_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_reduce.simplex_rat_reduce_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_div.simplex_rat_div_lib.
Local Open Scope sac.

Lemma proof_of_rat_div_safety_wit_28_r_eq_x_split_goal_1 : rat_div_safety_wit_28_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HF : checked_mul_flag A_r_eq_x E_r_eq_x = 1) by lia.
  pose proof (checked_mul_success_product_range A_r_eq_x E_r_eq_x HF) as HP.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_div_safety_wit_28_r_eq_x : rat_div_safety_wit_28_r_eq_x.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_safety_wit_28_r_eq_x_split_goal_1.
Qed. 

Lemma proof_of_rat_div_safety_wit_29_out_undef_split_goal_1 : rat_div_safety_wit_29_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HF : checked_mul_flag A_out_undef E_out_undef = 1) by lia.
  pose proof (checked_mul_success_product_range A_out_undef E_out_undef HF) as HP.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_div_safety_wit_29_out_undef : rat_div_safety_wit_29_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_safety_wit_29_out_undef_split_goal_1.
Qed. 

Lemma proof_of_rat_div_safety_wit_30_out_known_split_goal_1 : rat_div_safety_wit_30_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HF : checked_mul_flag A_out_known E_out_known = 1) by lia.
  pose proof (checked_mul_success_product_range A_out_known E_out_known HF) as HP.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_div_safety_wit_30_out_known : rat_div_safety_wit_30_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_safety_wit_30_out_known_split_goal_1.
Qed. 

Lemma proof_of_rat_div_safety_wit_31_r_eq_x_split_goal_1 : rat_div_safety_wit_31_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HF : checked_mul_flag B_r_eq_x C_r_eq_x = 1) by lia.
  pose proof (checked_mul_success_product_range B_r_eq_x C_r_eq_x HF) as HP.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_div_safety_wit_31_r_eq_x : rat_div_safety_wit_31_r_eq_x.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_safety_wit_31_r_eq_x_split_goal_1.
Qed. 

Lemma proof_of_rat_div_safety_wit_32_out_undef_split_goal_1 : rat_div_safety_wit_32_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HF : checked_mul_flag B_out_undef C_out_undef = 1) by lia.
  pose proof (checked_mul_success_product_range B_out_undef C_out_undef HF) as HP.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_div_safety_wit_32_out_undef : rat_div_safety_wit_32_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_safety_wit_32_out_undef_split_goal_1.
Qed. 

Lemma proof_of_rat_div_safety_wit_33_out_known_split_goal_1 : rat_div_safety_wit_33_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HF : checked_mul_flag B_out_known C_out_known = 1) by lia.
  pose proof (checked_mul_success_product_range B_out_known C_out_known HF) as HP.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_div_safety_wit_33_out_known : rat_div_safety_wit_33_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_safety_wit_33_out_known_split_goal_1.
Qed. 

Lemma proof_of_rat_div_return_wit_1_r_eq_x_split_goal_1 : rat_div_return_wit_1_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_rat_div_return_wit_1_r_eq_x_split_goal_2 : rat_div_return_wit_1_r_eq_x_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_rat_div_result.
  assert (HS : Z.ltb (B_r_eq_x * C_r_eq_x) 0 = true) by (apply Z.ltb_lt; lia).
  rewrite HS, Z.abs_neq by lia.
  congruence.
Qed.

Lemma proof_of_rat_div_return_wit_1_r_eq_x_split_goal_3 : rat_div_return_wit_1_r_eq_x_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_div_flag_success.
  repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_1_r_eq_x : rat_div_return_wit_1_r_eq_x.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_1_r_eq_x_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_1_r_eq_x_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_1_r_eq_x_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_2_r_eq_x_split_goal_1 : rat_div_return_wit_2_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_rat_div_return_wit_2_r_eq_x_split_goal_2 : rat_div_return_wit_2_r_eq_x_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_rat_div_result.
  assert (HS : Z.ltb (B_r_eq_x * C_r_eq_x) 0 = true) by (apply Z.ltb_lt; lia).
  rewrite HS, Z.abs_neq by lia.
  congruence.
Qed.

Lemma proof_of_rat_div_return_wit_2_r_eq_x_split_goal_3 : rat_div_return_wit_2_r_eq_x_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_div_flag_success.
  repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_2_r_eq_x : rat_div_return_wit_2_r_eq_x.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_2_r_eq_x_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_2_r_eq_x_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_2_r_eq_x_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_3_r_eq_x_split_goal_1 : rat_div_return_wit_3_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(fail).
  assert (HR : simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P_2 Q_2).
  { unfold simplex_rat_div_result.
    assert (HS : Z.ltb (B_r_eq_x * C_r_eq_x) 0 = true) by (apply Z.ltb_lt; lia).
    rewrite HS, Z.abs_neq by lia.
    assumption. }
  exact (proj2 (simplex_rat_div_normalized_bridge A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x
    P_2 Q_2 ltac:(lia) ltac:(congruence) HR)).
Qed.

Lemma proof_of_rat_div_return_wit_3_r_eq_x_split_goal_2 : rat_div_return_wit_3_r_eq_x_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_rat_div_result.
  assert (HS : Z.ltb (B_r_eq_x * C_r_eq_x) 0 = true) by (apply Z.ltb_lt; lia).
  rewrite HS, Z.abs_neq by lia.
  congruence.
Qed.

Lemma proof_of_rat_div_return_wit_3_r_eq_x_split_goal_3 : rat_div_return_wit_3_r_eq_x_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_div_flag_success.
  repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_3_r_eq_x : rat_div_return_wit_3_r_eq_x.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_3_r_eq_x_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_3_r_eq_x_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_3_r_eq_x_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_4_r_eq_x_split_goal_1 : rat_div_return_wit_4_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto); nia.
Qed.

Lemma proof_of_rat_div_return_wit_4_r_eq_x_split_goal_2 : rat_div_return_wit_4_r_eq_x_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_rat_div_result.
  assert (HS : Z.ltb (B_r_eq_x * C_r_eq_x) 0 = true) by (apply Z.ltb_lt; lia).
  rewrite HS, Z.abs_neq by lia.
  congruence.
Qed.

Lemma proof_of_rat_div_return_wit_4_r_eq_x_split_goal_3 : rat_div_return_wit_4_r_eq_x_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_div_flag_success.
  repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_4_r_eq_x : rat_div_return_wit_4_r_eq_x.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_4_r_eq_x_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_4_r_eq_x_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_4_r_eq_x_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_5_out_undef_split_goal_1 : rat_div_return_wit_5_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_rat_div_return_wit_5_out_undef_split_goal_2 : rat_div_return_wit_5_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_rat_div_result.
  assert (HS : Z.ltb (B_out_undef * C_out_undef) 0 = true) by (apply Z.ltb_lt; lia).
  rewrite HS, Z.abs_neq by lia.
  congruence.
Qed.

Lemma proof_of_rat_div_return_wit_5_out_undef_split_goal_3 : rat_div_return_wit_5_out_undef_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_div_flag_success.
  repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_5_out_undef : rat_div_return_wit_5_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_5_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_5_out_undef_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_5_out_undef_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_6_out_undef_split_goal_1 : rat_div_return_wit_6_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_rat_div_return_wit_6_out_undef_split_goal_2 : rat_div_return_wit_6_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_rat_div_result.
  assert (HS : Z.ltb (B_out_undef * C_out_undef) 0 = true) by (apply Z.ltb_lt; lia).
  rewrite HS, Z.abs_neq by lia.
  congruence.
Qed.

Lemma proof_of_rat_div_return_wit_6_out_undef_split_goal_3 : rat_div_return_wit_6_out_undef_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_div_flag_success.
  repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_6_out_undef : rat_div_return_wit_6_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_6_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_6_out_undef_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_6_out_undef_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_7_out_undef_split_goal_1 : rat_div_return_wit_7_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(fail).
  assert (HR : simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef P_2 Q_2).
  { unfold simplex_rat_div_result.
    assert (HS : Z.ltb (B_out_undef * C_out_undef) 0 = true) by (apply Z.ltb_lt; lia).
    rewrite HS, Z.abs_neq by lia.
    assumption. }
  exact (proj2 (simplex_rat_div_normalized_bridge A_out_undef B_out_undef C_out_undef E_out_undef
    P_2 Q_2 ltac:(lia) ltac:(congruence) HR)).
Qed.

Lemma proof_of_rat_div_return_wit_7_out_undef_split_goal_2 : rat_div_return_wit_7_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_rat_div_result.
  assert (HS : Z.ltb (B_out_undef * C_out_undef) 0 = true) by (apply Z.ltb_lt; lia).
  rewrite HS, Z.abs_neq by lia.
  congruence.
Qed.

Lemma proof_of_rat_div_return_wit_7_out_undef_split_goal_3 : rat_div_return_wit_7_out_undef_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_div_flag_success.
  repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_7_out_undef : rat_div_return_wit_7_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_7_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_7_out_undef_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_7_out_undef_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_8_out_undef_split_goal_1 : rat_div_return_wit_8_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto); nia.
Qed.

Lemma proof_of_rat_div_return_wit_8_out_undef_split_goal_2 : rat_div_return_wit_8_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_rat_div_result.
  assert (HS : Z.ltb (B_out_undef * C_out_undef) 0 = true) by (apply Z.ltb_lt; lia).
  rewrite HS, Z.abs_neq by lia.
  congruence.
Qed.

Lemma proof_of_rat_div_return_wit_8_out_undef_split_goal_3 : rat_div_return_wit_8_out_undef_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_div_flag_success.
  repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_8_out_undef : rat_div_return_wit_8_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_8_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_8_out_undef_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_8_out_undef_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_9_out_known_split_goal_1 : rat_div_return_wit_9_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_rat_div_return_wit_9_out_known_split_goal_2 : rat_div_return_wit_9_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_rat_div_result.
  assert (HS : Z.ltb (B_out_known * C_out_known) 0 = true) by (apply Z.ltb_lt; lia).
  rewrite HS, Z.abs_neq by lia.
  congruence.
Qed.

Lemma proof_of_rat_div_return_wit_9_out_known_split_goal_3 : rat_div_return_wit_9_out_known_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_div_flag_success.
  repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_9_out_known : rat_div_return_wit_9_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_9_out_known_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_9_out_known_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_9_out_known_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_10_out_known_split_goal_1 : rat_div_return_wit_10_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_rat_div_return_wit_10_out_known_split_goal_2 : rat_div_return_wit_10_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_rat_div_result.
  assert (HS : Z.ltb (B_out_known * C_out_known) 0 = true) by (apply Z.ltb_lt; lia).
  rewrite HS, Z.abs_neq by lia.
  congruence.
Qed.

Lemma proof_of_rat_div_return_wit_10_out_known_split_goal_3 : rat_div_return_wit_10_out_known_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_div_flag_success.
  repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_10_out_known : rat_div_return_wit_10_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_10_out_known_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_10_out_known_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_10_out_known_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_11_out_known_split_goal_1 : rat_div_return_wit_11_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(fail).
  assert (HR : simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known P_2 Q_2).
  { unfold simplex_rat_div_result.
    assert (HS : Z.ltb (B_out_known * C_out_known) 0 = true) by (apply Z.ltb_lt; lia).
    rewrite HS, Z.abs_neq by lia.
    assumption. }
  exact (proj2 (simplex_rat_div_normalized_bridge A_out_known B_out_known C_out_known E_out_known
    P_2 Q_2 ltac:(lia) ltac:(congruence) HR)).
Qed.

Lemma proof_of_rat_div_return_wit_11_out_known_split_goal_2 : rat_div_return_wit_11_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_rat_div_result.
  assert (HS : Z.ltb (B_out_known * C_out_known) 0 = true) by (apply Z.ltb_lt; lia).
  rewrite HS, Z.abs_neq by lia.
  congruence.
Qed.

Lemma proof_of_rat_div_return_wit_11_out_known_split_goal_3 : rat_div_return_wit_11_out_known_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_div_flag_success.
  repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_11_out_known : rat_div_return_wit_11_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_11_out_known_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_11_out_known_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_11_out_known_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_12_out_known_split_goal_1 : rat_div_return_wit_12_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto); nia.
Qed.

Lemma proof_of_rat_div_return_wit_12_out_known_split_goal_2 : rat_div_return_wit_12_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_rat_div_result.
  assert (HS : Z.ltb (B_out_known * C_out_known) 0 = true) by (apply Z.ltb_lt; lia).
  rewrite HS, Z.abs_neq by lia.
  congruence.
Qed.

Lemma proof_of_rat_div_return_wit_12_out_known_split_goal_3 : rat_div_return_wit_12_out_known_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  symmetry. apply simplex_rat_div_flag_success.
  repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_12_out_known : rat_div_return_wit_12_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_12_out_known_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_12_out_known_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_12_out_known_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_13_r_eq_x_split_goal_1 : rat_div_return_wit_13_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_rat_div_return_wit_13_r_eq_x_split_goal_2 : rat_div_return_wit_13_r_eq_x_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. unfold simplex_rat_div_result.
  match goal with |- simplex_rat_reduce_result (if Z.ltb ?d 0 then _ else _) (Z.abs ?d) _ _ =>
    assert (HS : Z.ltb d 0 = false) by (apply Z.ltb_ge; lia);
    rewrite HS, Z.abs_eq by lia
  end.
  subst; assumption.
Qed.

Lemma proof_of_rat_div_return_wit_13_r_eq_x_split_goal_3 : rat_div_return_wit_13_r_eq_x_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry. apply simplex_rat_div_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_13_r_eq_x : rat_div_return_wit_13_r_eq_x.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_13_r_eq_x_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_13_r_eq_x_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_13_r_eq_x_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_14_r_eq_x_split_goal_1 : rat_div_return_wit_14_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_rat_div_return_wit_14_r_eq_x_split_goal_2 : rat_div_return_wit_14_r_eq_x_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. unfold simplex_rat_div_result.
  match goal with |- simplex_rat_reduce_result (if Z.ltb ?d 0 then _ else _) (Z.abs ?d) _ _ =>
    assert (HS : Z.ltb d 0 = false) by (apply Z.ltb_ge; lia);
    rewrite HS, Z.abs_eq by lia
  end.
  subst; assumption.
Qed.

Lemma proof_of_rat_div_return_wit_14_r_eq_x_split_goal_3 : rat_div_return_wit_14_r_eq_x_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry. apply simplex_rat_div_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_14_r_eq_x : rat_div_return_wit_14_r_eq_x.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_14_r_eq_x_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_14_r_eq_x_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_14_r_eq_x_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_15_r_eq_x_split_goal_1 : rat_div_return_wit_15_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. unfold simplex_rat_div_result.
  match goal with |- simplex_rat_reduce_result (if Z.ltb ?d 0 then _ else _) (Z.abs ?d) _ _ =>
    assert (HS : Z.ltb d 0 = false) by (apply Z.ltb_ge; lia);
    rewrite HS, Z.abs_eq by lia
  end.
  subst; assumption.
Qed.

Lemma proof_of_rat_div_return_wit_15_r_eq_x_split_goal_2 : rat_div_return_wit_15_r_eq_x_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry. apply simplex_rat_div_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_15_r_eq_x : rat_div_return_wit_15_r_eq_x.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_15_r_eq_x_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_15_r_eq_x_split_goal_2.
Qed. 

Lemma proof_of_rat_div_return_wit_16_r_eq_x_split_goal_1 : rat_div_return_wit_16_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. unfold simplex_rat_div_result.
  match goal with |- simplex_rat_reduce_result (if Z.ltb ?d 0 then _ else _) (Z.abs ?d) _ _ =>
    assert (HS : Z.ltb d 0 = false) by (apply Z.ltb_ge; lia);
    rewrite HS, Z.abs_eq by lia
  end.
  subst; assumption.
Qed.

Lemma proof_of_rat_div_return_wit_16_r_eq_x_split_goal_2 : rat_div_return_wit_16_r_eq_x_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry. apply simplex_rat_div_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_16_r_eq_x : rat_div_return_wit_16_r_eq_x.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_16_r_eq_x_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_16_r_eq_x_split_goal_2.
Qed. 

Lemma proof_of_rat_div_return_wit_17_out_undef_split_goal_1 : rat_div_return_wit_17_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_rat_div_return_wit_17_out_undef_split_goal_2 : rat_div_return_wit_17_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. unfold simplex_rat_div_result.
  match goal with |- simplex_rat_reduce_result (if Z.ltb ?d 0 then _ else _) (Z.abs ?d) _ _ =>
    assert (HS : Z.ltb d 0 = false) by (apply Z.ltb_ge; lia);
    rewrite HS, Z.abs_eq by lia
  end.
  subst; assumption.
Qed.

Lemma proof_of_rat_div_return_wit_17_out_undef_split_goal_3 : rat_div_return_wit_17_out_undef_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry. apply simplex_rat_div_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_17_out_undef : rat_div_return_wit_17_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_17_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_17_out_undef_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_17_out_undef_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_18_out_undef_split_goal_1 : rat_div_return_wit_18_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_rat_div_return_wit_18_out_undef_split_goal_2 : rat_div_return_wit_18_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. unfold simplex_rat_div_result.
  match goal with |- simplex_rat_reduce_result (if Z.ltb ?d 0 then _ else _) (Z.abs ?d) _ _ =>
    assert (HS : Z.ltb d 0 = false) by (apply Z.ltb_ge; lia);
    rewrite HS, Z.abs_eq by lia
  end.
  subst; assumption.
Qed.

Lemma proof_of_rat_div_return_wit_18_out_undef_split_goal_3 : rat_div_return_wit_18_out_undef_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry. apply simplex_rat_div_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_18_out_undef : rat_div_return_wit_18_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_18_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_18_out_undef_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_18_out_undef_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_19_out_undef_split_goal_1 : rat_div_return_wit_19_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. unfold simplex_rat_div_result.
  match goal with |- simplex_rat_reduce_result (if Z.ltb ?d 0 then _ else _) (Z.abs ?d) _ _ =>
    assert (HS : Z.ltb d 0 = false) by (apply Z.ltb_ge; lia);
    rewrite HS, Z.abs_eq by lia
  end.
  subst; assumption.
Qed.

Lemma proof_of_rat_div_return_wit_19_out_undef_split_goal_2 : rat_div_return_wit_19_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry. apply simplex_rat_div_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_19_out_undef : rat_div_return_wit_19_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_19_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_19_out_undef_split_goal_2.
Qed. 

Lemma proof_of_rat_div_return_wit_20_out_undef_split_goal_1 : rat_div_return_wit_20_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. unfold simplex_rat_div_result.
  match goal with |- simplex_rat_reduce_result (if Z.ltb ?d 0 then _ else _) (Z.abs ?d) _ _ =>
    assert (HS : Z.ltb d 0 = false) by (apply Z.ltb_ge; lia);
    rewrite HS, Z.abs_eq by lia
  end.
  subst; assumption.
Qed.

Lemma proof_of_rat_div_return_wit_20_out_undef_split_goal_2 : rat_div_return_wit_20_out_undef_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry. apply simplex_rat_div_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_20_out_undef : rat_div_return_wit_20_out_undef.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_20_out_undef_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_20_out_undef_split_goal_2.
Qed. 

Lemma proof_of_rat_div_return_wit_21_out_known_split_goal_1 : rat_div_return_wit_21_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_rat_div_return_wit_21_out_known_split_goal_2 : rat_div_return_wit_21_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. unfold simplex_rat_div_result.
  match goal with |- simplex_rat_reduce_result (if Z.ltb ?d 0 then _ else _) (Z.abs ?d) _ _ =>
    assert (HS : Z.ltb d 0 = false) by (apply Z.ltb_ge; lia);
    rewrite HS, Z.abs_eq by lia
  end.
  subst; assumption.
Qed.

Lemma proof_of_rat_div_return_wit_21_out_known_split_goal_3 : rat_div_return_wit_21_out_known_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry. apply simplex_rat_div_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_21_out_known : rat_div_return_wit_21_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_21_out_known_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_21_out_known_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_21_out_known_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_22_out_known_split_goal_1 : rat_div_return_wit_22_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_rat_div_return_wit_22_out_known_split_goal_2 : rat_div_return_wit_22_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. unfold simplex_rat_div_result.
  match goal with |- simplex_rat_reduce_result (if Z.ltb ?d 0 then _ else _) (Z.abs ?d) _ _ =>
    assert (HS : Z.ltb d 0 = false) by (apply Z.ltb_ge; lia);
    rewrite HS, Z.abs_eq by lia
  end.
  subst; assumption.
Qed.

Lemma proof_of_rat_div_return_wit_22_out_known_split_goal_3 : rat_div_return_wit_22_out_known_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry. apply simplex_rat_div_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_22_out_known : rat_div_return_wit_22_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_22_out_known_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_22_out_known_split_goal_2.
  - Goal_apply proof_of_rat_div_return_wit_22_out_known_split_goal_3.
Qed. 

Lemma proof_of_rat_div_return_wit_23_out_known_split_goal_1 : rat_div_return_wit_23_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. unfold simplex_rat_div_result.
  match goal with |- simplex_rat_reduce_result (if Z.ltb ?d 0 then _ else _) (Z.abs ?d) _ _ =>
    assert (HS : Z.ltb d 0 = false) by (apply Z.ltb_ge; lia);
    rewrite HS, Z.abs_eq by lia
  end.
  subst; assumption.
Qed.

Lemma proof_of_rat_div_return_wit_23_out_known_split_goal_2 : rat_div_return_wit_23_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry. apply simplex_rat_div_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_23_out_known : rat_div_return_wit_23_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_23_out_known_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_23_out_known_split_goal_2.
Qed. 

Lemma proof_of_rat_div_return_wit_24_out_known_split_goal_1 : rat_div_return_wit_24_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. unfold simplex_rat_div_result.
  match goal with |- simplex_rat_reduce_result (if Z.ltb ?d 0 then _ else _) (Z.abs ?d) _ _ =>
    assert (HS : Z.ltb d 0 = false) by (apply Z.ltb_ge; lia);
    rewrite HS, Z.abs_eq by lia
  end.
  subst; assumption.
Qed.

Lemma proof_of_rat_div_return_wit_24_out_known_split_goal_2 : rat_div_return_wit_24_out_known_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros. symmetry. apply simplex_rat_div_flag_success. repeat split; congruence.
Qed.

Lemma proof_of_rat_div_return_wit_24_out_known : rat_div_return_wit_24_out_known.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_div_return_wit_24_out_known_split_goal_1.
  - Goal_apply proof_of_rat_div_return_wit_24_out_known_split_goal_2.
Qed. 

Lemma proof_of_rat_div_return_wit_25_r_eq_x_split_goal_1 : rat_div_return_wit_25_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros.
  symmetry.
  apply (proj2 (simplex_rat_div_failure_ordered A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x)).
  right. right. repeat split; lia.
Qed.

Lemma proof_of_rat_div_return_wit_25_r_eq_x : rat_div_return_wit_25_r_eq_x.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_return_wit_25_r_eq_x_split_goal_1.
Qed. 

Lemma proof_of_rat_div_return_wit_26_out_undef_split_goal_1 : rat_div_return_wit_26_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros.
  symmetry.
  apply (proj2 (simplex_rat_div_failure_ordered A_out_undef B_out_undef C_out_undef E_out_undef)).
  right. right. repeat split; lia.
Qed.

Lemma proof_of_rat_div_return_wit_26_out_undef : rat_div_return_wit_26_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_return_wit_26_out_undef_split_goal_1.
Qed. 

Lemma proof_of_rat_div_return_wit_27_out_known_split_goal_1 : rat_div_return_wit_27_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros.
  symmetry.
  apply (proj2 (simplex_rat_div_failure_ordered A_out_known B_out_known C_out_known E_out_known)).
  right. right. repeat split; lia.
Qed.

Lemma proof_of_rat_div_return_wit_27_out_known : rat_div_return_wit_27_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_return_wit_27_out_known_split_goal_1.
Qed. 

Lemma proof_of_rat_div_return_wit_28_r_eq_x_split_goal_1 : rat_div_return_wit_28_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros.
  symmetry.
  apply (proj2 (simplex_rat_div_failure_ordered A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x)).
  right. left. split; lia.
Qed.

Lemma proof_of_rat_div_return_wit_28_r_eq_x : rat_div_return_wit_28_r_eq_x.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_return_wit_28_r_eq_x_split_goal_1.
Qed. 

Lemma proof_of_rat_div_return_wit_29_out_undef_split_goal_1 : rat_div_return_wit_29_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros.
  symmetry.
  apply (proj2 (simplex_rat_div_failure_ordered A_out_undef B_out_undef C_out_undef E_out_undef)).
  right. left. split; lia.
Qed.

Lemma proof_of_rat_div_return_wit_29_out_undef : rat_div_return_wit_29_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_return_wit_29_out_undef_split_goal_1.
Qed. 

Lemma proof_of_rat_div_return_wit_30_out_known_split_goal_1 : rat_div_return_wit_30_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros.
  symmetry.
  apply (proj2 (simplex_rat_div_failure_ordered A_out_known B_out_known C_out_known E_out_known)).
  right. left. split; lia.
Qed.

Lemma proof_of_rat_div_return_wit_30_out_known : rat_div_return_wit_30_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_return_wit_30_out_known_split_goal_1.
Qed. 

Lemma proof_of_rat_div_return_wit_31_r_eq_x_split_goal_1 : rat_div_return_wit_31_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_rat_div_return_wit_31_r_eq_x : rat_div_return_wit_31_r_eq_x.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_return_wit_31_r_eq_x_split_goal_1.
Qed. 

Lemma proof_of_rat_div_return_wit_32_out_undef_split_goal_1 : rat_div_return_wit_32_out_undef_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_rat_div_return_wit_32_out_undef : rat_div_return_wit_32_out_undef.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_return_wit_32_out_undef_split_goal_1.
Qed. 

Lemma proof_of_rat_div_return_wit_33_out_known_split_goal_1 : rat_div_return_wit_33_out_known_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_rat_div_return_wit_33_out_known : rat_div_return_wit_33_out_known.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_return_wit_33_out_known_split_goal_1.
Qed. 

Lemma proof_of_rat_div_partial_solve_wit_11_r_eq_x_pure_split_goal_1 : rat_div_partial_solve_wit_11_r_eq_x_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HF : simplex_rat_div_flag A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x = 1).
  { apply simplex_rat_div_flag_success. repeat split; lia. }
  pose proof (simplex_rat_div_reduce_inputs A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x ltac:(lia) HF) as [HN HD].
  assert (HS : Z.ltb (B_r_eq_x * C_r_eq_x) 0 = true).
  { apply Z.ltb_lt. lia. }
  rewrite HS in HN.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_div_partial_solve_wit_11_r_eq_x_pure : rat_div_partial_solve_wit_11_r_eq_x_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_partial_solve_wit_11_r_eq_x_pure_split_goal_1.
Qed. 

Lemma proof_of_rat_div_partial_solve_wit_12_out_undef_pure_split_goal_1 : rat_div_partial_solve_wit_12_out_undef_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HF : simplex_rat_div_flag A_out_undef B_out_undef C_out_undef E_out_undef = 1).
  { apply simplex_rat_div_flag_success. repeat split; lia. }
  pose proof (simplex_rat_div_reduce_inputs A_out_undef B_out_undef C_out_undef E_out_undef ltac:(lia) HF) as [HN HD].
  assert (HS : Z.ltb (B_out_undef * C_out_undef) 0 = true).
  { apply Z.ltb_lt. lia. }
  rewrite HS in HN.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_div_partial_solve_wit_12_out_undef_pure : rat_div_partial_solve_wit_12_out_undef_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_partial_solve_wit_12_out_undef_pure_split_goal_1.
Qed. 

Lemma proof_of_rat_div_partial_solve_wit_13_out_known_pure_split_goal_1 : rat_div_partial_solve_wit_13_out_known_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HF : simplex_rat_div_flag A_out_known B_out_known C_out_known E_out_known = 1).
  { apply simplex_rat_div_flag_success. repeat split; lia. }
  pose proof (simplex_rat_div_reduce_inputs A_out_known B_out_known C_out_known E_out_known ltac:(lia) HF) as [HN HD].
  assert (HS : Z.ltb (B_out_known * C_out_known) 0 = true).
  { apply Z.ltb_lt. lia. }
  rewrite HS in HN.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_div_partial_solve_wit_13_out_known_pure : rat_div_partial_solve_wit_13_out_known_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_partial_solve_wit_13_out_known_pure_split_goal_1.
Qed. 

Lemma proof_of_rat_div_partial_solve_wit_14_r_eq_x_pure_split_goal_1 : rat_div_partial_solve_wit_14_r_eq_x_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HF : simplex_rat_div_flag A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x = 1).
  { apply simplex_rat_div_flag_success. repeat split; lia. }
  pose proof (simplex_rat_div_reduce_inputs A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x ltac:(lia) HF) as [HN HD].
  assert (HS : Z.ltb (B_r_eq_x * C_r_eq_x) 0 = false).
  { apply Z.ltb_ge. lia. }
  rewrite HS in HN.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_div_partial_solve_wit_14_r_eq_x_pure : rat_div_partial_solve_wit_14_r_eq_x_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_partial_solve_wit_14_r_eq_x_pure_split_goal_1.
Qed. 

Lemma proof_of_rat_div_partial_solve_wit_15_out_undef_pure_split_goal_1 : rat_div_partial_solve_wit_15_out_undef_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HF : simplex_rat_div_flag A_out_undef B_out_undef C_out_undef E_out_undef = 1).
  { apply simplex_rat_div_flag_success. repeat split; lia. }
  pose proof (simplex_rat_div_reduce_inputs A_out_undef B_out_undef C_out_undef E_out_undef ltac:(lia) HF) as [HN HD].
  assert (HS : Z.ltb (B_out_undef * C_out_undef) 0 = false).
  { apply Z.ltb_ge. lia. }
  rewrite HS in HN.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_div_partial_solve_wit_15_out_undef_pure : rat_div_partial_solve_wit_15_out_undef_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_partial_solve_wit_15_out_undef_pure_split_goal_1.
Qed. 

Lemma proof_of_rat_div_partial_solve_wit_16_out_known_pure_split_goal_1 : rat_div_partial_solve_wit_16_out_known_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HF : simplex_rat_div_flag A_out_known B_out_known C_out_known E_out_known = 1).
  { apply simplex_rat_div_flag_success. repeat split; lia. }
  pose proof (simplex_rat_div_reduce_inputs A_out_known B_out_known C_out_known E_out_known ltac:(lia) HF) as [HN HD].
  assert (HS : Z.ltb (B_out_known * C_out_known) 0 = false).
  { apply Z.ltb_ge. lia. }
  rewrite HS in HN.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rat_div_partial_solve_wit_16_out_known_pure : rat_div_partial_solve_wit_16_out_known_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rat_div_partial_solve_wit_16_out_known_pure_split_goal_1.
Qed. 

