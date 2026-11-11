From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_check Require Import simplex_check_goal.
From SimpleC.EE.Applications_human.simplex_check Require Import simplex_check_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_initialize.simplex_initialize_lib.
Require Import SimpleC.EE.Applications_human.simplex_pivot.simplex_pivot_lib.
Require Import SimpleC.EE.Applications_human.simplex_solve.simplex_solve_lib.
Require Import SimpleC.EE.Applications_human.simplex_check.simplex_check_lib.
Local Open Scope sac.

Lemma proof_of_sx_check_return_wit_5_check_rejected_coefficient_split_goal_1 : sx_check_return_wit_5_check_rejected_coefficient_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_check_return_wit_5_check_rejected_coefficient : sx_check_return_wit_5_check_rejected_coefficient.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_return_wit_5_check_rejected_coefficient_split_goal_1.
Qed.

Lemma proof_of_sx_check_return_wit_6_zero_negative_budget_split_goal_1 : sx_check_return_wit_6_zero_negative_budget_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_check_result.
  change (simplex_check_compute nil 0 N_zero_negative_budget L_zero_negative_budget =
    (-1, Some (simplex_check_initial nil 0 N_zero_negative_budget))).
  apply check_negative_compute; [lia|].
  intros i j Hi Hj. lia.
Qed.

Lemma proof_of_sx_check_return_wit_6_zero_negative_budget : sx_check_return_wit_6_zero_negative_budget.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_return_wit_6_zero_negative_budget_split_goal_1.
Qed.

Lemma proof_of_sx_check_return_wit_7_zero_normal_budget_split_goal_1 : sx_check_return_wit_7_zero_normal_budget_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_check_result in *.
  match goal with
  | H : simplex_check_compute _ 0 _ _ = _ |- _ =>
      rewrite check_zero_compute in H by lia; inversion H; subst; lia
  end.
Qed.

Lemma proof_of_sx_check_return_wit_7_zero_normal_budget : sx_check_return_wit_7_zero_normal_budget.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_return_wit_7_zero_normal_budget_split_goal_1.
Qed.

Lemma proof_of_sx_check_return_wit_8_zero_normal_budget_split_goal_1 : sx_check_return_wit_8_zero_normal_budget_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold simplex_init_return; reflexivity).
Qed.

Lemma proof_of_sx_check_return_wit_8_zero_normal_budget : sx_check_return_wit_8_zero_normal_budget.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_return_wit_8_zero_normal_budget_split_goal_1.
Qed.

Lemma proof_of_sx_check_return_wit_9_zero_normal_budget_split_goal_1 : sx_check_return_wit_9_zero_normal_budget_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_check_result in *.
  match goal with
  | H : simplex_check_compute _ 0 _ _ = _ |- _ =>
      rewrite check_zero_compute in H by lia; inversion H; subst; lia
  end.
Qed.

Lemma proof_of_sx_check_return_wit_9_zero_normal_budget : sx_check_return_wit_9_zero_normal_budget.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_return_wit_9_zero_normal_budget_split_goal_1.
Qed.

Lemma proof_of_sx_check_return_wit_10_matrix_negative_budget_split_goal_1 : sx_check_return_wit_10_matrix_negative_budget_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_check_result.
  change (simplex_check_compute A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget L_matrix_negative_budget =
    (-1, Some (simplex_check_initial A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget))).
  apply check_negative_compute; [lia|].
  intros i j Hi Hj.
  assert (HB : -2147483647 <= Znth (i*9+j) A_matrix_negative_budget 0).
  { eapply input_bound__scan_success; eauto; unfold INT_MAX in *; eauto. }
  lia.
Qed.

Lemma proof_of_sx_check_return_wit_10_matrix_negative_budget : sx_check_return_wit_10_matrix_negative_budget.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_return_wit_10_matrix_negative_budget_split_goal_1.
Qed.

Lemma proof_of_sx_check_return_wit_18_check_rejected_coefficient_split_goal_1 : sx_check_return_wit_18_check_rejected_coefficient_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_check_rejected_result.
  apply check_rejected_compute.
  exists x, y. repeat split; try lia.
Qed.

Lemma proof_of_sx_check_return_wit_18_check_rejected_coefficient : sx_check_return_wit_18_check_rejected_coefficient.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_return_wit_18_check_rejected_coefficient_split_goal_1.
Qed.

Lemma proof_of_sx_check_return_wit_19_zero_negative_budget_split_goal_1 : sx_check_return_wit_19_zero_negative_budget_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_check_result.
  change (simplex_check_compute nil 0 N_zero_negative_budget L_zero_negative_budget =
    (-1, Some (simplex_check_initial nil 0 N_zero_negative_budget))).
  apply check_negative_compute; [lia|].
  intros i j Hi Hj. lia.
Qed.

Lemma proof_of_sx_check_return_wit_19_zero_negative_budget : sx_check_return_wit_19_zero_negative_budget.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_return_wit_19_zero_negative_budget_split_goal_1.
Qed.

Lemma proof_of_sx_check_return_wit_20_zero_normal_budget : sx_check_return_wit_20_zero_normal_budget.
Proof.
  LLM_pre_process ltac:(unfold simplex_init_return in *; lia).
Qed.

Lemma proof_of_sx_check_return_wit_21_matrix_negative_budget_split_goal_1 : sx_check_return_wit_21_matrix_negative_budget_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_check_result.
  change (simplex_check_compute A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget L_matrix_negative_budget =
    (-1, Some (simplex_check_initial A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget))).
  apply check_negative_compute; [lia|].
  intros i j Hi Hj.
  assert (HB : -2147483647 <= Znth (i*9+j) A_matrix_negative_budget 0).
  { eapply input_bound__scan_success; eauto; unfold INT_MAX in *; eauto. }
  lia.
Qed.

Lemma proof_of_sx_check_return_wit_21_matrix_negative_budget : sx_check_return_wit_21_matrix_negative_budget.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_return_wit_21_matrix_negative_budget_split_goal_1.
Qed.

Lemma proof_of_sx_check_return_wit_22_matrix_normal_budget : sx_check_return_wit_22_matrix_normal_budget.
Proof.
  LLM_pre_process ltac:(unfold simplex_init_return in *; lia).
Qed.

Lemma proof_of_sx_check_partial_solve_wit_1_check_invalid_dimensions_pure_split_goal_1 : sx_check_partial_solve_wit_1_check_invalid_dimensions_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_check_invalid_dimensions.
  lia.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_1_check_invalid_dimensions_pure : sx_check_partial_solve_wit_1_check_invalid_dimensions_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_partial_solve_wit_1_check_invalid_dimensions_pure_split_goal_1.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_2_check_invalid_dimensions_pure_split_goal_1 : sx_check_partial_solve_wit_2_check_invalid_dimensions_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_check_invalid_dimensions.
  lia.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_2_check_invalid_dimensions_pure : sx_check_partial_solve_wit_2_check_invalid_dimensions_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_partial_solve_wit_2_check_invalid_dimensions_pure_split_goal_1.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_3_check_invalid_dimensions_pure_split_goal_1 : sx_check_partial_solve_wit_3_check_invalid_dimensions_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_check_invalid_dimensions.
  lia.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_3_check_invalid_dimensions_pure : sx_check_partial_solve_wit_3_check_invalid_dimensions_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_partial_solve_wit_3_check_invalid_dimensions_pure_split_goal_1.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_4_check_invalid_dimensions_pure_split_goal_1 : sx_check_partial_solve_wit_4_check_invalid_dimensions_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_check_invalid_dimensions.
  lia.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_4_check_invalid_dimensions_pure : sx_check_partial_solve_wit_4_check_invalid_dimensions_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_partial_solve_wit_4_check_invalid_dimensions_pure_split_goal_1.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_5_check_rejected_coefficient_pure : sx_check_partial_solve_wit_5_check_rejected_coefficient_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists y_2 x_2.
  split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_10_check_invalid_dimensions_pure_split_goal_1 : sx_check_partial_solve_wit_10_check_invalid_dimensions_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold simplex_init_return in *; lia).
Qed.

Lemma proof_of_sx_check_partial_solve_wit_10_check_invalid_dimensions_pure : sx_check_partial_solve_wit_10_check_invalid_dimensions_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_partial_solve_wit_10_check_invalid_dimensions_pure_split_goal_1.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_11_check_invalid_dimensions_pure_split_goal_1 : sx_check_partial_solve_wit_11_check_invalid_dimensions_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold simplex_init_return in *; lia).
Qed.

Lemma proof_of_sx_check_partial_solve_wit_11_check_invalid_dimensions_pure : sx_check_partial_solve_wit_11_check_invalid_dimensions_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_partial_solve_wit_11_check_invalid_dimensions_pure_split_goal_1.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_12_check_invalid_dimensions_pure_split_goal_1 : sx_check_partial_solve_wit_12_check_invalid_dimensions_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold simplex_init_return in *; lia).
Qed.

Lemma proof_of_sx_check_partial_solve_wit_12_check_invalid_dimensions_pure : sx_check_partial_solve_wit_12_check_invalid_dimensions_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_partial_solve_wit_12_check_invalid_dimensions_pure_split_goal_1.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_13_check_invalid_dimensions_pure_split_goal_1 : sx_check_partial_solve_wit_13_check_invalid_dimensions_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold simplex_init_return in *; lia).
Qed.

Lemma proof_of_sx_check_partial_solve_wit_13_check_invalid_dimensions_pure : sx_check_partial_solve_wit_13_check_invalid_dimensions_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_partial_solve_wit_13_check_invalid_dimensions_pure_split_goal_1.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_14_check_rejected_coefficient_pure_split_goal_1 : sx_check_partial_solve_wit_14_check_rejected_coefficient_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold simplex_init_return in *; lia).
Qed.

Lemma proof_of_sx_check_partial_solve_wit_14_check_rejected_coefficient_pure : sx_check_partial_solve_wit_14_check_rejected_coefficient_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_partial_solve_wit_14_check_rejected_coefficient_pure_split_goal_1.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_16_zero_normal_budget_pure_split_goal_1 : sx_check_partial_solve_wit_16_zero_normal_budget_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_check_partial_solve_wit_16_zero_normal_budget_pure : sx_check_partial_solve_wit_16_zero_normal_budget_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_partial_solve_wit_16_zero_normal_budget_pure_split_goal_1.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_18_matrix_normal_budget_pure_split_goal_1 : sx_check_partial_solve_wit_18_matrix_normal_budget_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros i j Hbounds.
  assert (HI : 0 <= i*9+j < Zlength A_matrix_normal_budget) by lia.
  pose proof (Forall_Znth_Zlength _ _ 0 (i*9+j) PreH25 HI) as HL.
  pose proof (Forall_Znth_Zlength _ _ 0 (i*9+j) PreH26 HI) as HU.
  lia.
Qed.

Lemma proof_of_sx_check_partial_solve_wit_18_matrix_normal_budget_pure : sx_check_partial_solve_wit_18_matrix_normal_budget_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_partial_solve_wit_18_matrix_normal_budget_pure_split_goal_1.
Qed.

Lemma proof_of_sx_solve_normal_state_entail_check_solve_initialized : sx_solve_normal_state_entail_check_solve_initialized.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename S_check_solve_initialized into s.
  rename L_check_solve_initialized into l.
  rename M_check_solve_initialized into m.
  rename N_check_solve_initialized into n.
  rename A_check_solve_initialized into a.
  subst s_pre pivot_limit_pre.
  assert (HM:0<=m<=16) by lia.
  assert (HN:0<=n<=8) by lia.
  assert (HA:forall i j,0<=i<m -> 0<=j<=n ->
    -2147483647<=Znth(i*9+j) a 0<=2147483647).
  { intros i j HI HJ.
    apply H7; repeat split; lia. }
  assert (Hnonmin:forall i j,0<=i<m -> 0<=j<=n -> Znth(i*9+j) a 0<> -2147483648).
  { intros i j HI HJ. specialize (HA i j HI HJ). lia. }
  pose proof (check_initial_normal a m n HM HN HA) as Hnormal.
  pose proof (check_initial_origin a m n HM HN) as Horigin.
  pose proof (check_initial_num_length a m n) as Hnum.
  destruct (check_list_length 400 ltac:(lia)) as [HZ400 HO400].
  destruct (check_list_length (m+n) ltac:(lia)) as [HZ HO].
  assert (HB:Zlength(simplex_init_basic n m)=m).
  { unfold simplex_init_basic. rewrite range_length__callee_bridge by lia. lia. }
  assert (HF:Zlength(simplex_init_flags n (m+n))=m+n).
  { unfold simplex_init_flags. rewrite Zlength_map,simplex_scan_range_length by lia. lia. }
  assert (HV:Zlength(simplex_init_values a m n)=m+n).
  { unfold simplex_init_values. rewrite Zlength_map,simplex_scan_range_length by lia. lia. }
  Exists s l m n (m+n) a
    (simplex_check_initial_num a m n) (simplex_init_ones 400)
    (simplex_init_basic n m) (simplex_init_flags n (m+n))
    (simplex_init_zeroes (m+n)) (simplex_init_flags n (m+n))
    (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))
    (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))
    (simplex_init_values a m n) (simplex_init_ones (m+n)).
  sep_apply_l_atomic (check_init_vars_solver s a m n HM HN).
  sep_apply_l_atomic (check_init_rows_solver s a m n HM HN).
  split_pure_spatial.
  2: { split_pures; dump_pre_spatial; try assumption; try lia. }
  cancel.
  Intros_r retval.
  apply derivable1_wand_sepcon_adjoint.
  Split.
  - Intros on od ob oib ovn ovd.
    Left. Exists on od ob oib ovn ovd.
    split_pure_spatial; [sepcon_right_assoc; cancel; reflexivity | split_pures; dump_pre_spatial; try assumption;
      eapply check_solver_composition; eauto].
  - Split.
    + Intros on od ob oib ovn ovd.
      Right. Left. Exists on od ob oib ovn ovd.
      split_pure_spatial; [sepcon_right_assoc; cancel; reflexivity | split_pures; dump_pre_spatial; try assumption;
        eapply check_solver_composition; eauto].
    + Intros on od ob oib ovn ovd.
      Right. Right. Exists on od ob oib ovn ovd.
      split_pure_spatial; [sepcon_right_assoc; cancel; reflexivity | split_pures; dump_pre_spatial; try assumption;
        eapply check_solver_composition; eauto].
Qed.

Lemma proof_of_sx_initialize_initialized_matrix_non_alias_entail_check_init_matrix : sx_initialize_initialized_matrix_non_alias_entail_check_init_matrix.
Proof.
LLM_pre_process ltac:(lia || int_auto).
Exists A_check_init_matrix M_check_init_matrix N_check_init_matrix S_check_init_matrix C_check_init_matrix.
sep_apply_l_atomic (check_old_initialize_matrix S_check_init_matrix M_check_init_matrix N_check_init_matrix Old_check_init_matrix A_check_init_matrix ltac:(lia) ltac:(lia)).
split_pure_spatial.
- cancel.
  Intros_r retval.
  apply_sepcon_adjoint.
  Intros_p HR.
  split_pure_spatial.
  + cancel; reflexivity.
  + split_pures; dump_pre_spatial; assumption.
- split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_initialize_zero_rows_entail_check_init_zero : sx_initialize_zero_rows_entail_check_init_zero.
Proof.
LLM_pre_process ltac:(lia || int_auto).
Exists N_check_init_zero S_check_init_zero C_check_init_zero.
sep_apply_l_atomic (check_old_initialize S_check_init_zero 0 N_check_init_zero Old_check_init_zero ltac:(lia) ltac:(lia)).
split_pure_spatial.
- cancel.
  Intros_r retval.
  apply_sepcon_adjoint.
  Intros_p HR.
  split_pure_spatial.
  + cancel; reflexivity.
  + split_pures; dump_pre_spatial; assumption.
- split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_initialize_invalid_dimensions_entail_check_init_invalid : sx_initialize_invalid_dimensions_entail_check_init_invalid.
Proof.
LLM_pre_process ltac:(lia || int_auto).
Exists (@nil Z) M_check_init_invalid N_check_init_invalid S_check_init_invalid C_check_init_invalid.
sep_apply_r_atomic (init_identity_wand__initialize_adapters 0).
elim_emp.
unfold simplex_check_invalid_dimensions in H3.
destruct H3 as [Hbad | [Hbad | [Hbad | Hbad]]].
- Left. split_pure_spatial; [cancel; reflexivity | split_pures; dump_pre_spatial; lia].
- Right. Left. split_pure_spatial; [cancel; reflexivity | split_pures; dump_pre_spatial; lia].
- Right. Right. Left. split_pure_spatial; [cancel; reflexivity | split_pures; dump_pre_spatial; lia].
- Right. Right. Right. split_pure_spatial; [cancel; reflexivity | split_pures; dump_pre_spatial; lia].
Qed.
