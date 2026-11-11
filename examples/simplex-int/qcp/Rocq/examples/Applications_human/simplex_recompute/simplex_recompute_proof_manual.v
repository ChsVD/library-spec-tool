From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_recompute Require Import simplex_recompute_goal.
From SimpleC.EE.Applications_human.simplex_recompute Require Import simplex_recompute_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_rat_mul.simplex_rat_mul_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_add.simplex_rat_add_lib.
Require Import SimpleC.EE.Applications_human.simplex_recompute.simplex_recompute_lib.
Local Open Scope sac.

Lemma proof_of_sx_recompute_entail_wit_1_recompute : sx_recompute_entail_wit_1_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst s_pre. Exists VD_recompute VN_recompute.
 unfold UndefStructPredSxRat. split_pure_spatial.
 - csimpl. sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   reflexivity.
Qed.

Lemma proof_of_sx_recompute_entail_wit_3_recompute : sx_recompute_entail_wit_3_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists CD_2 CN_2. split_pure_spatial.
 - sep_apply_l_atomic (rhs_focus__entry_focus S_recompute R_recompute RN_recompute RD_recompute i ltac:(lia)).
   unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_sx_recompute_entail_wit_4_recompute : sx_recompute_entail_wit_4_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists (Znth i RD_recompute 0) (Znth i RN_recompute 0) CD_2 CN_2.
 pose proof (forall_nth__entry_focus (Z.le (-INT_MAX)) RN_recompute i PreH16 ltac:(lia)) as HNL.
 pose proof (forall_nth__entry_focus (Z.ge INT_MAX) RN_recompute i PreH17 ltac:(lia)) as HNU.
 pose proof (forall_nth__entry_focus (Z.le 1) RD_recompute i PreH18 ltac:(lia)) as HDL.
 pose proof (forall_nth__entry_focus (Z.ge INT_MAX) RD_recompute i PreH19 ltac:(lia)) as HDU.
 split_pure_spatial.
 - csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end.
   sep_apply_r_atomic (rhs_merge__entry_focus S_recompute R_recompute RN_recompute RD_recompute i ltac:(lia)).
   unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia;
   reflexivity.
Qed.

Lemma proof_of_sx_recompute_entail_wit_5_recompute : sx_recompute_entail_wit_5_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists D_2 N_2 CD_2 CN_2. split_pure_spatial.
 - sep_apply_l_atomic (matrix_focus__entry_focus S_recompute R_recompute V_recompute AN_recompute AD_recompute i j ltac:(lia) ltac:(lia)).
   sep_apply_l_atomic (values_focus__entry_focus S_recompute V_recompute CN_2 CD_2 j ltac:(lia)).
   unfold simplex_recompute_cell, simplex_scan_rat_memory. replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by ring. csimpl. sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_sx_recompute_entail_wit_6_1_recompute : sx_recompute_entail_wit_6_1_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists Q_2 P_2 CD_2 CN_2.
 split_pure_spatial.
 - sep_apply (store_int_undef_store_int (&(( &( "product" ) )->ₛ "num")) P).
   sep_apply (store_int_undef_store_int (&(( &( "product" ) )->ₛ "den")) Q).
   sep_apply_r_atomic (matrix_merge__column_success S_recompute R_recompute V_recompute AN_recompute AD_recompute i j ltac:(lia) ltac:(lia)).
   sep_apply_r_atomic (values_merge__column_success S_recompute V_recompute CN_2 CD_2 j ltac:(lia)).
   unfold simplex_recompute_cell, simplex_scan_rat_memory.
   replace (24 * sizeof("SxRat")) with (sizeof("SxRat") * 24) by ring.
   sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?PP ** _] => progress (cancel PP) end end.
   csimpl.
   sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?PP ** _] => progress (cancel PP) end end.
   try reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   eapply column_success_step__column_success; eauto; lia.
Qed.

Lemma proof_of_sx_recompute_entail_wit_6_2_recompute : sx_recompute_entail_wit_6_2_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists Q_2 P_2 CD_2 CN_2.
 split_pure_spatial.
 - sep_apply (store_int_undef_store_int (&(( &( "product" ) )->ₛ "num")) P).
   sep_apply (store_int_undef_store_int (&(( &( "product" ) )->ₛ "den")) Q).
   sep_apply_r_atomic (matrix_merge__column_success S_recompute R_recompute V_recompute AN_recompute AD_recompute i j ltac:(lia) ltac:(lia)).
   sep_apply_r_atomic (values_merge__column_success S_recompute V_recompute CN_2 CD_2 j ltac:(lia)).
   unfold simplex_recompute_cell, simplex_scan_rat_memory.
   replace (24 * sizeof("SxRat")) with (sizeof("SxRat") * 24) by ring.
   sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?PP ** _] => progress (cancel PP) end end.
   csimpl.
   sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?PP ** _] => progress (cancel PP) end end.
   try reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   eapply column_success_step__column_success; eauto; lia.
Qed.

Lemma proof_of_sx_recompute_entail_wit_6_3_recompute : sx_recompute_entail_wit_6_3_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists Q_2 P_2 CD_2 CN_2.
 split_pure_spatial.
 - sep_apply (store_int_undef_store_int (&(( &( "product" ) )->ₛ "num")) P).
   sep_apply (store_int_undef_store_int (&(( &( "product" ) )->ₛ "den")) Q).
   sep_apply_r_atomic (matrix_merge__column_success S_recompute R_recompute V_recompute AN_recompute AD_recompute i j ltac:(lia) ltac:(lia)).
   sep_apply_r_atomic (values_merge__column_success S_recompute V_recompute CN_2 CD_2 j ltac:(lia)).
   unfold simplex_recompute_cell, simplex_scan_rat_memory.
   replace (24 * sizeof("SxRat")) with (sizeof("SxRat") * 24) by ring.
   sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?PP ** _] => progress (cancel PP) end end.
   csimpl.
   sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?PP ** _] => progress (cancel PP) end end.
   try reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   eapply column_success_step__column_success; eauto; lia.
Qed.

Lemma proof_of_sx_recompute_entail_wit_6_4_recompute : sx_recompute_entail_wit_6_4_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists Q_2 P_2 CD_2 CN_2.
 split_pure_spatial.
 - sep_apply (store_int_undef_store_int (&(( &( "product" ) )->ₛ "num")) P).
   sep_apply (store_int_undef_store_int (&(( &( "product" ) )->ₛ "den")) Q).
   sep_apply_r_atomic (matrix_merge__column_success S_recompute R_recompute V_recompute AN_recompute AD_recompute i j ltac:(lia) ltac:(lia)).
   sep_apply_r_atomic (values_merge__column_success S_recompute V_recompute CN_2 CD_2 j ltac:(lia)).
   unfold simplex_recompute_cell, simplex_scan_rat_memory.
   replace (24 * sizeof("SxRat")) with (sizeof("SxRat") * 24) by ring.
   sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?PP ** _] => progress (cancel PP) end end.
   csimpl.
   sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?PP ** _] => progress (cancel PP) end end.
   try reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   eapply column_success_step__column_success; eauto; lia.
Qed.

Lemma proof_of_sx_recompute_entail_wit_6_5_recompute : sx_recompute_entail_wit_6_5_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists D_2 N_2 CD_2 CN_2.
 split_pure_spatial.
 -    replace (24 * sizeof("SxRat")) with (sizeof("SxRat") * 24) by ring.
   sepcon_right_assoc.
   sep_apply_r_atomic (matrix_merge__skip_bounds S_recompute R_recompute V_recompute AN_recompute AD_recompute i j ltac:(lia) ltac:(lia)).
   sep_apply_r_atomic (values_merge__skip_bounds S_recompute V_recompute CN_2 CD_2 j ltac:(lia)).
   unfold simplex_recompute_cell, simplex_scan_rat_memory.
   csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end.
   reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   eapply row_skip__skip_bounds; [lia| |eassumption].
   left; assumption.
Qed.

Lemma proof_of_sx_recompute_entail_wit_6_6_recompute : sx_recompute_entail_wit_6_6_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists D_2 N_2 CD_2 CN_2.
 split_pure_spatial.
 -    replace (24 * sizeof("SxRat")) with (sizeof("SxRat") * 24) by ring.
   sepcon_right_assoc.
   sep_apply_r_atomic (matrix_merge__skip_bounds S_recompute R_recompute V_recompute AN_recompute AD_recompute i j ltac:(lia) ltac:(lia)).
   sep_apply_r_atomic (values_merge__skip_bounds S_recompute V_recompute CN_2 CD_2 j ltac:(lia)).
   unfold simplex_recompute_cell, simplex_scan_rat_memory.
   csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end.
   reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   eapply row_skip__skip_bounds; [lia| |eassumption].
   right; assumption.
Qed.

Lemma proof_of_sx_recompute_entail_wit_7_recompute : sx_recompute_entail_wit_7_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (E : j = V_recompute) by lia. subst j.
 Exists D_2 N_2 CD_2 CN_2. split_pure_spatial.
 - sep_apply (IntArray.full_split_to_missing_i &((S_recompute) # "SxState" ->ₛ "basic") i R_recompute B_recompute 0 ltac:(lia)).
   sep_apply (values_focus__row_commit S_recompute V_recompute CN_2 CD_2 (Znth i B_recompute 0) ltac:(auto)).
   unfold simplex_scan_rat_memory. cancel. csimpl. cancel.
 - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_recompute_entail_wit_8_recompute : sx_recompute_entail_wit_8_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists (replace_Znth (Znth i B_recompute 0) D CD_2) (replace_Znth (Znth i B_recompute 0) N CN_2).
 split_pure_spatial.
 - sep_apply (IntArray.missing_i_merge_to_full &((S_recompute) # "SxState" ->ₛ "basic") i R_recompute (Znth i B_recompute 0) B_recompute ltac:(lia)).
   rewrite replace_Znth_Znth.
   sep_apply_r_atomic (values_store__row_commit S_recompute V_recompute CN_2 CD_2 (Znth i B_recompute 0) N D ltac:(auto) ltac:(auto) ltac:(auto)).
   unfold simplex_scan_rat_memory.
   sep_apply (store_int_undef_store_int &( "j" ) V_recompute).
   sep_apply (store_int_undef_store_int &(&( "sum" ) ->ₛ "num") N).
   sep_apply (store_int_undef_store_int &(&( "sum" ) ->ₛ "den") D).
   cancel. csimpl. cancel.
 - split_pures; dump_pre_spatial; try lia; try assumption;
   try (apply forall_replace__row_commit; auto); try (rewrite Zlength_replace_Znth; auto).
   all: try lia.
   unfold simplex_recompute_prefix in *.
   rewrite simplex_recompute_compute_step by lia.
   match goal with H : simplex_recompute_compute _ _ _ _ _ _ _ _ _ _ = _ |- _ => rewrite H end.
   unfold simplex_recompute_commit. unfold simplex_recompute_sum in *.
   match goal with H : simplex_recompute_row _ _ _ _ _ _ _ _ _ = _ |- _ => rewrite H end. reflexivity.
Qed.

Lemma proof_of_sx_recompute_return_wit_2_recompute_split_goal_1 : sx_recompute_return_wit_2_recompute_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (i = R_recompute) by lia. subst i. assumption.
Qed.

Lemma proof_of_sx_recompute_return_wit_2_recompute : sx_recompute_return_wit_2_recompute.
Proof.
 aggressive_pre_process. Goal_apply proof_of_sx_recompute_return_wit_2_recompute_split_goal_1.
Qed.

Lemma proof_of_sx_recompute_return_wit_3_recompute : sx_recompute_return_wit_3_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists CD CN. split_pure_spatial.
 - sepcon_right_assoc.
   sep_apply_r_atomic (matrix_merge__failure_exit S_recompute R_recompute V_recompute AN_recompute AD_recompute i j ltac:(lia) ltac:(lia)).
   sep_apply_r_atomic (values_merge__failure_exit S_recompute V_recompute CN CD j ltac:(lia)).
   unfold simplex_recompute_cell, simplex_scan_rat_memory.
   assert (HS:24*sizeof("SxRat")=sizeof("SxRat")*24) by ring.
   rewrite HS. csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?T ** _] => progress (cancel T) end end.
   reflexivity.
 - split_pures; dump_pre_spatial; try assumption.
   unfold simplex_recompute_prefix, simplex_recompute_sum in *.
   eapply (compute_failure_suffix__failure_exit IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i R_recompute V_recompute CN CD); [lia|eassumption|].
   eapply (row_failure_suffix__failure_exit IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j V_recompute N D); [lia|eassumption|].
   eapply column_add_fail__failure_exit; eauto; lia.
Qed.

Lemma proof_of_sx_recompute_return_wit_4_recompute : sx_recompute_return_wit_4_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists CD CN. split_pure_spatial.
 - sepcon_right_assoc.
   sep_apply_r_atomic (matrix_merge__failure_exit S_recompute R_recompute V_recompute AN_recompute AD_recompute i j ltac:(lia) ltac:(lia)).
   sep_apply_r_atomic (values_merge__failure_exit S_recompute V_recompute CN CD j ltac:(lia)).
   unfold simplex_recompute_cell, simplex_scan_rat_memory.
   assert (HS:24*sizeof("SxRat")=sizeof("SxRat")*24) by ring.
   rewrite HS. csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?T ** _] => progress (cancel T) end end.
   reflexivity.
 - split_pures; dump_pre_spatial; try assumption.
   unfold simplex_recompute_prefix, simplex_recompute_sum in *.
   eapply (compute_failure_suffix__failure_exit IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i R_recompute V_recompute CN CD); [lia|eassumption|].
   eapply (row_failure_suffix__failure_exit IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j V_recompute N D); [lia|eassumption|].
   eapply column_add_fail__failure_exit; eauto; lia.
Qed.

Lemma proof_of_sx_recompute_return_wit_5_recompute : sx_recompute_return_wit_5_recompute.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists CD CN. split_pure_spatial.
 - sepcon_right_assoc.
   sep_apply_r_atomic (matrix_merge__failure_exit S_recompute R_recompute V_recompute AN_recompute AD_recompute i j ltac:(lia) ltac:(lia)).
   sep_apply_r_atomic (values_merge__failure_exit S_recompute V_recompute CN CD j ltac:(lia)).
   unfold simplex_recompute_cell, simplex_scan_rat_memory.
   assert (HS:24*sizeof("SxRat")=sizeof("SxRat")*24) by ring.
   rewrite HS. csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?T ** _] => progress (cancel T) end end.
   reflexivity.
 - split_pures; dump_pre_spatial; try assumption.
   unfold simplex_recompute_prefix, simplex_recompute_sum in *.
   eapply (compute_failure_suffix__failure_exit IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i R_recompute V_recompute CN CD); [lia|eassumption|].
   eapply (row_failure_suffix__failure_exit IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j V_recompute N D); [lia|eassumption|].
   eapply column_mul_fail__failure_exit; eauto; lia.
Qed.

Lemma proof_of_sx_recompute_partial_solve_wit_3_recompute_pure_split_goal_1 : sx_recompute_partial_solve_wit_3_recompute_pure_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 eapply (forall_nth__skip_bounds (Z.le 1) AD_recompute (i*24+j)); [eassumption|].
 nia.
Qed.

Lemma proof_of_sx_recompute_partial_solve_wit_3_recompute_pure_split_goal_2 : sx_recompute_partial_solve_wit_3_recompute_pure_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 eapply (forall_nth__skip_bounds (Z.le 1) CD j); [eassumption|].
 nia.
Qed.

Lemma proof_of_sx_recompute_partial_solve_wit_3_recompute_pure : sx_recompute_partial_solve_wit_3_recompute_pure.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_recompute_partial_solve_wit_3_recompute_pure_split_goal_1.
 - Goal_apply proof_of_sx_recompute_partial_solve_wit_3_recompute_pure_split_goal_2.
Qed.

