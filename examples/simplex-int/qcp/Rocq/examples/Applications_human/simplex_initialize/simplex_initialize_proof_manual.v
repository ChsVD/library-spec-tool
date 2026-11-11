From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_initialize Require Import simplex_initialize_goal.
From SimpleC.EE.Applications_human.simplex_initialize Require Import simplex_initialize_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_rat_zero.simplex_rat_zero_lib.
Require Import SimpleC.EE.Applications_human.simplex_recompute.simplex_recompute_lib.
Require Import SimpleC.EE.Applications_human.simplex_initialize.simplex_initialize_lib.
Local Open Scope sac.

Lemma proof_of_sx_initialize_entail_wit_1_rejected_coefficient : sx_initialize_entail_wit_1_rejected_coefficient.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 try subst s_pre; try subst rows_pre; try subst inputs_pre; try subst c_pre.
 Exists y_3 x_3. split_pure_spatial.
 - csimpl. sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.

Qed.

Lemma proof_of_sx_initialize_entail_wit_2_initialized_matrix_non_alias_split_goal_1 : sx_initialize_entail_wit_2_initialized_matrix_non_alias_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 all: try (dump_pre_spatial).
 all: cbn in *.
 all: firstorder lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_2_initialized_matrix_non_alias : sx_initialize_entail_wit_2_initialized_matrix_non_alias.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_initialize_entail_wit_2_initialized_matrix_non_alias_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_entail_wit_3_zero_rows_split_goal_1 : sx_initialize_entail_wit_3_zero_rows_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_initialize_entail_wit_3_zero_rows : sx_initialize_entail_wit_3_zero_rows.
Proof.
 aggressive_pre_process. Goal_apply proof_of_sx_initialize_entail_wit_3_zero_rows_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_entail_wit_4_rejected_coefficient : sx_initialize_entail_wit_4_rejected_coefficient.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 Exists y_4 x_4. split_pure_spatial.
 - sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   intros x y Hxy. apply PreH16. tauto || lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_5_initialized_matrix_non_alias_split_goal_1 : sx_initialize_entail_wit_5_initialized_matrix_non_alias_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 apply PreH11. lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_5_initialized_matrix_non_alias : sx_initialize_entail_wit_5_initialized_matrix_non_alias.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_initialize_entail_wit_5_initialized_matrix_non_alias_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_entail_wit_6_rejected_coefficient : sx_initialize_entail_wit_6_rejected_coefficient.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 Exists y_4 x_4. split_pure_spatial.
 - unfold simplex_init_input_cell. sep_apply_r_atomic (input_focus__scan_reject C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j ltac:(lia) ltac:(lia)). csimpl. sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; assumption || lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_7_initialized_matrix_non_alias_split_goal_1 : sx_initialize_entail_wit_7_initialized_matrix_non_alias_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 all: dump_pre_spatial; exact PreH14.
Qed.

Lemma proof_of_sx_initialize_entail_wit_7_initialized_matrix_non_alias_split_goal_spatial : sx_initialize_entail_wit_7_initialized_matrix_non_alias_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 sep_apply_l_atomic (input_focus__scan_success C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j ltac:(lia) ltac:(lia)).
 cancel (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias+N_initialized_matrix_non_alias) A_initialized_matrix_non_alias 0).
 cancel (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias+N_initialized_matrix_non_alias)).
 unfold simplex_init_input_cell. replace (sizeof(INT)*9) with (9*sizeof(INT)) by ring. csimpl. sepcon_right_assoc.
 repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
Qed.

Lemma proof_of_sx_initialize_entail_wit_7_initialized_matrix_non_alias : sx_initialize_entail_wit_7_initialized_matrix_non_alias.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_initialize_entail_wit_7_initialized_matrix_non_alias_split_goal_spatial.
 - Goal_apply proof_of_sx_initialize_entail_wit_7_initialized_matrix_non_alias_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_entail_wit_8_rejected_coefficient : sx_initialize_entail_wit_8_rejected_coefficient.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 exfalso. apply (PreH16 x_2 y_2); repeat split; auto; lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_9_rejected_coefficient : sx_initialize_entail_wit_9_rejected_coefficient.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 Exists y_4 x_4. split_pure_spatial.
 - sep_apply_l_atomic (store_int_undef_store_int ( &( "j" ) ) j). sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   intros x y Hxy. apply PreH19. intuition lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_10_initialized_matrix_non_alias_split_goal_1 : sx_initialize_entail_wit_10_initialized_matrix_non_alias_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 apply PreH14. lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_10_initialized_matrix_non_alias : sx_initialize_entail_wit_10_initialized_matrix_non_alias.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_initialize_entail_wit_10_initialized_matrix_non_alias_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_entail_wit_11_initialized_matrix_non_alias_split_goal_1 : sx_initialize_entail_wit_11_initialized_matrix_non_alias_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. intros x y HH.
 destruct (Z.eq_dec x i) as [EqX|EqX].
 - subst x. destruct (Z.eq_dec y j) as [EqY|EqY].
   + subst y. exact PreH3.
   + apply PreH17. lia.
 - apply PreH17. lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_11_initialized_matrix_non_alias_split_goal_spatial : sx_initialize_entail_wit_11_initialized_matrix_non_alias_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 sepcon_right_assoc.
 sep_apply_r_atomic (input_merge__scan_success C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j ltac:(lia) ltac:(lia)).
 cancel (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias+N_initialized_matrix_non_alias) A_initialized_matrix_non_alias 0).
 cancel (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias+N_initialized_matrix_non_alias)).
 unfold simplex_init_input_cell. replace (sizeof(INT)*9) with (9*sizeof(INT)) by ring. csimpl. sepcon_right_assoc.
 repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
Qed.

Lemma proof_of_sx_initialize_entail_wit_11_initialized_matrix_non_alias : sx_initialize_entail_wit_11_initialized_matrix_non_alias.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_initialize_entail_wit_11_initialized_matrix_non_alias_split_goal_spatial.
 - Goal_apply proof_of_sx_initialize_entail_wit_11_initialized_matrix_non_alias_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_entail_wit_12_rejected_coefficient : sx_initialize_entail_wit_12_rejected_coefficient.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 Exists y_3 x_3. split_pure_spatial.
 - unfold simplex_init_input_cell. sepcon_right_assoc.
   sep_apply_r_atomic (input_merge__scan_reject C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j ltac:(lia) ltac:(lia)). csimpl. sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   intros x y Hxy. destruct (Z.eq_dec x i); subst.
   + destruct (Z.eq_dec y j); subst; [int_auto|apply PreH20; intuition lia].
   + apply PreH20; intuition lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_13_rejected_coefficient_split_goal_1 : sx_initialize_entail_wit_13_rejected_coefficient_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_13_rejected_coefficient_split_goal_2 : sx_initialize_entail_wit_13_rejected_coefficient_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_13_rejected_coefficient_split_goal_3 : sx_initialize_entail_wit_13_rejected_coefficient_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_13_rejected_coefficient : sx_initialize_entail_wit_13_rejected_coefficient.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_initialize_entail_wit_13_rejected_coefficient_split_goal_1.
  - Goal_apply proof_of_sx_initialize_entail_wit_13_rejected_coefficient_split_goal_2.
  - Goal_apply proof_of_sx_initialize_entail_wit_13_rejected_coefficient_split_goal_3.
Qed.

Lemma proof_of_sx_initialize_entail_wit_16_initialized_matrix_non_alias : sx_initialize_entail_wit_16_initialized_matrix_non_alias.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 split_pure_spatial.
 - sep_apply_l_atomic (vars_focus__vars_success S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias+N_initialized_matrix_non_alias) A_initialized_matrix_non_alias j ltac:(lia)).
   unfold simplex_init_var. rewrite Z.ltb_irrefl.
   unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_initialize_entail_wit_17_rejected_coefficient : sx_initialize_entail_wit_17_rejected_coefficient.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_18_zero_rows : sx_initialize_entail_wit_18_zero_rows.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 split_pure_spatial.
 - replace (0+N_zero_rows) with N_zero_rows by lia.
   sep_apply_l_atomic (vars_focus__zero_rows S_zero_rows N_zero_rows j ltac:(lia)).
   unfold simplex_init_var. rewrite Z.ltb_irrefl.
   unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_19_zero_rows_split_goal_spatial : sx_initialize_entail_wit_19_zero_rows_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 replace (0+N_zero_rows) with N_zero_rows by lia.
 sep_apply_r_atomic (vars_step__zero_rows S_zero_rows N_zero_rows j ltac:(lia)).
 unfold simplex_init_var. assert (E:(Z.ltb j (j+1)%Z)=true) by (apply Z.ltb_lt;lia).
 rewrite E,zero_flag__zero_rows. simpl.
 unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
 repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
Qed.

Lemma proof_of_sx_initialize_entail_wit_19_zero_rows : sx_initialize_entail_wit_19_zero_rows.
Proof.
 aggressive_pre_process. Goal_apply proof_of_sx_initialize_entail_wit_19_zero_rows_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_20_initialized_matrix_non_alias_split_goal_spatial : sx_initialize_entail_wit_20_initialized_matrix_non_alias_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sepcon_right_assoc.
 sep_apply_r_atomic (vars_step__vars_success S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias+N_initialized_matrix_non_alias) A_initialized_matrix_non_alias j ltac:(lia)).
 unfold simplex_init_var. assert(E:Z.ltb j (j+1)=true) by (apply Z.ltb_lt;lia).
 rewrite E,zero_flag__vars_success. simpl.
 unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
 repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
Qed.

Lemma proof_of_sx_initialize_entail_wit_20_initialized_matrix_non_alias : sx_initialize_entail_wit_20_initialized_matrix_non_alias.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_initialize_entail_wit_20_initialized_matrix_non_alias_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_21_rejected_coefficient_split_goal_spatial : sx_initialize_entail_wit_21_rejected_coefficient_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_21_rejected_coefficient : sx_initialize_entail_wit_21_rejected_coefficient.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_entail_wit_21_rejected_coefficient_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_22_zero_rows_split_goal_spatial : sx_initialize_entail_wit_22_zero_rows_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (j=0+N_zero_rows) by lia. subst j. reflexivity.
Qed.

Lemma proof_of_sx_initialize_entail_wit_22_zero_rows : sx_initialize_entail_wit_22_zero_rows.
Proof.
 aggressive_pre_process. Goal_apply proof_of_sx_initialize_entail_wit_22_zero_rows_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_23_initialized_matrix_non_alias_split_goal_spatial : sx_initialize_entail_wit_23_initialized_matrix_non_alias_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(E:j=M_initialized_matrix_non_alias+N_initialized_matrix_non_alias) by lia.
 rewrite E. reflexivity.
Qed.

Lemma proof_of_sx_initialize_entail_wit_23_initialized_matrix_non_alias : sx_initialize_entail_wit_23_initialized_matrix_non_alias.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_initialize_entail_wit_23_initialized_matrix_non_alias_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_24_rejected_coefficient_split_goal_spatial : sx_initialize_entail_wit_24_rejected_coefficient_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_24_rejected_coefficient : sx_initialize_entail_wit_24_rejected_coefficient.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_entail_wit_24_rejected_coefficient_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_25_initialized_matrix_non_alias : sx_initialize_entail_wit_25_initialized_matrix_non_alias.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_l_atomic (input_focus__row_setup C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 ltac:(lia) ltac:(lia)).
 sep_apply_l_atomic (vars_focus__row_setup S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias+N_initialized_matrix_non_alias) A_initialized_matrix_non_alias i ltac:(lia) ltac:(lia) ltac:(lia)).
 sep_apply_l_atomic (rows_focus__row_setup S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias+N_initialized_matrix_non_alias) ltac:(lia)).
 unfold simplex_init_var,simplex_init_row,simplex_init_input_cell,simplex_scan_rat_memory.
 assert(E:(Z.ltb (N_initialized_matrix_non_alias+i) (M_initialized_matrix_non_alias+N_initialized_matrix_non_alias))=true) by (apply Z.ltb_lt;lia).
 rewrite E,Z.ltb_irrefl. try rewrite Bool.andb_false_r. simpl.
 split_pure_spatial.
 - replace (9*sizeof(INT)) with (sizeof(INT)*9) by ring.
   replace (i*9+0) with (i*9) by ring.
   replace (sizeof(INT)) with 4 by reflexivity. csimpl. repeat rewrite Z.ltb_irrefl. repeat rewrite Bool.andb_false_r. simpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; auto;lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_26_rejected_coefficient : sx_initialize_entail_wit_26_rejected_coefficient.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_27_initialized_matrix_non_alias_split_goal_spatial : sx_initialize_entail_wit_27_initialized_matrix_non_alias_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst b.
 sepcon_right_assoc.
 sep_apply_r_atomic (input_merge__row_setup C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 ltac:(lia) ltac:(lia)).
 sep_apply_r_atomic (vars_mark__row_setup S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias+N_initialized_matrix_non_alias) A_initialized_matrix_non_alias i ltac:(lia) ltac:(lia) ltac:(lia)).
 unfold simplex_init_var,simplex_init_input_cell,simplex_scan_rat_memory.
 assert(E:(Z.ltb (N_initialized_matrix_non_alias+i) (M_initialized_matrix_non_alias+N_initialized_matrix_non_alias))=true) by (apply Z.ltb_lt;lia).
 assert(F:(Z.leb N_initialized_matrix_non_alias (N_initialized_matrix_non_alias+i))=true) by (apply Z.leb_le;lia).
 assert(G:(Z.ltb (N_initialized_matrix_non_alias+i) (N_initialized_matrix_non_alias+(i+1)))=true) by (apply Z.ltb_lt;lia).
 rewrite E,F,G. simpl.
 replace (9*sizeof(INT)) with (sizeof(INT)*9) by ring.
 replace (i*9+0) with (i*9) by ring.
 replace (sizeof(INT)) with 4 by reflexivity. csimpl. repeat rewrite Z.ltb_irrefl. repeat rewrite Bool.andb_false_r. simpl. sepcon_right_assoc.
 repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
Qed.

Lemma proof_of_sx_initialize_entail_wit_27_initialized_matrix_non_alias : sx_initialize_entail_wit_27_initialized_matrix_non_alias.
Proof. aggressive_pre_process. Goal_apply proof_of_sx_initialize_entail_wit_27_initialized_matrix_non_alias_split_goal_spatial. Qed.

Lemma proof_of_sx_initialize_entail_wit_28_rejected_coefficient_split_goal_spatial : sx_initialize_entail_wit_28_rejected_coefficient_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_28_rejected_coefficient : sx_initialize_entail_wit_28_rejected_coefficient.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_entail_wit_28_rejected_coefficient_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_29_initialized_matrix_non_alias : sx_initialize_entail_wit_29_initialized_matrix_non_alias.
Proof.
LLM_pre_process ltac:(lia || int_auto).
rename S_initialized_matrix_non_alias into s; rename C_initialized_matrix_non_alias into c; rename M_initialized_matrix_non_alias into m; rename N_initialized_matrix_non_alias into n; rename A_initialized_matrix_non_alias into a.
split_pure_spatial.
- sep_apply_l_atomic (a_focus__matrix_steps s a n i j (m+n) ltac:(lia)).
 unfold simplex_init_a_undef. replace (24*sizeof("SxRat")) with (sizeof("SxRat")*24) by ring.
 csimpl. sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
- split_pures; dump_pre_spatial; auto.

Qed.

Lemma proof_of_sx_initialize_entail_wit_30_rejected_coefficient : sx_initialize_entail_wit_30_rejected_coefficient.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_31_initialized_matrix_non_alias_split_goal_spatial : sx_initialize_entail_wit_31_initialized_matrix_non_alias_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
rename S_initialized_matrix_non_alias into s; rename C_initialized_matrix_non_alias into c; rename M_initialized_matrix_non_alias into m; rename N_initialized_matrix_non_alias into n; rename A_initialized_matrix_non_alias into a.
sep_apply_l_atomic (input_focus__matrix_steps c a m n i (j+1) ltac:(lia) ltac:(lia)).
unfold simplex_init_input_cell. replace (sizeof(INT)*9) with (9*sizeof(INT)) by ring.
replace (i*9+(j+1)) with (i*9+j+1) by ring.
csimpl. sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
Qed.

Lemma proof_of_sx_initialize_entail_wit_31_initialized_matrix_non_alias : sx_initialize_entail_wit_31_initialized_matrix_non_alias.
Proof.
aggressive_pre_process.
Goal_apply proof_of_sx_initialize_entail_wit_31_initialized_matrix_non_alias_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_32_rejected_coefficient_split_goal_spatial : sx_initialize_entail_wit_32_rejected_coefficient_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_32_rejected_coefficient : sx_initialize_entail_wit_32_rejected_coefficient.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_entail_wit_32_rejected_coefficient_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_33_1_rejected_coefficient_split_goal_spatial : sx_initialize_entail_wit_33_1_rejected_coefficient_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_33_1_rejected_coefficient : sx_initialize_entail_wit_33_1_rejected_coefficient.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_entail_wit_33_1_rejected_coefficient_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_33_2_rejected_coefficient_split_goal_spatial : sx_initialize_entail_wit_33_2_rejected_coefficient_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_33_2_rejected_coefficient : sx_initialize_entail_wit_33_2_rejected_coefficient.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_entail_wit_33_2_rejected_coefficient_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_34_1_initialized_matrix_non_alias_split_goal_spatial : sx_initialize_entail_wit_34_1_initialized_matrix_non_alias_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
rename S_initialized_matrix_non_alias into s; rename C_initialized_matrix_non_alias into c; rename M_initialized_matrix_non_alias into m; rename N_initialized_matrix_non_alias into n; rename A_initialized_matrix_non_alias into a.
sepcon_right_assoc.
pose proof (input_merge__matrix_steps c a m n i (j+1) ltac:(lia) ltac:(lia)) as HI.
unfold simplex_init_input_cell in HI. revert HI. replace (sizeof(INT)*9) with (9*sizeof(INT)) by ring. csimpl. intros HI.
replace (i*9+j+1) with (i*9+(j+1)) by ring.
csimpl. sepcon_right_assoc. sep_apply_r_atomic HI.
assert (E:(j <? n)%Z=true) by (apply Z.ltb_lt;lia).
pose proof (matrix_prefix_step__matrix_steps s a n i j (m+n) ltac:(lia)) as HS.
unfold simplex_init_a_cell, simplex_init_coeff in HS. rewrite E in HS. revert HS. csimpl. intros HS.
sepcon_right_assoc. sep_apply_r_atomic HS.
replace (24*sizeof("SxRat")) with (sizeof("SxRat")*24) by ring.
replace (i*9+(j+1)) with (i*9+j+1) by ring.
csimpl. sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
Qed.

Lemma proof_of_sx_initialize_entail_wit_34_1_initialized_matrix_non_alias : sx_initialize_entail_wit_34_1_initialized_matrix_non_alias.
Proof.
aggressive_pre_process.
Goal_apply proof_of_sx_initialize_entail_wit_34_1_initialized_matrix_non_alias_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_34_2_initialized_matrix_non_alias_split_goal_spatial : sx_initialize_entail_wit_34_2_initialized_matrix_non_alias_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
rename S_initialized_matrix_non_alias into s; rename C_initialized_matrix_non_alias into c; rename M_initialized_matrix_non_alias into m; rename N_initialized_matrix_non_alias into n; rename A_initialized_matrix_non_alias into a.
assert (E:(j <? n)%Z=false) by (apply Z.ltb_ge;lia).
pose proof (matrix_prefix_step__matrix_steps s a n i j (m+n) ltac:(lia)) as HS.
unfold simplex_init_a_cell, simplex_init_coeff in HS. rewrite E in HS. revert HS. csimpl. intros HS.
sepcon_right_assoc. sep_apply_r_atomic HS.
replace (24*sizeof("SxRat")) with (sizeof("SxRat")*24) by ring.
csimpl. sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
Qed.

Lemma proof_of_sx_initialize_entail_wit_34_2_initialized_matrix_non_alias : sx_initialize_entail_wit_34_2_initialized_matrix_non_alias.
Proof.
aggressive_pre_process.
Goal_apply proof_of_sx_initialize_entail_wit_34_2_initialized_matrix_non_alias_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_35_rejected_coefficient_split_goal_spatial : sx_initialize_entail_wit_35_rejected_coefficient_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_35_rejected_coefficient : sx_initialize_entail_wit_35_rejected_coefficient.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_entail_wit_35_rejected_coefficient_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_36_initialized_matrix_non_alias_split_goal_spatial : sx_initialize_entail_wit_36_initialized_matrix_non_alias_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
rename S_initialized_matrix_non_alias into s; rename C_initialized_matrix_non_alias into c; rename M_initialized_matrix_non_alias into m; rename N_initialized_matrix_non_alias into n; rename A_initialized_matrix_non_alias into a.
assert (EJ:j=m+n) by lia. subst j.
pose proof (row_finish__matrix_steps s a n i m (m+n) ltac:(lia)) as HS.
unfold simplex_init_row at 1 in HS.
assert (EI:(i <? i+1)%Z=true) by (apply Z.ltb_lt;lia). rewrite EI in HS.
unfold simplex_scan_rat_memory in HS. revert HS. csimpl. intros HS.
sepcon_right_assoc. sep_apply_r_atomic HS.
csimpl. sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
Qed.

Lemma proof_of_sx_initialize_entail_wit_36_initialized_matrix_non_alias : sx_initialize_entail_wit_36_initialized_matrix_non_alias.
Proof.
aggressive_pre_process.
Goal_apply proof_of_sx_initialize_entail_wit_36_initialized_matrix_non_alias_split_goal_spatial.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_1 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. intros k HK.
 assert (E: In (Znth k (simplex_init_basic N_initialized_matrix_non_alias M_initialized_matrix_non_alias) 0)
 (Zrange N_initialized_matrix_non_alias (N_initialized_matrix_non_alias+M_initialized_matrix_non_alias))).
 { apply Znth_In_Zlength. unfold simplex_init_basic. rewrite range_length__callee_bridge; lia. }
 apply In_Zrange in E. lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_2 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_an, simplex_init_ones, simplex_init_zeroes, simplex_init_rhs.
 rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_3 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_an, simplex_init_ones, simplex_init_zeroes, simplex_init_rhs.
 rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_4 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_4.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_an, simplex_init_ones, simplex_init_zeroes, simplex_init_rhs.
 rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_5 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_5.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_an, simplex_init_ones, simplex_init_zeroes, simplex_init_rhs.
 rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_6 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_6.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_an, simplex_init_ones, simplex_init_zeroes, simplex_init_rhs.
 rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_7 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_7.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_an, simplex_init_ones, simplex_init_zeroes, simplex_init_rhs.
 rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_8 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_8.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_ones, simplex_init_zeroes.
 apply Forall_forall. intros x HX. apply in_map_iff in HX. destruct HX as [k [<- HK]]. int_auto.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_9 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_9.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_ones, simplex_init_zeroes.
 apply Forall_forall. intros x HX. apply in_map_iff in HX. destruct HX as [k [<- HK]]. int_auto.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_10 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_10.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_ones, simplex_init_zeroes.
 apply Forall_forall. intros x HX. apply in_map_iff in HX. destruct HX as [k [<- HK]]. int_auto.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_11 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_11.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_ones, simplex_init_zeroes.
 apply Forall_forall. intros x HX. apply in_map_iff in HX. destruct HX as [k [<- HK]]. int_auto.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_12 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_12.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_ones, simplex_init_zeroes.
 apply Forall_forall. intros x HX. apply in_map_iff in HX. destruct HX as [k [<- HK]]. int_auto.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_13 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_13.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_ones, simplex_init_zeroes.
 apply Forall_forall. intros x HX. apply in_map_iff in HX. destruct HX as [k [<- HK]]. int_auto.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_14 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_14.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_rhs. apply Forall_forall. intros x HX.
 apply in_map_iff in HX. destruct HX as [k [<- HK]]. apply In_Zrange in HK.
 pose proof (bounds_nth__callee_bridge A_initialized_matrix_non_alias (k*9) PreH7 PreH8 ltac:(rewrite PreH6; lia)) as HB.
 int_auto.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_15 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_15.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_rhs. apply Forall_forall. intros x HX.
 apply in_map_iff in HX. destruct HX as [k [<- HK]]. apply In_Zrange in HK.
 pose proof (bounds_nth__callee_bridge A_initialized_matrix_non_alias (k*9) PreH7 PreH8 ltac:(rewrite PreH6; lia)) as HB.
 int_auto.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_16 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_16.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_ones, simplex_init_zeroes.
 apply Forall_forall. intros x HX. apply in_map_iff in HX. destruct HX as [k [<- HK]]. int_auto.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_17 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_17.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_ones, simplex_init_zeroes.
 apply Forall_forall. intros x HX. apply in_map_iff in HX. destruct HX as [k [<- HK]]. int_auto.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_18 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_18.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_an. apply Forall_forall. intros x HX.
 apply in_map_iff in HX. destruct HX as [k [<- HK]]. apply In_Zrange in HK.
 pose proof (Z.mod_pos_bound k 24 ltac:(lia)) as HM.
 pose proof (Z.div_mod k 24 ltac:(lia)) as HD.
 pose proof (coeff_bounds__callee_bridge A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias (k/24) (k mod 24) ltac:(lia) ltac:(lia) PreH6 PreH7 PreH8 ltac:(nia) HM) as HB.
 int_auto.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_19 : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_19.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_init_an. apply Forall_forall. intros x HX.
 apply in_map_iff in HX. destruct HX as [k [<- HK]]. apply In_Zrange in HK.
 pose proof (Z.mod_pos_bound k 24 ltac:(lia)) as HM.
 pose proof (Z.div_mod k 24 ltac:(lia)) as HD.
 pose proof (coeff_bounds__callee_bridge A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias (k/24) (k mod 24) ltac:(lia) ltac:(lia) PreH6 PreH7 PreH8 ltac:(nia) HM) as HB.
 int_auto.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_spatial : sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 assert(E:i=M_initialized_matrix_non_alias) by lia. subst i.
 replace (M_initialized_matrix_non_alias+N_initialized_matrix_non_alias) with (N_initialized_matrix_non_alias+M_initialized_matrix_non_alias) by lia.
 sepcon_right_assoc.
 sep_apply_l_atomic (vars_to_recompute__callee_bridge S_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias ltac:(lia) ltac:(lia)).
 sep_apply_l_atomic (rows_to_recompute__callee_bridge S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias (N_initialized_matrix_non_alias+M_initialized_matrix_non_alias) ltac:(lia) ltac:(lia)).
 csimpl. sepcon_right_assoc.
 repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
Qed.

Lemma proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias : sx_initialize_entail_wit_37_initialized_matrix_non_alias.
Proof.
aggressive_pre_process.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_spatial.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_1.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_2.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_3.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_4.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_5.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_6.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_7.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_8.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_9.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_10.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_11.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_12.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_13.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_14.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_15.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_16.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_17.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_18.
 - Goal_apply proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_19.

Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_1 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_2 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_3 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_4 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_5 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_6 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_7 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_8 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_9 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_10 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_11 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_12 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_13 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_14 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_15 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_16 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_17 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_18 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_19 : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_spatial : sx_initialize_entail_wit_38_rejected_coefficient_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto);
  unfold simplex_init_unreachable in *; contradiction.
Qed.

Lemma proof_of_sx_initialize_entail_wit_38_rejected_coefficient : sx_initialize_entail_wit_38_rejected_coefficient.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_spatial.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_1.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_2.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_3.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_4.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_5.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_6.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_7.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_8.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_9.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_10.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_11.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_12.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_13.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_14.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_15.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_16.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_17.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_18.
  - Goal_apply proof_of_sx_initialize_entail_wit_38_rejected_coefficient_split_goal_19.
Qed.

Lemma proof_of_sx_initialize_return_wit_1_zero_rows_split_goal_1 : sx_initialize_return_wit_1_zero_rows_split_goal_1.
Proof.
 LLM_pre_process ltac:(unfold simplex_init_return; lia || int_auto).
Qed.

Lemma proof_of_sx_initialize_return_wit_1_zero_rows_split_goal_spatial : sx_initialize_return_wit_1_zero_rows_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(i=0) by lia. subst i. replace (0+N_zero_rows) with N_zero_rows by lia.
 rewrite vars_finish__zero_rows. reflexivity.
Qed.

Lemma proof_of_sx_initialize_return_wit_1_zero_rows : sx_initialize_return_wit_1_zero_rows.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_initialize_return_wit_1_zero_rows_split_goal_spatial.
 - Goal_apply proof_of_sx_initialize_return_wit_1_zero_rows_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_return_wit_2_initialized_matrix_non_alias_split_goal_1 : sx_initialize_return_wit_2_initialized_matrix_non_alias_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 pose proof (closed__final_result A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias retval ON OD PreH8 PreH10 ltac:(lia) PreH15 PreH16 PreH19 PreH20 PreH7) as [HR [HON HOD]].
 unfold simplex_init_return. dump_pre_spatial. exact HR.
Qed.

Lemma proof_of_sx_initialize_return_wit_2_initialized_matrix_non_alias_split_goal_spatial : sx_initialize_return_wit_2_initialized_matrix_non_alias_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 pose proof (closed__final_result A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias retval ON OD PreH8 PreH10 ltac:(lia) PreH15 PreH16 PreH19 PreH20 PreH7) as [HR [HON HOD]].
 subst ON OD. sepcon_right_assoc.
 sep_apply_r_atomic (vars_pack__final_result S_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias PreH8 PreH10).
 sepcon_right_assoc.
 sep_apply_r_atomic (rows_pack__final_result S_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias PreH8 PreH10 ltac:(lia)).
 csimpl. sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _]=>progress(cancel P) end end. reflexivity.
Qed.

Lemma proof_of_sx_initialize_return_wit_2_initialized_matrix_non_alias : sx_initialize_return_wit_2_initialized_matrix_non_alias.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_initialize_return_wit_2_initialized_matrix_non_alias_split_goal_spatial.
 - Goal_apply proof_of_sx_initialize_return_wit_2_initialized_matrix_non_alias_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_return_wit_3_rejected_coefficient_split_goal_1 : sx_initialize_return_wit_3_rejected_coefficient_split_goal_1.
Proof.
 LLM_pre_process ltac:(unfold simplex_init_unreachable in *; contradiction).
Qed.

Lemma proof_of_sx_initialize_return_wit_3_rejected_coefficient_split_goal_spatial : sx_initialize_return_wit_3_rejected_coefficient_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(unfold simplex_init_unreachable in *; contradiction).
Qed.

Lemma proof_of_sx_initialize_return_wit_3_rejected_coefficient : sx_initialize_return_wit_3_rejected_coefficient.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_initialize_return_wit_3_rejected_coefficient_split_goal_spatial.
 - Goal_apply proof_of_sx_initialize_return_wit_3_rejected_coefficient_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_return_wit_4_initialized_matrix_non_alias_split_goal_1 : sx_initialize_return_wit_4_initialized_matrix_non_alias_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 pose proof (input_bound__scan_success A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PreH10) as HB.
 cbn in *. exfalso. lia.
Qed.

Lemma proof_of_sx_initialize_return_wit_4_initialized_matrix_non_alias_split_goal_spatial : sx_initialize_return_wit_4_initialized_matrix_non_alias_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 pose proof (input_bound__scan_success A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PreH10) as HB.
 cbn in *. exfalso. lia.
Qed.

Lemma proof_of_sx_initialize_return_wit_4_initialized_matrix_non_alias : sx_initialize_return_wit_4_initialized_matrix_non_alias.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_initialize_return_wit_4_initialized_matrix_non_alias_split_goal_spatial.
 - Goal_apply proof_of_sx_initialize_return_wit_4_initialized_matrix_non_alias_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_return_wit_5_rejected_coefficient_split_goal_1 : sx_initialize_return_wit_5_rejected_coefficient_split_goal_1.
Proof.
 LLM_pre_process ltac:(unfold simplex_init_return; reflexivity).
Qed.

Lemma proof_of_sx_initialize_return_wit_5_rejected_coefficient_split_goal_spatial : sx_initialize_return_wit_5_rejected_coefficient_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 replace (9*sizeof(INT)) with (sizeof(INT)*9) by ring.
 sep_apply_r_atomic (input_merge__rejected_returns C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 unfold simplex_init_input_cell. cancel.
Qed.

Lemma proof_of_sx_initialize_return_wit_5_rejected_coefficient : sx_initialize_return_wit_5_rejected_coefficient.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_initialize_return_wit_5_rejected_coefficient_split_goal_spatial.
 - Goal_apply proof_of_sx_initialize_return_wit_5_rejected_coefficient_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_return_wit_6_invalid_dimensions_split_goal_1 : sx_initialize_return_wit_6_invalid_dimensions_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_init_return; reflexivity.
Qed.

Lemma proof_of_sx_initialize_return_wit_6_invalid_dimensions : sx_initialize_return_wit_6_invalid_dimensions.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_return_wit_6_invalid_dimensions_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_return_wit_7_invalid_dimensions_split_goal_1 : sx_initialize_return_wit_7_invalid_dimensions_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_init_return; reflexivity.
Qed.

Lemma proof_of_sx_initialize_return_wit_7_invalid_dimensions : sx_initialize_return_wit_7_invalid_dimensions.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_return_wit_7_invalid_dimensions_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_return_wit_8_invalid_dimensions_split_goal_1 : sx_initialize_return_wit_8_invalid_dimensions_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_init_return; reflexivity.
Qed.

Lemma proof_of_sx_initialize_return_wit_8_invalid_dimensions : sx_initialize_return_wit_8_invalid_dimensions.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_return_wit_8_invalid_dimensions_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_return_wit_9_invalid_dimensions_split_goal_1 : sx_initialize_return_wit_9_invalid_dimensions_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto); unfold simplex_init_return; reflexivity.
Qed.

Lemma proof_of_sx_initialize_return_wit_9_invalid_dimensions : sx_initialize_return_wit_9_invalid_dimensions.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_return_wit_9_invalid_dimensions_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_return_wit_10_invalid_dimensions_split_goal_1 : sx_initialize_return_wit_10_invalid_dimensions_split_goal_1.
Proof.
  LLM_pre_process ltac:(try unfold simplex_init_return; reflexivity).
Qed.

Lemma proof_of_sx_initialize_return_wit_10_invalid_dimensions : sx_initialize_return_wit_10_invalid_dimensions.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_return_wit_10_invalid_dimensions_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_return_wit_11_invalid_dimensions_split_goal_1 : sx_initialize_return_wit_11_invalid_dimensions_split_goal_1.
Proof.
  LLM_pre_process ltac:(try unfold simplex_init_return; reflexivity).
Qed.

Lemma proof_of_sx_initialize_return_wit_11_invalid_dimensions : sx_initialize_return_wit_11_invalid_dimensions.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_return_wit_11_invalid_dimensions_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_return_wit_12_invalid_dimensions_split_goal_1 : sx_initialize_return_wit_12_invalid_dimensions_split_goal_1.
Proof.
  LLM_pre_process ltac:(try unfold simplex_init_return; reflexivity).
Qed.

Lemma proof_of_sx_initialize_return_wit_12_invalid_dimensions : sx_initialize_return_wit_12_invalid_dimensions.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_return_wit_12_invalid_dimensions_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_return_wit_13_invalid_dimensions_split_goal_1 : sx_initialize_return_wit_13_invalid_dimensions_split_goal_1.
Proof.
  LLM_pre_process ltac:(try unfold simplex_init_return; reflexivity).
Qed.

Lemma proof_of_sx_initialize_return_wit_13_invalid_dimensions : sx_initialize_return_wit_13_invalid_dimensions.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_initialize_return_wit_13_invalid_dimensions_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias_pure_split_goal_1 : sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias_pure_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; exact PreH32.
Qed.

Lemma proof_of_sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias_pure : sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias_pure.
Proof.
aggressive_pre_process.
 Goal_apply proof_of_sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias_pure_split_goal_1.
Qed.

Lemma proof_of_sx_initialize_partial_solve_wit_14_rejected_coefficient_pure_split_goal_1 : sx_initialize_partial_solve_wit_14_rejected_coefficient_pure_split_goal_1.
Proof.
 LLM_pre_process ltac:(unfold simplex_init_unreachable in *; contradiction).
Qed.

Lemma proof_of_sx_initialize_partial_solve_wit_14_rejected_coefficient_pure : sx_initialize_partial_solve_wit_14_rejected_coefficient_pure.
Proof.
 aggressive_pre_process. Goal_apply proof_of_sx_initialize_partial_solve_wit_14_rejected_coefficient_pure_split_goal_1.
Qed.

