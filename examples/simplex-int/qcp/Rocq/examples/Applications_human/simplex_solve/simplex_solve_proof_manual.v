From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_solve Require Import simplex_solve_goal.
From SimpleC.EE.Applications_human.simplex_solve Require Import simplex_solve_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_find_violation_preserve.simplex_find_violation_preserve_lib.
Require Import SimpleC.EE.Applications_human.simplex_find_entering_preserve.simplex_find_entering_preserve_lib.
Require Import SimpleC.EE.Applications_human.simplex_pivot.simplex_pivot_lib.
Require Import SimpleC.EE.Applications_human.simplex_recompute.simplex_recompute_lib.
Require Import SimpleC.EE.Applications_human.simplex_solve.simplex_solve_lib.
Local Open Scope sac.

Lemma proof_of_sx_solve_entail_wit_1_normal_state_split_goal_1 : sx_solve_entail_wit_1_normal_state_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_solve_entail_wit_1_normal_state : sx_solve_entail_wit_1_normal_state.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_solve_entail_wit_1_normal_state_split_goal_1.
Qed.

Lemma proof_of_sx_solve_entail_wit_2_normal_state : sx_solve_entail_wit_2_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (HB : forall k, In k CB_2 -> 0<=k<V_normal_state).
 { intros k HK. rewrite PreH7. eapply normal_basis__search_memory; eauto. }
 Exists CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2.
 split_pure_spatial.
 - sep_apply_l_atomic (solve_search_split s_pre V_normal_state CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state HB). cancel.
 - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_solve_entail_wit_3_normal_state : sx_solve_entail_wit_3_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (HQ:retval=1).
 { unfold simplex_find_violation_spec, simplex_find_violation_result in PreH2. tauto. }
 subst retval.
 assert (HB : forall k, In k CB_2 -> 0<=k<V_normal_state).
 { intros k HK. rewrite PreH9. eapply normal_basis__search_memory; eauto. }
 Exists CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2.
 split_pure_spatial.
 - sep_apply_l_atomic (solve_search_merge s_pre V_normal_state CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state HB). cancel.
 - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_solve_entail_wit_4_normal_state : sx_solve_entail_wit_4_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 pose proof (solve_violation_selected_row _ _ _ _ _ _ _ _ _ _ _ _ _ PreH18 ltac:(lia)) as [HR [HD HS]].
 assert (HN:Zlength CN_2=400 /\ Zlength CD_2=400).
 { unfold simplex_solve_normal, simplex_solve_pack in PreH15. tauto. }
 assert (HB:forall k,In k (Zrange 0 V_normal_state)->0<=k<V_normal_state).
 { intros k HK. apply In_Zrange in HK. lia. }
 destruct HD as [HD|HD]; [Left|Right]; Exists CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2;
 split_pure_spatial.
 - sep_apply_l_atomic (solve_search_split s_pre V_normal_state (Zrange 0 V_normal_state) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state HB).
   sep_apply_l_atomic (solve_enter_memory_split s_pre M_normal_state V_normal_state CN_2 CD_2 row ltac:(tauto) ltac:(tauto) ltac:(lia) ltac:(lia) HR). cancel.
 - split_pures; dump_pre_spatial; auto; lia.
 - sep_apply_l_atomic (solve_search_split s_pre V_normal_state (Zrange 0 V_normal_state) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state HB).
   sep_apply_l_atomic (solve_enter_memory_split s_pre M_normal_state V_normal_state CN_2 CD_2 row ltac:(tauto) ltac:(tauto) ltac:(lia) ltac:(lia) HR). cancel.
 - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_sx_solve_entail_wit_5_1_normal_state : sx_solve_entail_wit_5_1_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (HQ:retval=1).
 { unfold simplex_find_entering_spec, simplex_enter_result in PreH2. destruct PreH2 as [[? ?]|[k [? [? [[? ?]|[? ?]]]]]]; lia. }
 subst retval.
 assert (HN:Zlength CN_2=400 /\ Zlength CD_2=400).
 { unfold simplex_solve_normal, simplex_solve_pack in PreH16. tauto. }
 assert (HB:forall k,In k (Zrange 0 V_normal_state)->0<=k<V_normal_state).
 { intros k HK. apply In_Zrange in HK. lia. }
 rewrite <- PreH9 in *.
 Exists CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2.
 split_pure_spatial.
 - sep_apply_l_atomic (solve_search_merge s_pre V_normal_state (Zrange 0 V_normal_state) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state HB).
   sep_apply_l_atomic (solve_enter_memory_merge s_pre M_normal_state V_normal_state CN_2 CD_2 row ltac:(tauto) ltac:(tauto) ltac:(lia) ltac:(lia) ltac:(lia)). cancel.
 - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_solve_entail_wit_5_2_normal_state : sx_solve_entail_wit_5_2_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (HQ:retval=1).
 { unfold simplex_find_entering_spec, simplex_enter_result in PreH2. destruct PreH2 as [[? ?]|[k [? [? [[? ?]|[? ?]]]]]]; lia. }
 subst retval.
 assert (HN:Zlength CN_2=400 /\ Zlength CD_2=400).
 { unfold simplex_solve_normal, simplex_solve_pack in PreH16. tauto. }
 assert (HB:forall k,In k (Zrange 0 V_normal_state)->0<=k<V_normal_state).
 { intros k HK. apply In_Zrange in HK. lia. }
 rewrite <- PreH9 in *.
 Exists CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2.
 split_pure_spatial.
 - sep_apply_l_atomic (solve_search_merge s_pre V_normal_state (Zrange 0 V_normal_state) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state HB).
   sep_apply_l_atomic (solve_enter_memory_merge s_pre M_normal_state V_normal_state CN_2 CD_2 row ltac:(tauto) ltac:(tauto) ltac:(lia) ltac:(lia) ltac:(lia)). cancel.
 - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_solve_entail_wit_6_1_normal_state : sx_solve_entail_wit_6_1_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst retval.
 pose proof PreH21 as HN.
 unfold simplex_solve_normal, simplex_solve_pack in HN.
 cbn zeta in HN.
 assert (HB:0<=Znth row CB 0<V_normal_state).
 { destruct HN as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HB _]]]]]]]]]]]]]].
   specialize (HB row ltac:(lia)). lia. }
 assert (HLN:Zlength CN_2=400 /\ Zlength CD_2=400) by tauto.
 pose proof (pivot_lengths__repair_memory CN_2 CD_2 M_normal_state V_normal_state row entering (Znth row CB 0) 1 ON OD (proj1 HLN) (proj2 HLN) PreH3) as [HON HOD].
 assert (HE:entering<V_normal_state).
 { unfold simplex_find_entering_spec, simplex_enter_result in PreH25.
   destruct PreH25 as [[_ [E _]]|[k [HK [_ [[_ [E _]]|[E _]]]]]]; lia. }
 destruct (PreH4 eq_refl) as [HC HEQ].
 Exists ON OD CN_2 CD_2 CB CIB_2 CVN_2 CVD_2.
 split_pure_spatial.
 - sep_apply_l_atomic (solve_variables_split s_pre V_normal_state HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state ltac:(lia)).
   sep_apply_l_atomic (values_focus__entry_focus s_pre V_normal_state CVN_2 CVD_2 (Znth row CB 0) HB).
   sep_apply_l_atomic (solve_bound_focus s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state (Znth row CB 0) HB).
   unfold simplex_solve_bound_slot, simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.

 - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_sx_solve_entail_wit_6_2_normal_state : sx_solve_entail_wit_6_2_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst retval.
 pose proof PreH21 as HN.
 unfold simplex_solve_normal, simplex_solve_pack in HN.
 cbn zeta in HN.
 assert (HB:0<=Znth row CB 0<V_normal_state).
 { destruct HN as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HB _]]]]]]]]]]]]]].
   specialize (HB row ltac:(lia)). lia. }
 assert (HLN:Zlength CN_2=400 /\ Zlength CD_2=400) by tauto.
 pose proof (pivot_lengths__repair_memory CN_2 CD_2 M_normal_state V_normal_state row entering (Znth row CB 0) 1 ON OD (proj1 HLN) (proj2 HLN) PreH3) as [HON HOD].
 assert (HE:entering<V_normal_state).
 { unfold simplex_find_entering_spec, simplex_enter_result in PreH25.
   destruct PreH25 as [[_ [E _]]|[k [HK [_ [[_ [E _]]|[E _]]]]]]; lia. }
 destruct (PreH4 eq_refl) as [HC HEQ].
 Exists ON OD CN_2 CD_2 CB CIB_2 CVN_2 CVD_2.
 split_pure_spatial.
 - sep_apply_l_atomic (solve_variables_split s_pre V_normal_state HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state ltac:(lia)).
   sep_apply_l_atomic (values_focus__entry_focus s_pre V_normal_state CVN_2 CVD_2 (Znth row CB 0) HB).
   sep_apply_l_atomic (solve_bound_focus s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state (Znth row CB 0) HB).
   unfold simplex_solve_bound_slot, simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_sx_solve_entail_wit_7_1_normal_state : sx_solve_entail_wit_7_1_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 pose proof PreH15 as HN.
 unfold simplex_solve_normal, simplex_solve_pack in HN. cbn zeta in HN.
 assert (HVN:Zlength CVN_2=V_normal_state) by (intuition lia).
 assert (HVD:Zlength CVD_2=V_normal_state) by (intuition lia).
 Exists PN_2 PD_2 CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2.
 split_pure_spatial.
 - unfold simplex_solve_repair.
   rewrite (proj2 (Z.ltb_lt 0 direction) ltac:(lia)).
   rewrite solve_pivot_recompute_memory by (auto; lia).
   pose proof (values_cells_store__repair_memory s_pre V_normal_state CVN_2 CVD_2 leaving (Znth leaving LN_normal_state 0) (Znth leaving LD_normal_state 0) HVN HVD ltac:(lia)) as VS.
   cancel.
   csimpl.
   sep_apply_l_atomic VS.
   sep_apply_r_atomic (solve_bound_merge s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state leaving ltac:(lia)).
   unfold simplex_solve_bound_slot, simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_sx_solve_entail_wit_7_2_normal_state : sx_solve_entail_wit_7_2_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 pose proof PreH15 as HN.
 unfold simplex_solve_normal, simplex_solve_pack in HN. cbn zeta in HN.
 assert (HVN:Zlength CVN_2=V_normal_state) by (intuition lia).
 assert (HVD:Zlength CVD_2=V_normal_state) by (intuition lia).
 Exists PN_2 PD_2 CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2.
 split_pure_spatial.
 - unfold simplex_solve_repair.
   rewrite (proj2 (Z.ltb_ge 0 direction) ltac:(lia)).
   rewrite solve_pivot_recompute_memory by (auto; lia).
   pose proof (values_cells_store__repair_memory s_pre V_normal_state CVN_2 CVD_2 leaving (Znth leaving UN_normal_state 0) (Znth leaving UD_normal_state 0) HVN HVD ltac:(lia)) as VS.
   cancel.
   csimpl.
   sep_apply_l_atomic VS.
   sep_apply_r_atomic (solve_bound_merge s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state leaving ltac:(lia)).
   unfold simplex_solve_bound_slot, simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
 - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_sx_solve_entail_wit_8_normal_state : sx_solve_entail_wit_8_normal_state.
Proof.

 LLM_pre_process ltac:(lia || int_auto).
 assert (HQ:retval=1).
 { pose proof (solve_recompute_code__iteration _ _ _ _ _ _ _ _ _ _ _ _ _ PreH8). lia. }
 subst retval.
 assert (HNB:Znth entering CIB_2 0=0).
 { eapply solve_enter_nonbasic__iteration; eauto; lia. }
 assert (HOLD:=PreH22).
 unfold simplex_solve_normal, simplex_solve_pack in HOLD; cbn zeta in HOLD.
 destruct HOLD as [HN [HD [HBL [HIL [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HB HREST]]]]]]]]]]]]]].
 assert (HCOLS:V_normal_state=I_normal_state+M_normal_state) by lia.
 assert (HNORMAL:simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state
 M_normal_state I_normal_state (simplex_solve_pack PN PD
 (simplex_pivot_basis CB_2 row entering 1) (simplex_pivot_marks CIB_2 leaving entering 1) ON OD)).
 { rewrite PreH31. cbn [simplex_pivot_basis simplex_pivot_marks].
   eapply (solve_success_normal__iteration A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state
 CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 PN PD ON OD M_normal_state I_normal_state row entering direction); eauto; try lia.
   - rewrite <- HCOLS; eassumption.
   - rewrite <- HCOLS, <- PreH31; exact PreH36.
   - rewrite <- HCOLS; eassumption.
   - intros k HK. unfold simplex_solve_rat. specialize (PreH40 k ltac:(rewrite HCOLS; exact HK)).
     change INT_MAX with 2147483647 in PreH40. tauto.
   - intros j HJ.
     pose proof (solve_forall_nth__iteration _ _ j PreH2 ltac:(lia)).
     pose proof (solve_forall_nth__iteration _ _ j PreH3 ltac:(lia)).
     pose proof (solve_forall_nth__iteration _ _ j PreH4 ltac:(lia)).
     pose proof (solve_forall_nth__iteration _ _ j PreH5 ltac:(lia)).
     change INT_MAX with 2147483647 in *. lia.
   - unfold simplex_recompute_prefix in PreH8.
     rewrite <- HCOLS. replace (M_normal_state+I_normal_state) with V_normal_state in PreH8 by lia. rewrite PreH31 in PreH8. exact PreH8. }
 assert (HITER:simplex_solve_iteration HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state
 M_normal_state V_normal_state L_normal_state count (simplex_solve_pack CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2)=
 (2,simplex_solve_pack PN PD (simplex_pivot_basis CB_2 row entering 1)
 (simplex_pivot_marks CIB_2 leaving entering 1) ON OD)).
 { unfold simplex_find_violation_spec in PreH33.
   destruct (proj1 (simplex_find_violation_compute_iff (fun j=>Znth j CB_2 0)
 (simplex_scan_rows CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state) V_normal_state M_normal_state 1 row direction PreH11
     ltac:(intros j HJ; destruct (HB j HJ); lia)) PreH33) as [best HSCAN].
   pose proof (proj1 (simplex_enter_compute_iff _ _ _ _ PreH16) PreH34) as HENTER.
   unfold simplex_solve_iteration, simplex_solve_pack.
   rewrite HSCAN. cbn [Z.eqb].
   rewrite (proj2 (Z.ltb_ge row 0) PreH25), HENTER. cbn [Z.eqb].
   rewrite (proj2 (Z.ltb_ge entering 0) PreH27), (proj2 (Z.leb_gt _ _) PreH32).
   unfold simplex_pivot_result in PreH35. rewrite <- PreH31, PreH35. cbn [Z.eqb].
   unfold simplex_recompute_prefix, simplex_solve_repair in PreH8.
   rewrite PreH31.
   replace (M_normal_state+I_normal_state) with V_normal_state in PreH8 by lia.
   rewrite PreH31 in PreH8. rewrite PreH8. reflexivity. }
 assert (HORIGIN:simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state
 M_normal_state I_normal_state (simplex_solve_pack PN PD (simplex_pivot_basis CB_2 row entering 1)
 (simplex_pivot_marks CIB_2 leaving entering 1) ON OD)).
 { eapply solve_origin_extend; [exact PreH23|exact PreH32|]. rewrite <- HCOLS; exact HITER. }
 assert (HPROGRESS:simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state
 M_normal_state V_normal_state L_normal_state (count+1) N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state
 PN PD (simplex_pivot_basis CB_2 row entering 1) (simplex_pivot_marks CIB_2 leaving entering 1) ON OD).
 { unfold simplex_solve_progress in *. rewrite solve_prefix_step by lia. rewrite PreH24.
   cbn [simplex_solve_tick Z.eqb]. exact HITER. }
 Exists PN PD (simplex_pivot_basis CB_2 row entering 1) (simplex_pivot_marks CIB_2 leaving entering 1) ON OD.
 split_pure_spatial.
 - rewrite <- PreH15.
   rewrite (solve_pivot_recompute_memory s_pre M_normal_state V_normal_state PN PD PreH38 PreH39 ltac:(lia) ltac:(lia)).
   sep_apply_l_atomic (solve_variables_merge s_pre V_normal_state HL_normal_state HU_normal_state ON OD LN_normal_state LD_normal_state UN_normal_state UD_normal_state ltac:(lia)).
   cancel.
   sep_apply_l_atomic (store_int_undef_store_int (&("row")) row).
   sep_apply_l_atomic (store_int_undef_store_int (&("direction")) direction).
   sep_apply_l_atomic (store_int_undef_store_int (&("entering")) entering).
   sep_apply_l_atomic (store_int_undef_store_int (&("leaving")) leaving).
   cancel.
 - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_sx_solve_return_wit_1_normal_state : sx_solve_return_wit_1_normal_state.
Proof.
 LLM_pre_process ltac:(lia).
 subst s_pre pivot_limit_pre.
 try subst retval.
 assert (HV: V_normal_state=M_normal_state+I_normal_state) by lia.
 assert (Hscan:exists best, simplex_scan_compute (fun j=>Znth j CB 0)
   (simplex_scan_rows CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state)
   V_normal_state M_normal_state=(1,(best,(row,direction)))).
 { rewrite HV. eapply solve_scan_normal__rejection_results; eauto; rewrite <- HV; assumption. }
 destruct Hscan as [best Hscan].
 match goal with H:simplex_find_entering_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
   apply simplex_enter_preserve_compute_iff in H; [rename H into Henter|lia] end.
 Exists PN PD (simplex_pivot_basis CB row entering 1) (simplex_pivot_marks CIB leaving entering 1) ON_2 OD_2.
 rewrite <- HV.
 rewrite (solve_pivot_recompute_memory S_normal_state M_normal_state V_normal_state PN PD ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia)).
 sep_apply_l_atomic (solve_variables_merge S_normal_state V_normal_state HL_normal_state HU_normal_state ON_2 OD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state ltac:(lia)).
 split_pure_spatial.
 - csimpl; sepcon_right_assoc; repeat progress cancel; try reflexivity.
 - split_pures; dump_pre_spatial; try lia.
   unfold simplex_solve_result.
   eapply solve_terminal_complete with (count:=count); try lia.
   match goal with H:simplex_solve_progress _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
     unfold simplex_solve_progress in H; rewrite H end.
   unfold simplex_solve_tick.
   cbn beta iota zeta delta [Z.eqb].
   unfold simplex_solve_iteration. cbn beta iota zeta delta [simplex_solve_pack].
   rewrite Hscan. cbn beta iota zeta delta [Z.eqb].
   rewrite (proj2 (Z.ltb_ge row 0) ltac:(lia)).
   rewrite Henter. cbn beta iota zeta delta [Z.eqb].
   rewrite (proj2 (Z.ltb_ge entering 0) ltac:(lia)).

   rewrite (proj2 (Z.leb_gt L_normal_state count) ltac:(lia)).
   match goal with H:simplex_pivot_result _ _ _ _ _ _ _ _ _ _ |- _ =>
     unfold simplex_pivot_result in H; rewrite <- PreH31; rewrite H end.
   cbn beta iota zeta delta [Z.eqb].
   unfold simplex_recompute_prefix, simplex_solve_repair in PreH8.
   rewrite <- HV in PreH8.
   rewrite <- PreH31 in PreH8.
   rewrite PreH8. reflexivity.
Qed.

Lemma proof_of_sx_solve_return_wit_2_normal_state : sx_solve_return_wit_2_normal_state.
Proof.
 LLM_pre_process ltac:(lia).
 subst s_pre pivot_limit_pre.
 try subst retval.
 assert (HV: V_normal_state=M_normal_state+I_normal_state) by lia.
 assert (Hscan:exists best, simplex_scan_compute (fun j=>Znth j CB 0)
   (simplex_scan_rows CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state)
   V_normal_state M_normal_state=(1,(best,(row,direction)))).
 { rewrite HV. eapply solve_scan_normal__rejection_results; eauto; rewrite <- HV; assumption. }
 destruct Hscan as [best Hscan].
 match goal with H:simplex_find_entering_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
   apply simplex_enter_preserve_compute_iff in H; [rename H into Henter|lia] end.
 Exists ON_2 OD_2 (simplex_pivot_basis CB row entering 0) (simplex_pivot_marks CIB (Znth row CB 0) entering 0) CVN CVD.
 split_pure_spatial.
 - csimpl; sepcon_right_assoc; repeat progress cancel; try reflexivity.
 - split_pures; dump_pre_spatial; try lia.
   unfold simplex_solve_result.
   eapply solve_terminal_complete with (count:=count); try lia.
   match goal with H:simplex_solve_progress _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
     unfold simplex_solve_progress in H; rewrite H end.
   unfold simplex_solve_tick.
   cbn beta iota zeta delta [Z.eqb].
   unfold simplex_solve_iteration. cbn beta iota zeta delta [simplex_solve_pack].
   rewrite Hscan. cbn beta iota zeta delta [Z.eqb].
   rewrite (proj2 (Z.ltb_ge row 0) ltac:(lia)).
   rewrite Henter. cbn beta iota zeta delta [Z.eqb].
   rewrite (proj2 (Z.ltb_ge entering 0) ltac:(lia)).

   rewrite (proj2 (Z.leb_gt L_normal_state count) ltac:(lia)).
   match goal with H:simplex_pivot_result _ _ _ _ _ _ _ _ _ _ |- _ =>
     unfold simplex_pivot_result in H; rewrite H end.
   reflexivity.
Qed.

Lemma proof_of_sx_solve_return_wit_3_normal_state : sx_solve_return_wit_3_normal_state.
Proof.
 LLM_pre_process ltac:(lia).
 subst s_pre pivot_limit_pre.
 try subst retval.
 assert (HV: V_normal_state=M_normal_state+I_normal_state) by lia.
 assert (Hscan:exists best, simplex_scan_compute (fun j=>Znth j CB 0)
   (simplex_scan_rows CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state)
   V_normal_state M_normal_state=(1,(best,(row,direction)))).
 { rewrite HV. eapply solve_scan_normal__rejection_results; eauto; rewrite <- HV; assumption. }
 destruct Hscan as [best Hscan].
 match goal with H:simplex_find_entering_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
   apply simplex_enter_preserve_compute_iff in H; [rename H into Henter|lia] end.
 Exists ON_2 OD_2 (simplex_pivot_basis CB row entering 0) (simplex_pivot_marks CIB (Znth row CB 0) entering 0) CVN CVD.
 split_pure_spatial.
 - csimpl; sepcon_right_assoc; repeat progress cancel; try reflexivity.
 - split_pures; dump_pre_spatial; try lia.
   unfold simplex_solve_result.
   eapply solve_terminal_complete with (count:=count); try lia.
   match goal with H:simplex_solve_progress _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
     unfold simplex_solve_progress in H; rewrite H end.
   unfold simplex_solve_tick.
   cbn beta iota zeta delta [Z.eqb].
   unfold simplex_solve_iteration. cbn beta iota zeta delta [simplex_solve_pack].
   rewrite Hscan. cbn beta iota zeta delta [Z.eqb].
   rewrite (proj2 (Z.ltb_ge row 0) ltac:(lia)).
   rewrite Henter. cbn beta iota zeta delta [Z.eqb].
   rewrite (proj2 (Z.ltb_ge entering 0) ltac:(lia)).

   rewrite (proj2 (Z.leb_gt L_normal_state count) ltac:(lia)).
   match goal with H:simplex_pivot_result _ _ _ _ _ _ _ _ _ _ |- _ =>
     unfold simplex_pivot_result in H; rewrite H end.
   reflexivity.
Qed.

Lemma proof_of_sx_solve_return_wit_4_normal_state : sx_solve_return_wit_4_normal_state.
Proof.
 LLM_pre_process ltac:(lia).
 subst s_pre pivot_limit_pre.
 try subst retval.
 assert (HV: V_normal_state=M_normal_state+I_normal_state) by lia.
 assert (Hscan:exists best, simplex_scan_compute (fun j=>Znth j CB 0)
   (simplex_scan_rows CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state)
   V_normal_state M_normal_state=(1,(best,(row,direction)))).
 { rewrite HV. eapply solve_scan_normal__rejection_results; eauto; rewrite <- HV; assumption. }
 destruct Hscan as [best Hscan].
 match goal with H:simplex_find_entering_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
   apply simplex_enter_preserve_compute_iff in H; [rename H into Henter|lia] end.
 Exists CN CD CB CIB CVN CVD.
 split_pure_spatial.
 - csimpl; sepcon_right_assoc; repeat progress cancel; try reflexivity.
 - split_pures; dump_pre_spatial; try lia.
   unfold simplex_solve_result.
   eapply solve_terminal_complete with (count:=count); try lia.
   match goal with H:simplex_solve_progress _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
     unfold simplex_solve_progress in H; rewrite H end.
   unfold simplex_solve_tick.
   cbn beta iota zeta delta [Z.eqb].
   unfold simplex_solve_iteration. cbn beta iota zeta delta [simplex_solve_pack].
   rewrite Hscan. cbn beta iota zeta delta [Z.eqb].
   rewrite (proj2 (Z.ltb_ge row 0) ltac:(lia)).
   rewrite Henter. cbn beta iota zeta delta [Z.eqb].
   rewrite (proj2 (Z.ltb_ge entering 0) ltac:(lia)).

   rewrite (proj2 (Z.leb_le L_normal_state count) ltac:(lia)).
   reflexivity.
Qed.

Lemma proof_of_sx_solve_return_wit_5_normal_state : sx_solve_return_wit_5_normal_state.
Proof.
 LLM_pre_process ltac:(lia).
 subst s_pre pivot_limit_pre.
 try subst retval.
 assert (HV: V_normal_state=M_normal_state+I_normal_state) by lia.
 assert (Hscan:exists best, simplex_scan_compute (fun j=>Znth j CB 0)
   (simplex_scan_rows CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state)
   V_normal_state M_normal_state=(1,(best,(row,direction)))).
 { rewrite HV. eapply solve_scan_normal__rejection_results; eauto; rewrite <- HV; assumption. }
 destruct Hscan as [best Hscan].
 match goal with H:simplex_find_entering_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
   apply simplex_enter_preserve_compute_iff in H; [rename H into Henter|lia] end.
 Exists CN CD CB CIB CVN CVD.
 split_pure_spatial.
 - csimpl; sepcon_right_assoc; repeat progress cancel; try reflexivity.
 - split_pures; dump_pre_spatial; try lia.
   unfold simplex_solve_result.
   eapply solve_terminal_complete with (count:=count); try lia.
   match goal with H:simplex_solve_progress _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
     unfold simplex_solve_progress in H; rewrite H end.
   unfold simplex_solve_tick.
   cbn beta iota zeta delta [Z.eqb].
   unfold simplex_solve_iteration. cbn beta iota zeta delta [simplex_solve_pack].
   rewrite Hscan. cbn beta iota zeta delta [Z.eqb].
   rewrite (proj2 (Z.ltb_ge row 0) ltac:(lia)).
   rewrite Henter. cbn beta iota zeta delta [Z.eqb].
   rewrite (proj2 (Z.ltb_ge entering 0) ltac:(lia)).

   rewrite (proj2 (Z.leb_le L_normal_state count) ltac:(lia)).
   reflexivity.
Qed.

Lemma proof_of_sx_solve_return_wit_6_normal_state : sx_solve_return_wit_6_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists CN CD CB CIB CVN CVD.
 try subst s_pre.
 replace V_normal_state with (I_normal_state+M_normal_state) in * by lia.
 split_pure_spatial.
 - cancel (simplex_pivot_memory S_normal_state M_normal_state (I_normal_state+M_normal_state) CN CD).
   cancel.
 -
 split_pures; dump_pre_spatial; try tauto; try lia.
 + eapply solve_terminal_result__unsat with (a:=A_normal_state) (inputs:=I_normal_state)
     (count:=count) (r:=row) (dir:=direction) (e:=entering); eauto; lia.
 + intros _. eapply solve_no_candidate_unsat__unsat with (n:=CN) (d:=CD) (b:=CB) (ib:=CIB)
     (vn:=CVN) (vd:=CVD) (r:=row) (dir:=direction) (e:=entering); eauto; lia.
Qed.

Lemma proof_of_sx_solve_return_wit_7_normal_state : sx_solve_return_wit_7_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists CN CD CB CIB CVN CVD.
 try subst s_pre.
 replace V_normal_state with (I_normal_state+M_normal_state) in * by lia.
 split_pure_spatial.
 - cancel (simplex_pivot_memory S_normal_state M_normal_state (I_normal_state+M_normal_state) CN CD).
   cancel.
 -
 split_pures; dump_pre_spatial; try tauto; try lia.
 + eapply solve_terminal_result__unsat with (a:=A_normal_state) (inputs:=I_normal_state)
     (count:=count) (r:=row) (dir:=direction) (e:=entering); eauto; lia.
 + intros _. eapply solve_no_candidate_unsat__unsat with (n:=CN) (d:=CD) (b:=CB) (ib:=CIB)
     (vn:=CVN) (vd:=CVD) (r:=row) (dir:=direction) (e:=entering); eauto; lia.
Qed.

Lemma proof_of_sx_solve_return_wit_8_normal_state : sx_solve_return_wit_8_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst s_pre. rewrite <- PreH9 in *.
 pose proof PreH16 as Hshape.
 cbn [simplex_solve_normal simplex_solve_pack] in Hshape.
 destruct Hshape as [HN [HD Hshape]].
 Exists CN CD CB CIB CVN CVD.
 sep_apply_l_atomic (solve_search_merge S_normal_state V_normal_state (Zrange 0 V_normal_state) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state ltac:(intros; apply In_Zrange in H; lia)).
 sep_apply_l_atomic (solve_enter_memory_merge S_normal_state M_normal_state V_normal_state CN CD row HN HD ltac:(lia) ltac:(lia) ltac:(lia)).
 split_pure_spatial; [cancel |].
 split_pures; dump_pre_spatial; try lia.
 unfold simplex_solve_result.
 eapply solve_terminal_complete with (count:=count); try lia.
 unfold simplex_solve_progress in PreH18.
 rewrite PreH18. cbn [simplex_solve_tick].
 unfold simplex_solve_iteration. cbn [simplex_solve_pack].
 assert (HB:forall j,0<=j<M_normal_state -> Znth j CB 0<V_normal_state).
 { intros j HJ. destruct Hshape as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HB _]]]]]]]]]]]].
   specialize (HB j HJ). lia. }
 unfold simplex_find_violation_spec in PreH19.
 apply (proj1 (simplex_find_violation_compute_iff _ _ _ _ _ _ _ PreH5 HB)) in PreH19.
 destruct PreH19 as [best HS]. rewrite HS.
 rewrite (proj2 (Z.ltb_ge row 0) PreH20).
 unfold simplex_find_entering_spec in PreH2.
 apply (proj1 (simplex_enter_compute_iff _ _ _ _ PreH10)) in PreH2.
 rewrite PreH2, PreH1. reflexivity.
Qed.

Lemma proof_of_sx_solve_return_wit_9_normal_state : sx_solve_return_wit_9_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst s_pre. rewrite <- PreH9 in *.
 pose proof PreH16 as Hshape.
 cbn [simplex_solve_normal simplex_solve_pack] in Hshape.
 destruct Hshape as [HN [HD Hshape]].
 Exists CN CD CB CIB CVN CVD.
 sep_apply_l_atomic (solve_search_merge S_normal_state V_normal_state (Zrange 0 V_normal_state) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state ltac:(intros; apply In_Zrange in H; lia)).
 sep_apply_l_atomic (solve_enter_memory_merge S_normal_state M_normal_state V_normal_state CN CD row HN HD ltac:(lia) ltac:(lia) ltac:(lia)).
 split_pure_spatial; [cancel |].
 split_pures; dump_pre_spatial; try lia.
 unfold simplex_solve_result.
 eapply solve_terminal_complete with (count:=count); try lia.
 unfold simplex_solve_progress in PreH18.
 rewrite PreH18. cbn [simplex_solve_tick].
 unfold simplex_solve_iteration. cbn [simplex_solve_pack].
 assert (HB:forall j,0<=j<M_normal_state -> Znth j CB 0<V_normal_state).
 { intros j HJ. destruct Hshape as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HB _]]]]]]]]]]]].
   specialize (HB j HJ). lia. }
 unfold simplex_find_violation_spec in PreH19.
 apply (proj1 (simplex_find_violation_compute_iff _ _ _ _ _ _ _ PreH5 HB)) in PreH19.
 destruct PreH19 as [best HS]. rewrite HS.
 rewrite (proj2 (Z.ltb_ge row 0) PreH20).
 unfold simplex_find_entering_spec in PreH2.
 apply (proj1 (simplex_enter_compute_iff _ _ _ _ PreH10)) in PreH2.
 rewrite PreH2, PreH1. reflexivity.
Qed.

Lemma proof_of_sx_solve_return_wit_10_normal_state : sx_solve_return_wit_10_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists CN CD CB CIB CVN CVD.
 subst s_pre.
 split_pure_spatial.
 - cancel (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state).
   cancel (simplex_pivot_memory S_normal_state M_normal_state V_normal_state CN CD).
   cancel.
 - pose proof PreH15 as HN.
   cbn [simplex_solve_normal simplex_solve_pack] in HN.
   do 13 (destruct HN as [_ HN]).
   destruct HN as [HB [HJ [HR [HZ [HE HEQ]]]]].
   split_pures; dump_pre_spatial.
   all: try lia.
   all: try (intros; split; assumption).
   + unfold simplex_solve_result.
     eapply solve_terminal_complete with (count:=count); [lia|lia|lia|].
     unfold simplex_solve_progress in PreH17.
     unfold simplex_solve_tick. rewrite PreH17.
     cbn [Z.eqb]. unfold simplex_solve_iteration, simplex_solve_pack.
     unfold simplex_find_violation_spec in PreH18.
     apply (proj1 (simplex_find_violation_compute_iff (fun i=>Znth i CB 0)
       (simplex_scan_rows CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state)
       V_normal_state M_normal_state 1 row direction PreH4
       ltac:(intros j Hj; destruct (HB j Hj) as [Hrange Hmark]; lia))) in PreH18.
     destruct PreH18 as [best HC]. rewrite HC.
     rewrite (proj2 (Z.ltb_lt row 0) PreH1). reflexivity.
   + intros _. unfold simplex_solve_witness.
     apply solve_source_projection.
     apply (proj1 (HEQ _)). split; [exact HE|].
     eapply solve_no_violation_all_bounds with (b:=CB) (ib:=CIB)
       (rows:=M_normal_state) (r:=row) (direction:=direction).
     * intros j Hj. specialize (HJ j ltac:(lia)).
       destruct HJ as [_ [_ [_ [_ [HV [HL [HU _]]]]]]].
       unfold simplex_solve_rat in HV, HL, HU. lia.
     * intros j Hj Hneq. specialize (HJ j ltac:(lia)).
       destruct HJ as [HI [_ [_ [HM _]]]]. apply HM. lia.
     * intros j Hj Hz. specialize (HJ j ltac:(lia)).
       destruct HJ as [_ [_ [_ [_ [_ [_ [_ [_ HNB]]]]]]]].
       apply HNB. exact Hz.
     * replace (I_normal_state+M_normal_state) with V_normal_state by lia.
       exact PreH18.
     * exact PreH1.
Qed.

Lemma proof_of_sx_solve_return_wit_11_normal_state : sx_solve_return_wit_11_normal_state.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst s_pre.
 pose proof PreH16 as Hshape.
 cbn [simplex_solve_normal simplex_solve_pack] in Hshape.
 destruct Hshape as [HN [HD [HBL Hshape]]].
 assert (HB:forall j,0<=j<M_normal_state -> 0<=Znth j CB 0<V_normal_state).
 { intros j HJ. destruct Hshape as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HB _]]]]]]]]]]].
   specialize (HB j HJ). lia. }
 assert (HBI:forall k,In k CB -> 0<=k<V_normal_state).
 { intros k HK. apply In_nth with (d:=0%Z) in HK.
   destruct HK as [i [Hi <-]].
   specialize (HB (Z.of_nat i) ltac:(rewrite Zlength_correct in HBL; lia)).
   unfold Znth in HB. rewrite Nat2Z.id in HB. exact HB. }
 Exists CN CD CB CIB CVN CVD.
 sep_apply_l_atomic (solve_search_merge S_normal_state V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state HBI).
 split_pure_spatial; [cancel |].
 split_pures; dump_pre_spatial; try lia.
 unfold simplex_solve_result.
 eapply solve_terminal_complete with (count:=count); try lia.
 unfold simplex_solve_progress in PreH18.
 rewrite PreH18. cbn [simplex_solve_tick].
 unfold simplex_solve_iteration. cbn [simplex_solve_pack].
 unfold simplex_find_violation_spec in PreH2.
 apply (proj1 (simplex_find_violation_compute_iff _ _ _ _ _ _ _ PreH5 (fun j HJ => proj2 (HB j HJ)))) in PreH2.
 destruct PreH2 as [best HS]. rewrite HS, PreH1. reflexivity.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_1 : sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  intros j Hj. specialize (Hbasis j Hj). lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_2 : sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  intros j [Hj Hguard].
  destruct (in_index__search_preconditions CB j Hj) as [k [Hk Ek]].
  rewrite Hb in Hk. specialize (Hbasis k Hk).
  assert (Hjrange: 0<=j<I_normal_state+M_normal_state) by lia.
  specialize (Hcols j Hjrange).
  unfold simplex_solve_rat in Hcols. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_3 : sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  intros j [Hj Hguard].
  destruct (in_index__search_preconditions CB j Hj) as [k [Hk Ek]].
  rewrite Hb in Hk. specialize (Hbasis k Hk).
  assert (Hjrange: 0<=j<I_normal_state+M_normal_state) by lia.
  specialize (Hcols j Hjrange).
  unfold simplex_solve_rat in Hcols. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_4 : sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  intros j [Hj Hguard].
  destruct (in_index__search_preconditions CB j Hj) as [k [Hk Ek]].
  rewrite Hb in Hk. specialize (Hbasis k Hk).
  assert (Hjrange: 0<=j<I_normal_state+M_normal_state) by lia.
  specialize (Hcols j Hjrange).
  unfold simplex_solve_rat in Hcols. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_5 : sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  intros j Hj. specialize (Hbasis j Hj). lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_1_normal_state_pure : sx_solve_partial_solve_wit_1_normal_state_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_1.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_2.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_3.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_4.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_5.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_1 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  unfold simplex_solve_row. rewrite Zlength_map, simplex_scan_range_length by lia. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_2 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_3 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_4 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  unfold simplex_solve_row. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [j [<- Hj]].
  apply In_Zrange in Hj.
  assert (HS: In (16+row*24+j) (simplex_pivot_slots M_normal_state (I_normal_state+M_normal_state))).
  { apply simplex_pivot_a_active; lia. }
  specialize (Hslots _ HS). unfold simplex_solve_rat in Hslots.
  try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_5 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  unfold simplex_solve_row. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [j [<- Hj]].
  apply In_Zrange in Hj.
  assert (HS: In (16+row*24+j) (simplex_pivot_slots M_normal_state (I_normal_state+M_normal_state))).
  { apply simplex_pivot_a_active; lia. }
  specialize (Hslots _ HS). unfold simplex_solve_rat in Hslots.
  try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_6 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  apply Forall_forall. intros x Hx.
  destruct (in_index__search_preconditions CVN x Hx) as [j [Hj Ej]].
  rewrite Hvn in Hj. specialize (Hcols j Hj).
  unfold simplex_solve_rat in Hcols. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_7 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  apply Forall_forall. intros x Hx.
  destruct (in_index__search_preconditions CVN x Hx) as [j [Hj Ej]].
  rewrite Hvn in Hj. specialize (Hcols j Hj).
  unfold simplex_solve_rat in Hcols. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_8 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  apply Forall_forall. intros x Hx.
  destruct (in_index__search_preconditions CVD x Hx) as [j [Hj Ej]].
  rewrite Hvd in Hj. specialize (Hcols j Hj).
  unfold simplex_solve_rat in Hcols. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_9 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  apply Forall_forall. intros x Hx.
  destruct (in_index__search_preconditions CVD x Hx) as [j [Hj Ej]].
  rewrite Hvd in Hj. specialize (Hcols j Hj).
  unfold simplex_solve_rat in Hcols. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_10 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  intros j [Hj Hguard].
  assert (Hjrange: 0<=j<I_normal_state+M_normal_state) by lia.
  specialize (Hcols j Hjrange). unfold simplex_solve_rat in Hcols.
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_11 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  intros j [Hj Hguard].
  assert (Hjrange: 0<=j<I_normal_state+M_normal_state) by lia.
  specialize (Hcols j Hjrange). unfold simplex_solve_rat in Hcols.
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_12 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  intros j [Hj Hguard].
  assert (Hjrange: 0<=j<I_normal_state+M_normal_state) by lia.
  specialize (Hcols j Hjrange). unfold simplex_solve_rat in Hcols.
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_13 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  intros j [Hj Hguard].
  assert (Hjrange: 0<=j<I_normal_state+M_normal_state) by lia.
  specialize (Hcols j Hjrange). unfold simplex_solve_rat in Hcols.
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_14 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_15 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_16 : sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  unfold simplex_solve_row. rewrite Zlength_map, simplex_scan_range_length by lia. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_2_normal_state_pure : sx_solve_partial_solve_wit_2_normal_state_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_1.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_2.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_3.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_4.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_5.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_6.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_7.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_8.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_9.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_10.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_11.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_12.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_13.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_14.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_15.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_16.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_1 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  unfold simplex_solve_row. rewrite Zlength_map, simplex_scan_range_length by lia. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_2 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_3 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_4 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  unfold simplex_solve_row. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [j [<- Hj]].
  apply In_Zrange in Hj.
  assert (HS: In (16+row*24+j) (simplex_pivot_slots M_normal_state (I_normal_state+M_normal_state))).
  { apply simplex_pivot_a_active; lia. }
  specialize (Hslots _ HS). unfold simplex_solve_rat in Hslots.
  try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_5 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  unfold simplex_solve_row. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [j [<- Hj]].
  apply In_Zrange in Hj.
  assert (HS: In (16+row*24+j) (simplex_pivot_slots M_normal_state (I_normal_state+M_normal_state))).
  { apply simplex_pivot_a_active; lia. }
  specialize (Hslots _ HS). unfold simplex_solve_rat in Hslots.
  try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_6 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  apply Forall_forall. intros x Hx.
  destruct (in_index__search_preconditions CVN x Hx) as [j [Hj Ej]].
  rewrite Hvn in Hj. specialize (Hcols j Hj).
  unfold simplex_solve_rat in Hcols. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_7 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  apply Forall_forall. intros x Hx.
  destruct (in_index__search_preconditions CVN x Hx) as [j [Hj Ej]].
  rewrite Hvn in Hj. specialize (Hcols j Hj).
  unfold simplex_solve_rat in Hcols. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_8 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  apply Forall_forall. intros x Hx.
  destruct (in_index__search_preconditions CVD x Hx) as [j [Hj Ej]].
  rewrite Hvd in Hj. specialize (Hcols j Hj).
  unfold simplex_solve_rat in Hcols. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_9 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  apply Forall_forall. intros x Hx.
  destruct (in_index__search_preconditions CVD x Hx) as [j [Hj Ej]].
  rewrite Hvd in Hj. specialize (Hcols j Hj).
  unfold simplex_solve_rat in Hcols. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_10 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  intros j [Hj Hguard].
  assert (Hjrange: 0<=j<I_normal_state+M_normal_state) by lia.
  specialize (Hcols j Hjrange). unfold simplex_solve_rat in Hcols.
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_11 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  intros j [Hj Hguard].
  assert (Hjrange: 0<=j<I_normal_state+M_normal_state) by lia.
  specialize (Hcols j Hjrange). unfold simplex_solve_rat in Hcols.
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_12 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  intros j [Hj Hguard].
  assert (Hjrange: 0<=j<I_normal_state+M_normal_state) by lia.
  specialize (Hcols j Hjrange). unfold simplex_solve_rat in Hcols.
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_13 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  intros j [Hj Hguard].
  assert (Hjrange: 0<=j<I_normal_state+M_normal_state) by lia.
  specialize (Hcols j Hjrange). unfold simplex_solve_rat in Hcols.
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_14 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_15 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_16 : sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hnormal end.
  unfold simplex_solve_normal, simplex_solve_pack in Hnormal.
  destruct Hnormal as [Hn [Hd [Hb [Hib [Hvn [Hvd [Hhl [Hhu [Hln [Hld [Hun [Hud [Hnd [Hbasis [Hcols [Hslots Hrest]]]]]]]]]]]]]]]].
  unfold simplex_solve_row. rewrite Zlength_map, simplex_scan_range_length by lia. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_3_normal_state_pure : sx_solve_partial_solve_wit_3_normal_state_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_1.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_2.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_3.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_4.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_5.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_6.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_7.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_8.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_9.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_10.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_11.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_12.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_13.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_14.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_15.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_16.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_1 : sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_find_entering_spec _ _ _ _ _ _ _ _ _ _ _ _ 1 _ |- _ => pose proof H as HE end.
  unfold simplex_find_entering_spec, simplex_enter_result in HE.
  destruct HE as [[_ [HE _]]|[j [HJ [_ [[_ [HE HOBS]]|[HF _]]]]]]; try lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_2 : sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  exact HN.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_3 : sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  exact HD.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_4 : sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  exact HND.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_5 : sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  intros k HK. specialize (HBAS k HK). replace (M_normal_state + I_normal_state) with (I_normal_state + M_normal_state) by lia. exact HBAS.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_6 : sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  intros k HK.
  specialize (HMARK k ltac:(lia)).
  destruct HMARK as [HR [_ [_ [HIFF _]]]]. split; [exact HR|].
  intros HNZ. assert (HEQ:Znth k CIB 0=1) by lia.
  apply HIFF in HEQ. destruct HEQ as [i [HI HEQ]]. rewrite <- HEQ.
  unfold Znth. apply nth_In. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. rewrite Zlength_correct in HB. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_7 : sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_find_entering_spec _ _ _ _ _ _ _ _ _ _ _ _ 1 _ |- _ => pose proof H as HE end.
  unfold simplex_find_entering_spec, simplex_enter_result in HE.
  destruct HE as [[_ [HE _]]|[j [HJ [_ [[_ [HE HOBS]]|[HF _]]]]]]; try lia.
  subst j.
  unfold simplex_enter_observations, simplex_enter_column in HOBS.
  destruct (Z.eqb (Znth entering CIB 0) 0) eqn:HBASIC; cbn in HOBS.
  - apply Z.eqb_eq in HBASIC. exact HBASIC.
  - discriminate.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_8 : sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  intros i k HK. apply HZERO; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_9 : sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  intros k HK. specialize (HRAT k ltac:(replace V_normal_state with (I_normal_state + M_normal_state) in HK by lia; replace (M_normal_state + I_normal_state) with (I_normal_state + M_normal_state) in HK by lia; exact HK)).
  unfold simplex_solve_rat in HRAT. tauto.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_10 : sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  intros k HK. specialize (HRAT k ltac:(replace V_normal_state with (I_normal_state + M_normal_state) in HK by lia; replace (M_normal_state + I_normal_state) with (I_normal_state + M_normal_state) in HK by lia; exact HK)).
  unfold simplex_solve_rat in HRAT. tauto.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_11 : sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  intros k HK.
  specialize (HMARK k ltac:(lia)).
  destruct HMARK as [HR [_ [_ [HIFF _]]]]. split; [exact HR|].
  intros HNZ. assert (HEQ:Znth k CIB 0=1) by lia.
  apply HIFF in HEQ. destruct HEQ as [i [HI HEQ]]. rewrite <- HEQ.
  unfold Znth. apply nth_In. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. rewrite Zlength_correct in HB. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_12 : sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  intros k HK. specialize (HBAS k HK). replace V_normal_state with (I_normal_state + M_normal_state) by lia. exact HBAS.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_13 : sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_find_entering_spec _ _ _ _ _ _ _ _ _ _ _ _ 1 _ |- _ => pose proof H as HE end.
  unfold simplex_find_entering_spec, simplex_enter_result in HE.
  destruct HE as [[_ [HE _]]|[j [HJ [_ [[_ [HE HOBS]]|[HF _]]]]]]; try lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_6_normal_state_pure : sx_solve_partial_solve_wit_6_normal_state_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_1.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_2.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_3.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_4.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_5.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_6.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_7.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_8.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_9.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_10.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_11.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_12.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_13.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_1 : sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_find_entering_spec _ _ _ _ _ _ _ _ _ _ _ _ 1 _ |- _ => pose proof H as HE end.
  unfold simplex_find_entering_spec, simplex_enter_result in HE.
  destruct HE as [[_ [HE _]]|[j [HJ [_ [[_ [HE HOBS]]|[HF _]]]]]]; try lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_2 : sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  exact HN.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_3 : sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  exact HD.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_4 : sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  exact HND.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_5 : sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  intros k HK. specialize (HBAS k HK). replace (M_normal_state + I_normal_state) with (I_normal_state + M_normal_state) by lia. exact HBAS.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_6 : sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  intros k HK.
  specialize (HMARK k ltac:(lia)).
  destruct HMARK as [HR [_ [_ [HIFF _]]]]. split; [exact HR|].
  intros HNZ. assert (HEQ:Znth k CIB 0=1) by lia.
  apply HIFF in HEQ. destruct HEQ as [i [HI HEQ]]. rewrite <- HEQ.
  unfold Znth. apply nth_In. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. rewrite Zlength_correct in HB. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_7 : sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_find_entering_spec _ _ _ _ _ _ _ _ _ _ _ _ 1 _ |- _ => pose proof H as HE end.
  unfold simplex_find_entering_spec, simplex_enter_result in HE.
  destruct HE as [[_ [HE _]]|[j [HJ [_ [[_ [HE HOBS]]|[HF _]]]]]]; try lia.
  subst j.
  unfold simplex_enter_observations, simplex_enter_column in HOBS.
  destruct (Z.eqb (Znth entering CIB 0) 0) eqn:HBASIC; cbn in HOBS.
  - apply Z.eqb_eq in HBASIC. exact HBASIC.
  - discriminate.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_8 : sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  intros i k HK. apply HZERO; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_9 : sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  intros k HK. specialize (HRAT k ltac:(replace V_normal_state with (I_normal_state + M_normal_state) in HK by lia; replace (M_normal_state + I_normal_state) with (I_normal_state + M_normal_state) in HK by lia; exact HK)).
  unfold simplex_solve_rat in HRAT. tauto.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_10 : sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  intros k HK. specialize (HRAT k ltac:(replace V_normal_state with (I_normal_state + M_normal_state) in HK by lia; replace (M_normal_state + I_normal_state) with (I_normal_state + M_normal_state) in HK by lia; exact HK)).
  unfold simplex_solve_rat in HRAT. tauto.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_11 : sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  intros k HK.
  specialize (HMARK k ltac:(lia)).
  destruct HMARK as [HR [_ [_ [HIFF _]]]]. split; [exact HR|].
  intros HNZ. assert (HEQ:Znth k CIB 0=1) by lia.
  apply HIFF in HEQ. destruct HEQ as [i [HI HEQ]]. rewrite <- HEQ.
  unfold Znth. apply nth_In. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. rewrite Zlength_correct in HB. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_12 : sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_solve_normal _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HN end.
  unfold simplex_solve_normal, simplex_solve_pack in HN; cbn zeta in HN.
  destruct HN as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HMARK [HRAT [HZERO HREST]]]]]]]]]]]]]]]]].
  intros k HK. specialize (HBAS k HK). replace V_normal_state with (I_normal_state + M_normal_state) by lia. exact HBAS.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_13 : sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.

  match goal with H : simplex_find_entering_spec _ _ _ _ _ _ _ _ _ _ _ _ 1 _ |- _ => pose proof H as HE end.
  unfold simplex_find_entering_spec, simplex_enter_result in HE.
  destruct HE as [[_ [HE _]]|[j [HJ [_ [[_ [HE HOBS]]|[HF _]]]]]]; try lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_7_normal_state_pure : sx_solve_partial_solve_wit_7_normal_state_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_1.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_2.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_3.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_4.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_5.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_6.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_7.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_8.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_9.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_10.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_11.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_12.
  - Goal_apply proof_of_sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_13.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_1 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 apply solve_matrix_length; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_2 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 apply solve_matrix_length; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_3 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 apply solve_rhs_length; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_4 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_4.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 apply solve_rhs_length; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_5 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_5.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
pose proof PreH32 as Hnormal.
 unfold simplex_solve_normal, simplex_solve_pack in Hnormal. cbn zeta in Hnormal.
 destruct Hnormal as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HVAR HREST]]]]]]]]]]]]]]].
unfold simplex_pivot_basis. rewrite Z.eqb_refl.
 intros k HK. destruct (Z.eq_dec row k) as [E|E].
 - subst k. rewrite Znth_replace_Znth_Same by lia. lia.
 - rewrite Znth_replace_Znth_Diff by lia. destruct (HBAS k HK). lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_6 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_6.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
apply matrix_prop__recompute_preconditions; try lia.
 intros k HK. pose proof (PreH50 k ltac:(first [exact HK | rewrite <-PreH25; exact HK | rewrite PreH25; exact HK])) as HP.
try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_7 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_7.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
apply matrix_prop__recompute_preconditions; try lia.
 intros k HK. pose proof (PreH50 k ltac:(first [exact HK | rewrite <-PreH25; exact HK | rewrite PreH25; exact HK])) as HP.
try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_8 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_8.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
apply matrix_prop__recompute_preconditions; try lia.
 intros k HK. pose proof (PreH50 k ltac:(first [exact HK | rewrite <-PreH25; exact HK | rewrite PreH25; exact HK])) as HP.
 try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_9 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_9.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
apply matrix_prop__recompute_preconditions; try lia.
 intros k HK. pose proof (PreH50 k ltac:(first [exact HK | rewrite <-PreH25; exact HK | rewrite PreH25; exact HK])) as HP.
 try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_10 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_10.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
apply rhs_prop__recompute_preconditions; try lia.
 intros k HK. pose proof (PreH50 k (simplex_pivot_rhs_active _ _ _ HK)) as HP.
try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_11 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_11.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
apply rhs_prop__recompute_preconditions; try lia.
 intros k HK. pose proof (PreH50 k (simplex_pivot_rhs_active _ _ _ HK)) as HP.
try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_12 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_12.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
apply rhs_prop__recompute_preconditions; try lia.
 intros k HK. pose proof (PreH50 k (simplex_pivot_rhs_active _ _ _ HK)) as HP.
rewrite (solve_den_default PD k) by (auto; lia). try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_13 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_13.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
apply rhs_prop__recompute_preconditions; try lia.
 intros k HK. pose proof (PreH50 k (simplex_pivot_rhs_active _ _ _ HK)) as HP.
rewrite (solve_den_default PD k) by (auto; lia). try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_14 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_14.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
pose proof PreH32 as Hnormal.
 unfold simplex_solve_normal, simplex_solve_pack in Hnormal. cbn zeta in Hnormal.
 destruct Hnormal as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HVAR HREST]]]]]]]]]]]]]]].
eapply (repair_prop__recompute_preconditions _ _ _ _ (M_normal_state+I_normal_state)); try lia.
- intros j HJ. specialize (HVAR j ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_15 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_15.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
pose proof PreH32 as Hnormal.
 unfold simplex_solve_normal, simplex_solve_pack in Hnormal. cbn zeta in Hnormal.
 destruct Hnormal as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HVAR HREST]]]]]]]]]]]]]]].
eapply (repair_prop__recompute_preconditions _ _ _ _ (M_normal_state+I_normal_state)); try lia.
- intros j HJ. specialize (HVAR j ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_16 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_16.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
pose proof PreH32 as Hnormal.
 unfold simplex_solve_normal, simplex_solve_pack in Hnormal. cbn zeta in Hnormal.
 destruct Hnormal as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HVAR HREST]]]]]]]]]]]]]]].
eapply (repair_prop__recompute_preconditions _ _ _ _ (M_normal_state+I_normal_state)); try lia.
- intros j HJ. specialize (HVAR j ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_17 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_17.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
pose proof PreH32 as Hnormal.
 unfold simplex_solve_normal, simplex_solve_pack in Hnormal. cbn zeta in Hnormal.
 destruct Hnormal as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HVAR HREST]]]]]]]]]]]]]]].
eapply (repair_prop__recompute_preconditions _ _ _ _ (M_normal_state+I_normal_state)); try lia.
- intros j HJ. specialize (HVAR j ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_18 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_18.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
pose proof PreH32 as Hnormal.
 unfold simplex_solve_normal, simplex_solve_pack in Hnormal. cbn zeta in Hnormal.
 destruct Hnormal as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HVAR HREST]]]]]]]]]]]]]]].
unfold simplex_solve_repair. rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_19 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_19.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
pose proof PreH32 as Hnormal.
 unfold simplex_solve_normal, simplex_solve_pack in Hnormal. cbn zeta in Hnormal.
 destruct Hnormal as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HVAR HREST]]]]]]]]]]]]]]].
unfold simplex_solve_repair. rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_20 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_20.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
pose proof PreH32 as Hnormal.
 unfold simplex_solve_normal, simplex_solve_pack in Hnormal. cbn zeta in Hnormal.
 destruct Hnormal as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HVAR HREST]]]]]]]]]]]]]]].
unfold simplex_solve_repair. rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_21 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_21.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
pose proof PreH32 as Hnormal.
 unfold simplex_solve_normal, simplex_solve_pack in Hnormal. cbn zeta in Hnormal.
 destruct Hnormal as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HVAR HREST]]]]]]]]]]]]]]].
unfold simplex_solve_repair. rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_22 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_22.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
pose proof PreH32 as Hnormal.
 unfold simplex_solve_normal, simplex_solve_pack in Hnormal. cbn zeta in Hnormal.
 destruct Hnormal as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HVAR HREST]]]]]]]]]]]]]]].
eapply (repair_prop__recompute_preconditions _ _ _ _ (M_normal_state+I_normal_state)); try lia.
- intros j HJ. specialize (HVAR j ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_23 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_23.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
pose proof PreH32 as Hnormal.
 unfold simplex_solve_normal, simplex_solve_pack in Hnormal. cbn zeta in Hnormal.
 destruct Hnormal as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HVAR HREST]]]]]]]]]]]]]]].
eapply (repair_prop__recompute_preconditions _ _ _ _ (M_normal_state+I_normal_state)); try lia.
- intros j HJ. specialize (HVAR j ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_24 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_24.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
pose proof PreH32 as Hnormal.
 unfold simplex_solve_normal, simplex_solve_pack in Hnormal. cbn zeta in Hnormal.
 destruct Hnormal as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HVAR HREST]]]]]]]]]]]]]]].
eapply (repair_prop__recompute_preconditions _ _ _ _ (M_normal_state+I_normal_state)); try lia.
- intros j HJ. specialize (HVAR j ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_25 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_25.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
pose proof PreH32 as Hnormal.
 unfold simplex_solve_normal, simplex_solve_pack in Hnormal. cbn zeta in Hnormal.
 destruct Hnormal as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HVAR HREST]]]]]]]]]]]]]]].
eapply (repair_prop__recompute_preconditions _ _ _ _ (M_normal_state+I_normal_state)); try lia.
- intros j HJ. specialize (HVAR j ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
- specialize (HVAR leaving ltac:(lia)). unfold simplex_solve_rat in HVAR. try apply Z.le_ge; lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_26 : sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_26.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
pose proof PreH32 as Hnormal.
 unfold simplex_solve_normal, simplex_solve_pack in Hnormal. cbn zeta in Hnormal.
 destruct Hnormal as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS [HVAR HREST]]]]]]]]]]]]]]].
unfold simplex_pivot_basis. rewrite Z.eqb_refl.
 intros k HK. destruct (Z.eq_dec row k) as [E|E].
 - subst k. rewrite Znth_replace_Znth_Same by lia. lia.
 - rewrite Znth_replace_Znth_Diff by lia. destruct (HBAS k HK). lia.
Qed.

Lemma proof_of_sx_solve_partial_solve_wit_10_normal_state_pure : sx_solve_partial_solve_wit_10_normal_state_pure.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_1.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_2.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_3.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_4.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_5.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_6.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_7.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_8.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_9.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_10.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_11.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_12.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_13.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_14.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_15.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_16.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_17.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_18.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_19.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_20.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_21.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_22.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_23.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_24.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_25.
 Goal_apply proof_of_sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_26.
Qed.

