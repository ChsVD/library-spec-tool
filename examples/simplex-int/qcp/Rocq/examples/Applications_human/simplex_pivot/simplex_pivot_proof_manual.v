From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_pivot Require Import simplex_pivot_goal.
From SimpleC.EE.Applications_human.simplex_pivot Require Import simplex_pivot_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_rat_div.simplex_rat_div_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_mul.simplex_rat_mul_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_add.simplex_rat_add_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_zero.simplex_rat_zero_lib.
Require Import SimpleC.EE.Applications_human.simplex_pivot.simplex_pivot_lib.
Local Open Scope sac.

Lemma proof_of_sx_pivot_entail_wit_1_split_goal_1 : sx_pivot_entail_wit_1_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 pose proof (PreH23 (16+R_tableau_pivot*24+E_tableau_pivot) (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot ltac:(lia) ltac:(lia))) as Hb.
 tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_1_split_goal_2 : sx_pivot_entail_wit_1_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 pose proof (PreH23 (16+R_tableau_pivot*24+E_tableau_pivot) (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot ltac:(lia) ltac:(lia))) as Hb.
 tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_1_split_goal_3 : sx_pivot_entail_wit_1_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 pose proof (PreH23 (16+R_tableau_pivot*24+E_tableau_pivot) (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot ltac:(lia) ltac:(lia))) as Hb.
 tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_1_split_goal_4 : sx_pivot_entail_wit_1_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 pose proof (PreH23 (16+R_tableau_pivot*24+E_tableau_pivot) (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot ltac:(lia) ltac:(lia))) as Hb.
 tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_1_split_goal_5 : sx_pivot_entail_wit_1_split_goal_5.
Proof.
LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_1_split_goal_6 : sx_pivot_entail_wit_1_split_goal_6.
Proof.
LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_1_split_goal_7 : sx_pivot_entail_wit_1_split_goal_7.
Proof.
LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_1_split_goal_8 : sx_pivot_entail_wit_1_split_goal_8.
Proof.
LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_1_split_goal_spatial : sx_pivot_entail_wit_1_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 rewrite PreH5.
 sep_apply_l_atomic (native_focus_a__entry_focus S_tableau_pivot M_tableau_pivot V_tableau_pivot N_tableau_pivot D_tableau_pivot R_tableau_pivot E_tableau_pivot ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 replace (sizeof("SxRat")*24) with (24*sizeof("SxRat")) by ring.
 csimpl. sepcon_right_assoc.
 repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end.
 reflexivity.
Qed.

Lemma proof_of_sx_pivot_entail_wit_1 : sx_pivot_entail_wit_1.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_pivot_entail_wit_1_split_goal_spatial.
 - Goal_apply proof_of_sx_pivot_entail_wit_1_split_goal_1.
 - Goal_apply proof_of_sx_pivot_entail_wit_1_split_goal_2.
 - Goal_apply proof_of_sx_pivot_entail_wit_1_split_goal_3.
 - Goal_apply proof_of_sx_pivot_entail_wit_1_split_goal_4.
 - Goal_apply proof_of_sx_pivot_entail_wit_1_split_goal_5.
 - Goal_apply proof_of_sx_pivot_entail_wit_1_split_goal_6.
 - Goal_apply proof_of_sx_pivot_entail_wit_1_split_goal_7.
 - Goal_apply proof_of_sx_pivot_entail_wit_1_split_goal_8.
Qed.

Lemma proof_of_sx_pivot_entail_wit_2_split_goal_1 : sx_pivot_entail_wit_2_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 pose proof (PreH20 R_tableau_pivot (simplex_pivot_rhs_active M_tableau_pivot V_tableau_pivot R_tableau_pivot ltac:(lia))) as Hb.
 tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_2_split_goal_2 : sx_pivot_entail_wit_2_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 pose proof (PreH20 R_tableau_pivot (simplex_pivot_rhs_active M_tableau_pivot V_tableau_pivot R_tableau_pivot ltac:(lia))) as Hb.
 tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_2_split_goal_3 : sx_pivot_entail_wit_2_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 pose proof (PreH20 R_tableau_pivot (simplex_pivot_rhs_active M_tableau_pivot V_tableau_pivot R_tableau_pivot ltac:(lia))) as Hb.
 tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_2_split_goal_4 : sx_pivot_entail_wit_2_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 pose proof (PreH20 R_tableau_pivot (simplex_pivot_rhs_active M_tableau_pivot V_tableau_pivot R_tableau_pivot ltac:(lia))) as Hb.
 tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_2_split_goal_5 : sx_pivot_entail_wit_2_split_goal_5.
Proof.
LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_2_split_goal_6 : sx_pivot_entail_wit_2_split_goal_6.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 match goal with H:forall k:Z, 0<=k< ?m -> _ |- _ =>
 pose proof (H R_tableau_pivot ltac:(lia)) as Hb end.
 subst leaving. intuition congruence.
Qed.

Lemma proof_of_sx_pivot_entail_wit_2_split_goal_7 : sx_pivot_entail_wit_2_split_goal_7.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 match goal with H:forall k:Z, 0<=k< ?m -> _ |- _ =>
 pose proof (H R_tableau_pivot ltac:(lia)) as Hb end.
 subst leaving. intuition congruence.
Qed.

Lemma proof_of_sx_pivot_entail_wit_2_split_goal_8 : sx_pivot_entail_wit_2_split_goal_8.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 match goal with H:forall k:Z, 0<=k< ?m -> _ |- _ =>
 pose proof (H R_tableau_pivot ltac:(lia)) as Hb end.
 subst leaving. intuition congruence.
Qed.

Lemma proof_of_sx_pivot_entail_wit_2_split_goal_9 : sx_pivot_entail_wit_2_split_goal_9.
Proof.
LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_2_split_goal_10 : sx_pivot_entail_wit_2_split_goal_10.
Proof.
LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_2_split_goal_11 : sx_pivot_entail_wit_2_split_goal_11.
Proof.
LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_2_split_goal_12 : sx_pivot_entail_wit_2_split_goal_12.
Proof.
LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; auto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_2_split_goal_spatial : sx_pivot_entail_wit_2_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 replace (24*sizeof("SxRat")) with (sizeof("SxRat")*24) by ring.
 sepcon_right_assoc.
 sep_apply_l_atomic (native_merge_a__entry_focus S_tableau_pivot M_tableau_pivot V_tableau_pivot N_tableau_pivot D_tableau_pivot R_tableau_pivot E_tableau_pivot ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 sep_apply_l_atomic (native_focus_rhs__entry_focus S_tableau_pivot M_tableau_pivot V_tableau_pivot N_tableau_pivot D_tableau_pivot R_tableau_pivot ltac:(lia) ltac:(lia) ltac:(lia)).
 sepcon_right_assoc. reflexivity.
Qed.

Lemma proof_of_sx_pivot_entail_wit_2 : sx_pivot_entail_wit_2.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_pivot_entail_wit_2_split_goal_spatial.
 - Goal_apply proof_of_sx_pivot_entail_wit_2_split_goal_1.
 - Goal_apply proof_of_sx_pivot_entail_wit_2_split_goal_2.
 - Goal_apply proof_of_sx_pivot_entail_wit_2_split_goal_3.
 - Goal_apply proof_of_sx_pivot_entail_wit_2_split_goal_4.
 - Goal_apply proof_of_sx_pivot_entail_wit_2_split_goal_5.
 - Goal_apply proof_of_sx_pivot_entail_wit_2_split_goal_6.
 - Goal_apply proof_of_sx_pivot_entail_wit_2_split_goal_7.
 - Goal_apply proof_of_sx_pivot_entail_wit_2_split_goal_8.
 - Goal_apply proof_of_sx_pivot_entail_wit_2_split_goal_9.
 - Goal_apply proof_of_sx_pivot_entail_wit_2_split_goal_10.
 - Goal_apply proof_of_sx_pivot_entail_wit_2_split_goal_11.
 - Goal_apply proof_of_sx_pivot_entail_wit_2_split_goal_12.
Qed.

Lemma proof_of_sx_pivot_entail_wit_3_1 : sx_pivot_entail_wit_3_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(Hactive:In R_tableau_pivot (simplex_pivot_slots M_tableau_pivot V_tableau_pivot)) by(apply simplex_pivot_rhs_active;lia).
 assert(Hkb:0<=R_tableau_pivot<400) by(eapply simplex_pivot_slots_bounds;eauto;lia).
 assert(Hflag:simplex_rat_div_flag (Znth R_tableau_pivot CN_2 0)(Znth R_tableau_pivot CD_2 1) (Znth (16+R_tableau_pivot*24+E_tableau_pivot) N_tableau_pivot 0)(Znth (16+R_tableau_pivot*24+E_tableau_pivot) D_tableau_pivot 1)=1) by congruence.
 assert(Hgcd:Z.gcd(Z.abs(-P)) Q=1). { rewrite Z.abs_opp. exact PreH9. }
 assert(Hnew:forall k, In k (simplex_pivot_slots M_tableau_pivot V_tableau_pivot) ->
 ((((-INT_MAX<=Znth k(replace_Znth R_tableau_pivot (-P) CN_2)0 /\ Znth k(replace_Znth R_tableau_pivot (-P) CN_2)0<=INT_MAX) /\ 1<=Znth k(replace_Znth R_tableau_pivot Q CD_2)1) /\ Znth k(replace_Znth R_tableau_pivot Q CD_2)1<=INT_MAX) /\ Z.gcd(Z.abs(Znth k(replace_Znth R_tableau_pivot (-P) CN_2)0))(Znth k(replace_Znth R_tableau_pivot Q CD_2)1)=1)).
 { intros k HK. pose proof(put_good__row_division M_tableau_pivot V_tableau_pivot CN_2 CD_2 R_tableau_pivot (-P) Q ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) Hkb ltac:(lia) ltac:(lia) Hgcd ltac:(intros x Hx; specialize(PreH35 x Hx);tauto) k HK) as HG. tauto. }
 assert(Hprogress:simplex_pivot_row_progress N_tableau_pivot D_tableau_pivot R_tableau_pivot E_tableau_pivot 0 (replace_Znth R_tableau_pivot (-P) CN_2)(replace_Znth R_tableau_pivot Q CD_2)).
 { unfold simplex_pivot_row_progress,simplex_pivot_row_prefix.
   change (simplex_pivot_start N_tableau_pivot D_tableau_pivot R_tableau_pivot E_tableau_pivot = (1,(replace_Znth R_tableau_pivot (-P) CN_2,replace_Znth R_tableau_pivot Q CD_2))).
   unfold simplex_pivot_start. pose proof (div_update__row_division (Znth (16+R_tableau_pivot*24+E_tableau_pivot) N_tableau_pivot 0) (Znth (16+R_tableau_pivot*24+E_tableau_pivot) D_tableau_pivot 1) R_tableau_pivot CN_2 CD_2 P Q Hflag PreH4) as HE.
   rewrite PreH36,PreH37 in HE. rewrite PreH36,PreH37. exact HE. }
 Exists (replace_Znth R_tableau_pivot Q CD_2)(replace_Znth R_tableau_pivot (-P) CN_2). split_pure_spatial.
 - pose proof(memory_update__row_division S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 R_tableau_pivot (-P) Q ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) Hactive) as HH.
   rewrite native_rhs__row_division in HH by lia.
   sepcon_right_assoc. sep_apply_l_atomic HH. cancel.
 - split_pures; dump_pre_spatial; try assumption; try (rewrite Zlength_replace_Znth; assumption); try lia; tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_3_2 : sx_pivot_entail_wit_3_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(Hactive:In R_tableau_pivot (simplex_pivot_slots M_tableau_pivot V_tableau_pivot)) by(apply simplex_pivot_rhs_active;lia).
 assert(Hkb:0<=R_tableau_pivot<400) by(eapply simplex_pivot_slots_bounds;eauto;lia).
 assert(Hflag:simplex_rat_div_flag (Znth R_tableau_pivot CN_2 0)(Znth R_tableau_pivot CD_2 1) (Znth (16+R_tableau_pivot*24+E_tableau_pivot) N_tableau_pivot 0)(Znth (16+R_tableau_pivot*24+E_tableau_pivot) D_tableau_pivot 1)=1) by congruence.
 assert(Hgcd:Z.gcd(Z.abs(-P)) Q=1). { rewrite Z.abs_opp. exact PreH9. }
 assert(Hnew:forall k, In k (simplex_pivot_slots M_tableau_pivot V_tableau_pivot) ->
 ((((-INT_MAX<=Znth k(replace_Znth R_tableau_pivot (-P) CN_2)0 /\ Znth k(replace_Znth R_tableau_pivot (-P) CN_2)0<=INT_MAX) /\ 1<=Znth k(replace_Znth R_tableau_pivot Q CD_2)1) /\ Znth k(replace_Znth R_tableau_pivot Q CD_2)1<=INT_MAX) /\ Z.gcd(Z.abs(Znth k(replace_Znth R_tableau_pivot (-P) CN_2)0))(Znth k(replace_Znth R_tableau_pivot Q CD_2)1)=1)).
 { intros k HK. pose proof(put_good__row_division M_tableau_pivot V_tableau_pivot CN_2 CD_2 R_tableau_pivot (-P) Q ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) Hkb ltac:(lia) ltac:(lia) Hgcd ltac:(intros x Hx; specialize(PreH34 x Hx);tauto) k HK) as HG. tauto. }
 assert(Hprogress:simplex_pivot_row_progress N_tableau_pivot D_tableau_pivot R_tableau_pivot E_tableau_pivot 0 (replace_Znth R_tableau_pivot (-P) CN_2)(replace_Znth R_tableau_pivot Q CD_2)).
 { unfold simplex_pivot_row_progress,simplex_pivot_row_prefix.
   change (simplex_pivot_start N_tableau_pivot D_tableau_pivot R_tableau_pivot E_tableau_pivot = (1,(replace_Znth R_tableau_pivot (-P) CN_2,replace_Znth R_tableau_pivot Q CD_2))).
   unfold simplex_pivot_start. pose proof (div_update__row_division (Znth (16+R_tableau_pivot*24+E_tableau_pivot) N_tableau_pivot 0) (Znth (16+R_tableau_pivot*24+E_tableau_pivot) D_tableau_pivot 1) R_tableau_pivot CN_2 CD_2 P Q Hflag PreH4) as HE.
   rewrite PreH35,PreH36 in HE. rewrite PreH35,PreH36. exact HE. }
 Exists (replace_Znth R_tableau_pivot Q CD_2)(replace_Znth R_tableau_pivot (-P) CN_2). split_pure_spatial.
 - pose proof(memory_update__row_division S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 R_tableau_pivot (-P) Q ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) Hactive) as HH.
   rewrite native_rhs__row_division in HH by lia.
   sepcon_right_assoc. sep_apply_l_atomic HH. cancel.
 - split_pures; dump_pre_spatial; try assumption; try (rewrite Zlength_replace_Znth; assumption); try lia; tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_4 : sx_pivot_entail_wit_4.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(Hactive:In (16+R_tableau_pivot*24+j)(simplex_pivot_slots M_tableau_pivot V_tableau_pivot)) by(apply simplex_pivot_a_active;lia).
 pose proof(PreH24 _ Hactive) as Hcell.
 Exists CD_2 CN_2. split_pure_spatial.
 - pose proof(memory_focus__row_division S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 (16+R_tableau_pivot*24+j) ltac:(lia) ltac:(lia) Hactive) as HH.
   rewrite native_a__row_division in HH by lia.
   sepcon_right_assoc. sep_apply_l_atomic HH. cancel.
 - split_pures; dump_pre_spatial; try assumption; try lia; tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_5_1 : sx_pivot_entail_wit_5_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(Hactive:In (16+R_tableau_pivot*24+j) (simplex_pivot_slots M_tableau_pivot V_tableau_pivot)) by(apply simplex_pivot_a_active;lia).
 assert(Hkb:0<=(16+R_tableau_pivot*24+j)<400) by(eapply simplex_pivot_slots_bounds;eauto;lia).
 assert(Hflag:simplex_rat_div_flag (Znth (16+R_tableau_pivot*24+j) CN_2 0)(Znth (16+R_tableau_pivot*24+j) CD_2 1) (Znth (16+R_tableau_pivot*24+E_tableau_pivot) N_tableau_pivot 0)(Znth (16+R_tableau_pivot*24+E_tableau_pivot) D_tableau_pivot 1)=1) by congruence.
 assert(Hgcd:Z.gcd(Z.abs(-P)) Q=1). { rewrite Z.abs_opp. exact PreH9. }
 assert(Hnew:forall k, In k (simplex_pivot_slots M_tableau_pivot V_tableau_pivot) ->
 ((((-INT_MAX<=Znth k(replace_Znth (16+R_tableau_pivot*24+j) (-P) CN_2)0 /\ Znth k(replace_Znth (16+R_tableau_pivot*24+j) (-P) CN_2)0<=INT_MAX) /\ 1<=Znth k(replace_Znth (16+R_tableau_pivot*24+j) Q CD_2)1) /\ Znth k(replace_Znth (16+R_tableau_pivot*24+j) Q CD_2)1<=INT_MAX) /\ Z.gcd(Z.abs(Znth k(replace_Znth (16+R_tableau_pivot*24+j) (-P) CN_2)0))(Znth k(replace_Znth (16+R_tableau_pivot*24+j) Q CD_2)1)=1)).
 { intros k HK. pose proof(put_good__row_division M_tableau_pivot V_tableau_pivot CN_2 CD_2 (16+R_tableau_pivot*24+j) (-P) Q ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) Hkb ltac:(lia) ltac:(lia) Hgcd ltac:(intros x Hx; specialize(PreH36 x Hx);tauto) k HK) as HG. tauto. }
 assert(Hprogress:simplex_pivot_row_progress N_tableau_pivot D_tableau_pivot R_tableau_pivot E_tableau_pivot (j+1) (replace_Znth (16+R_tableau_pivot*24+j) (-P) CN_2)(replace_Znth (16+R_tableau_pivot*24+j) Q CD_2)).
 { unfold simplex_pivot_row_progress in *. rewrite simplex_pivot_row_step by lia. rewrite PreH37.
   unfold simplex_pivot_row_column. assert (Ej:Z.eqb j E_tableau_pivot=false) by(apply Z.eqb_neq;exact PreH13).
   rewrite Ej. apply div_update__row_division;assumption. }
 Exists (replace_Znth (16+R_tableau_pivot*24+j) Q CD_2)(replace_Znth (16+R_tableau_pivot*24+j) (-P) CN_2). split_pure_spatial.
 - pose proof(memory_update__row_division S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 (16+R_tableau_pivot*24+j) (-P) Q ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) Hactive) as HH.
   rewrite native_a__row_division in HH by lia.
   sepcon_right_assoc. sep_apply_l_atomic HH. cancel.
 - split_pures; dump_pre_spatial; try assumption; try (rewrite Zlength_replace_Znth; assumption); try lia; tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_5_2 : sx_pivot_entail_wit_5_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(Hactive:In (16+R_tableau_pivot*24+j) (simplex_pivot_slots M_tableau_pivot V_tableau_pivot)) by(apply simplex_pivot_a_active;lia).
 assert(Hkb:0<=(16+R_tableau_pivot*24+j)<400) by(eapply simplex_pivot_slots_bounds;eauto;lia).
 assert(Hflag:simplex_rat_div_flag (Znth (16+R_tableau_pivot*24+j) CN_2 0)(Znth (16+R_tableau_pivot*24+j) CD_2 1) (Znth (16+R_tableau_pivot*24+E_tableau_pivot) N_tableau_pivot 0)(Znth (16+R_tableau_pivot*24+E_tableau_pivot) D_tableau_pivot 1)=1) by congruence.
 assert(Hgcd:Z.gcd(Z.abs(-P)) Q=1). { rewrite Z.abs_opp. exact PreH9. }
 assert(Hnew:forall k, In k (simplex_pivot_slots M_tableau_pivot V_tableau_pivot) ->
 ((((-INT_MAX<=Znth k(replace_Znth (16+R_tableau_pivot*24+j) (-P) CN_2)0 /\ Znth k(replace_Znth (16+R_tableau_pivot*24+j) (-P) CN_2)0<=INT_MAX) /\ 1<=Znth k(replace_Znth (16+R_tableau_pivot*24+j) Q CD_2)1) /\ Znth k(replace_Znth (16+R_tableau_pivot*24+j) Q CD_2)1<=INT_MAX) /\ Z.gcd(Z.abs(Znth k(replace_Znth (16+R_tableau_pivot*24+j) (-P) CN_2)0))(Znth k(replace_Znth (16+R_tableau_pivot*24+j) Q CD_2)1)=1)).
 { intros k HK. pose proof(put_good__row_division M_tableau_pivot V_tableau_pivot CN_2 CD_2 (16+R_tableau_pivot*24+j) (-P) Q ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) Hkb ltac:(lia) ltac:(lia) Hgcd ltac:(intros x Hx; specialize(PreH35 x Hx);tauto) k HK) as HG. tauto. }
 assert(Hprogress:simplex_pivot_row_progress N_tableau_pivot D_tableau_pivot R_tableau_pivot E_tableau_pivot (j+1) (replace_Znth (16+R_tableau_pivot*24+j) (-P) CN_2)(replace_Znth (16+R_tableau_pivot*24+j) Q CD_2)).
 { unfold simplex_pivot_row_progress in *. rewrite simplex_pivot_row_step by lia. rewrite PreH36.
   unfold simplex_pivot_row_column. assert (Ej:Z.eqb j E_tableau_pivot=false) by(apply Z.eqb_neq;exact PreH12).
   rewrite Ej. apply div_update__row_division;assumption. }
 Exists (replace_Znth (16+R_tableau_pivot*24+j) Q CD_2)(replace_Znth (16+R_tableau_pivot*24+j) (-P) CN_2). split_pure_spatial.
 - pose proof(memory_update__row_division S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 (16+R_tableau_pivot*24+j) (-P) Q ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) Hactive) as HH.
   rewrite native_a__row_division in HH by lia.
   sepcon_right_assoc. sep_apply_l_atomic HH. cancel.
 - split_pures; dump_pre_spatial; try assumption; try (rewrite Zlength_replace_Znth; assumption); try lia; tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_5_3 : sx_pivot_entail_wit_5_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(Hactive:In (16+R_tableau_pivot*24+j)(simplex_pivot_slots M_tableau_pivot V_tableau_pivot)) by(apply simplex_pivot_a_active;lia).
 assert(Hprogress:simplex_pivot_row_progress N_tableau_pivot D_tableau_pivot R_tableau_pivot E_tableau_pivot (j+1) CN_2 CD_2).
 { unfold simplex_pivot_row_progress in *. rewrite simplex_pivot_row_step by lia. rewrite PreH25.
   unfold simplex_pivot_row_column. rewrite PreH1,Z.eqb_refl. reflexivity. }
 Exists CD_2 CN_2. split_pure_spatial.
 - pose proof(memory_merge__row_division S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 (16+R_tableau_pivot*24+j) ltac:(lia) ltac:(lia) Hactive) as HH.
   rewrite native_a__row_division in HH by lia.
   sepcon_right_assoc. sep_apply_l_atomic HH. cancel.
 - split_pures; dump_pre_spatial; try assumption; try lia; tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_6 : sx_pivot_entail_wit_6.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (j=V_tableau_pivot) by lia. subst j.
 Exists CD_2 CN_2. split_pure_spatial.
 - unfold simplex_pivot_memory, simplex_pivot_except.
   sepcon_right_assoc.
   sep_apply_l_atomic (cell_focus__row_finalize (simplex_pivot_slots M_tableau_pivot V_tableau_pivot)
    (fun k=>simplex_pivot_memory_cell S_tableau_pivot k (Znth k CN_2 0) (Znth k CD_2 1)) (16+R_tableau_pivot*24+leaving)
    (slots_nodup__row_finalize M_tableau_pivot V_tableau_pivot ltac:(lia) ltac:(lia))
    (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot R_tableau_pivot leaving ltac:(lia) ltac:(lia))).
   rewrite matrix_cell__row_finalize by lia.
   csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end.
   try reflexivity.
 - pose proof (PreH24 (16+R_tableau_pivot*24+leaving)
     (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot R_tableau_pivot leaving ltac:(lia) ltac:(lia))).
   split_pures; dump_pre_spatial; try assumption; try lia; tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_7 : sx_pivot_entail_wit_7.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (HB : In (16+R_tableau_pivot*24+leaving) (simplex_pivot_slots M_tableau_pivot V_tableau_pivot)) by (apply simplex_pivot_a_active;lia).
 assert (HE : In (16+R_tableau_pivot*24+E_tableau_pivot) (simplex_pivot_slots M_tableau_pivot V_tableau_pivot)) by (apply simplex_pivot_a_active;lia).
 assert (HKB : 0<=16+R_tableau_pivot*24+leaving<400) by nia.
 assert (HKE : 0<=16+R_tableau_pivot*24+E_tableau_pivot<400) by nia.
 pose proof (good_put__row_finalize M_tableau_pivot V_tableau_pivot CN_2 CD_2
  (16+R_tableau_pivot*24+leaving) P Q ltac:(lia) ltac:(lia) PreH32 PreH33 HKB
  ltac:(lia) ltac:(lia) PreH9 PreH34) as HG.
 pose proof (recip_update__row_finalize N_tableau_pivot D_tableau_pivot CN_2 CD_2
  V_tableau_pivot R_tableau_pivot E_tableau_pivot (16+R_tableau_pivot*24+leaving) P Q
  PreH35 ltac:(lia) PreH4) as HP.
 replace (16+R_tableau_pivot*24+leaving-16-R_tableau_pivot*24) with leaving in HP by ring.
 pose proof (HG (16+R_tableau_pivot*24+E_tableau_pivot) HE) as HGE.
 Exists (replace_Znth (16+R_tableau_pivot*24+leaving) Q CD_2)
  (replace_Znth (16+R_tableau_pivot*24+leaving) P CN_2).
 split_pure_spatial.
 - pose proof (memory_put__row_finalize S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2
    (16+R_tableau_pivot*24+leaving) P Q ltac:(lia) ltac:(lia) PreH32 PreH33 HB) as HM.
   rewrite matrix_cell__row_finalize in HM by lia.
   sepcon_right_assoc. sep_apply_l_atomic HM.
   sepcon_right_assoc. sep_apply_l_atomic (memory_focus__row_finalize S_tableau_pivot M_tableau_pivot V_tableau_pivot
    (replace_Znth (16+R_tableau_pivot*24+leaving) P CN_2) (replace_Znth (16+R_tableau_pivot*24+leaving) Q CD_2)
    (16+R_tableau_pivot*24+E_tableau_pivot) ltac:(lia) ltac:(lia) HE).
   rewrite matrix_cell__row_finalize by lia. csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?A ** _] => progress(cancel A) end end. try reflexivity.
 - split_pures; dump_pre_spatial; rewrite ?Zlength_replace_Znth; try assumption; try lia; tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_8 : sx_pivot_entail_wit_8.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (HE : In (16+R_tableau_pivot*24+E_tableau_pivot) (simplex_pivot_slots M_tableau_pivot V_tableau_pivot)) by (apply simplex_pivot_a_active;lia).
 assert (HKE : 0<=16+R_tableau_pivot*24+E_tableau_pivot<400) by nia.
 assert (HG0 : Z.gcd (Z.abs 0) 1=1) by reflexivity.
 pose proof (good_put__row_finalize M_tableau_pivot V_tableau_pivot CN_2 CD_2
  (16+R_tableau_pivot*24+E_tableau_pivot) 0 1 ltac:(lia) ltac:(lia) PreH21 PreH22 HKE
  ltac:(lia) ltac:(lia) HG0 PreH23) as HG.
 pose proof (zero_update__row_finalize N_tableau_pivot D_tableau_pivot CN_2 CD_2
  V_tableau_pivot R_tableau_pivot E_tableau_pivot leaving PreH24) as HP.
 Exists (replace_Znth (16+R_tableau_pivot*24+E_tableau_pivot) 1 CD_2)
  (replace_Znth (16+R_tableau_pivot*24+E_tableau_pivot) 0 CN_2).
 split_pure_spatial.
 - pose proof (memory_put__row_finalize S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2
    (16+R_tableau_pivot*24+E_tableau_pivot) 0 1 ltac:(lia) ltac:(lia) PreH21 PreH22 HE) as HM.
   rewrite matrix_cell__row_finalize in HM by lia.
   sepcon_right_assoc. sep_apply_l_atomic HM.
   sepcon_right_assoc. sep_apply_l_atomic (store_int_undef_store_int (&( "j" )) V_tableau_pivot).
   csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?A ** _] => progress(cancel A) end end. try reflexivity.
 - split_pures; dump_pre_spatial; rewrite ?Zlength_replace_Znth; try assumption; try lia; tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_9 : sx_pivot_entail_wit_9.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists CD_2 CN_2.
 pose proof (PreH25 _ (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot i E_tableau_pivot ltac:(lia) ltac:(lia))) as G.
 split_pure_spatial.
 - sep_apply (memory_focus__factor_rhs S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 (16+i*24+E_tableau_pivot) ltac:(lia) ltac:(lia) (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot i E_tableau_pivot ltac:(lia) ltac:(lia))).
   rewrite cell_a__factor_rhs by lia. csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end.
   reflexivity.
 - split_pures; dump_pre_spatial; tauto || lia.
Qed.

Lemma proof_of_sx_pivot_entail_wit_10 : sx_pivot_entail_wit_10.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists (Znth (16+i*24+E_tableau_pivot) CD_2 1) (Znth (16+i*24+E_tableau_pivot) CN_2 0) CD_2 CN_2.
 pose proof (PreH23 _ (simplex_pivot_rhs_active M_tableau_pivot V_tableau_pivot i ltac:(lia))) as Gi.
 pose proof (PreH23 _ (simplex_pivot_rhs_active M_tableau_pivot V_tableau_pivot R_tableau_pivot ltac:(lia))) as Gr.
 assert(Hfactor:simplex_pivot_factor N_tableau_pivot D_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot leaving i (Znth (16+i*24+E_tableau_pivot) CN_2 0) (Znth (16+i*24+E_tableau_pivot) CD_2 1)).
 { unfold simplex_pivot_factor. exists CN_2,CD_2. auto. }
 split_pure_spatial.
 - pose proof (memory_merge__factor_rhs S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 (16+i*24+E_tableau_pivot) ltac:(lia) ltac:(lia)
    (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot i E_tableau_pivot ltac:(lia) ltac:(lia))) as HM.
   rewrite cell_a__factor_rhs in HM by lia. sepcon_right_assoc. sep_apply HM.
   sep_apply (memory_focus_pair__factor_rhs S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 i R_tableau_pivot ltac:(lia) ltac:(lia)
   (simplex_pivot_rhs_active M_tableau_pivot V_tableau_pivot i ltac:(lia)) (simplex_pivot_rhs_active M_tableau_pivot V_tableau_pivot R_tableau_pivot ltac:(lia)) ltac:(lia)).
   rewrite !cell_rhs__factor_rhs by lia. csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end.
   reflexivity.
 - split_pures; dump_pre_spatial; tauto || lia.
Qed.

Lemma proof_of_sx_pivot_entail_wit_11_1 : sx_pivot_entail_wit_11_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists FN_2 FD_2 (replace_Znth i Q_2 CD_2) (replace_Znth i P_2 CN_2).
 pose proof (columns_zero__factor_rhs N_tableau_pivot D_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot leaving i FN_2 FD_2 CN_2 CD_2 P Q P_2 Q_2 ltac:(assumption) ltac:(congruence) ltac:(assumption) ltac:(congruence) ltac:(assumption)) as Hcolumns.
 pose proof (active_update__factor_rhs M_tableau_pivot V_tableau_pivot CN_2 CD_2 i P_2 Q_2 ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(assumption)
  ltac:(intros k Hk; pose proof (PreH48 k Hk) as K; tauto)) as Hgood.
 split_pure_spatial.
 - pose proof (memory_update_rhs__factor_rhs S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 i R_tableau_pivot P_2 Q_2 ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia)) as HM.
   rewrite !cell_rhs__factor_rhs in HM by lia.
   sepcon_right_assoc. sep_apply_r_atomic HM.
   sep_apply (store_int_undef_store_int (&(( &( "term" ) )->ₛ "num")) P).
   sep_apply (store_int_undef_store_int (&(( &( "term" ) )->ₛ "den")) Q).
   csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end.
   reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   + rewrite Zlength_replace_Znth. assumption.
   + rewrite Zlength_replace_Znth. assumption.
   + intros k Hk. pose proof(Hgood k Hk) as K. tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_11_2 : sx_pivot_entail_wit_11_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists FN_2 FD_2 (replace_Znth i Q_2 CD_2) (replace_Znth i P_2 CN_2).
 pose proof (columns_zero__factor_rhs N_tableau_pivot D_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot leaving i FN_2 FD_2 CN_2 CD_2 P Q P_2 Q_2 ltac:(assumption) ltac:(congruence) ltac:(assumption) ltac:(congruence) ltac:(assumption)) as Hcolumns.
 pose proof (active_update__factor_rhs M_tableau_pivot V_tableau_pivot CN_2 CD_2 i P_2 Q_2 ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(assumption)
  ltac:(intros k Hk; pose proof (PreH47 k Hk) as K; tauto)) as Hgood.
 split_pure_spatial.
 - pose proof (memory_update_rhs__factor_rhs S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 i R_tableau_pivot P_2 Q_2 ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia)) as HM.
   rewrite !cell_rhs__factor_rhs in HM by lia.
   sepcon_right_assoc. sep_apply_r_atomic HM.
   sep_apply (store_int_undef_store_int (&(( &( "term" ) )->ₛ "num")) P).
   sep_apply (store_int_undef_store_int (&(( &( "term" ) )->ₛ "den")) Q).
   csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end.
   reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   + rewrite Zlength_replace_Znth. assumption.
   + rewrite Zlength_replace_Znth. assumption.
   + intros k Hk. pose proof(Hgood k Hk) as K. tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_11_3 : sx_pivot_entail_wit_11_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists FN_2 FD_2 (replace_Znth i Q_2 CD_2) (replace_Znth i P_2 CN_2).
 pose proof (columns_zero__factor_rhs N_tableau_pivot D_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot leaving i FN_2 FD_2 CN_2 CD_2 P Q P_2 Q_2 ltac:(assumption) ltac:(congruence) ltac:(assumption) ltac:(congruence) ltac:(assumption)) as Hcolumns.
 pose proof (active_update__factor_rhs M_tableau_pivot V_tableau_pivot CN_2 CD_2 i P_2 Q_2 ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(assumption)
  ltac:(intros k Hk; pose proof (PreH47 k Hk) as K; tauto)) as Hgood.
 split_pure_spatial.
 - pose proof (memory_update_rhs__factor_rhs S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 i R_tableau_pivot P_2 Q_2 ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia)) as HM.
   rewrite !cell_rhs__factor_rhs in HM by lia.
   sepcon_right_assoc. sep_apply_r_atomic HM.
   sep_apply (store_int_undef_store_int (&(( &( "term" ) )->ₛ "num")) P).
   sep_apply (store_int_undef_store_int (&(( &( "term" ) )->ₛ "den")) Q).
   csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end.
   reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   + rewrite Zlength_replace_Znth. assumption.
   + rewrite Zlength_replace_Znth. assumption.
   + intros k Hk. pose proof(Hgood k Hk) as K. tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_11_4 : sx_pivot_entail_wit_11_4.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists FN_2 FD_2 (replace_Znth i Q_2 CD_2) (replace_Znth i P_2 CN_2).
 pose proof (columns_zero__factor_rhs N_tableau_pivot D_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot leaving i FN_2 FD_2 CN_2 CD_2 P Q P_2 Q_2 ltac:(assumption) ltac:(congruence) ltac:(assumption) ltac:(congruence) ltac:(assumption)) as Hcolumns.
 pose proof (active_update__factor_rhs M_tableau_pivot V_tableau_pivot CN_2 CD_2 i P_2 Q_2 ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(assumption)
  ltac:(intros k Hk; pose proof (PreH46 k Hk) as K; tauto)) as Hgood.
 split_pure_spatial.
 - pose proof (memory_update_rhs__factor_rhs S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 i R_tableau_pivot P_2 Q_2 ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia)) as HM.
   rewrite !cell_rhs__factor_rhs in HM by lia.
   sepcon_right_assoc. sep_apply_r_atomic HM.
   sep_apply (store_int_undef_store_int (&(( &( "term" ) )->ₛ "num")) P).
   sep_apply (store_int_undef_store_int (&(( &( "term" ) )->ₛ "den")) Q).
   csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end.
   reflexivity.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   + rewrite Zlength_replace_Znth. assumption.
   + rewrite Zlength_replace_Znth. assumption.
   + intros k Hk. pose proof(Hgood k Hk) as K. tauto.
Qed.

Lemma proof_of_sx_pivot_entail_wit_12 : sx_pivot_entail_wit_12.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 pose proof(PreH24 (16+R_tableau_pivot*24+j)
 (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot R_tableau_pivot j ltac:(lia) ltac:(lia))) as Hsrc.
 pose proof(PreH24 (16+i*24+j)
 (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot i j ltac:(lia) ltac:(lia))) as Hdst.
 destruct Hsrc as [[[[Hs1 Hs2] Hs3] Hs4] Hs5].
 destruct Hdst as [[[[Hd1 Hd2] Hd3] Hd4] Hd5].
 Exists FN_2 FD_2 CD_2 CN_2.
 split_pure_spatial.
 - sep_apply(pivot_memory_focus__other_columns S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2
 (16+R_tableau_pivot*24+j)(16+i*24+j)ltac:(lia)ltac:(lia)
 (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot R_tableau_pivot j ltac:(lia)ltac:(lia))
 (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot i j ltac:(lia)ltac:(lia))ltac:(lia)).
   rewrite !pivot_matrix_cell__other_columns by lia.
   csimpl. repeat const_array_simpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => multimatch L with context[?P ** _] => progress(cancel P) end end.
   try reflexivity.
 - split_pures;dump_pre_spatial;auto;lia.
Qed.

Lemma proof_of_sx_pivot_entail_wit_13_1 : sx_pivot_entail_wit_13_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(Hstep:simplex_pivot_columns_progress N_tableau_pivot D_tableau_pivot V_tableau_pivot
 R_tableau_pivot E_tableau_pivot leaving i_2 (j+1) FN_2 FD_2
 (replace_Znth(16+i_2*24+j)P_2 CN_2)(replace_Znth(16+i_2*24+j)Q_2 CD_2)).
 { eapply pivot_column_step__other_columns with (p:=P)(q:=Q);eauto;congruence. }
 pose proof(pivot_good_put__other_columns M_tableau_pivot V_tableau_pivot CN_2 CD_2
 (16+i_2*24+j)P_2 Q_2 ltac:(lia)ltac:(lia)ltac:(assumption)ltac:(assumption)ltac:(lia)
 PreH48 ltac:(lia)ltac:(lia)ltac:(assumption)) as Hgood.
 Exists FN_2 FD_2 (replace_Znth(16+i_2*24+j)Q_2 CD_2)(replace_Znth(16+i_2*24+j)P_2 CN_2).
 split_pure_spatial.
 - sep_apply(store_int_undef_store_int (&(( &( "term" ) )->ₛ "num")) P).
   sep_apply(store_int_undef_store_int (&(( &( "term" ) )->ₛ "den")) Q).
   csimpl. repeat const_array_simpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => multimatch L with context[?X ** _] => progress(cancel X) end end.
   sep_apply_r_atomic(pivot_matrix_update__other_columns S_tableau_pivot M_tableau_pivot V_tableau_pivot
   CN_2 CD_2 R_tableau_pivot i_2 j P_2 Q_2 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)
   ltac:(assumption)ltac:(assumption)).
   rewrite !pivot_matrix_cell__other_columns by lia.
   csimpl. repeat const_array_simpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => multimatch L with context[?X ** _] => progress(cancel X) end end.
   try reflexivity.
 - split_pures;dump_pre_spatial;try assumption;try (rewrite Zlength_replace_Znth by lia);auto;lia.
Qed.

Lemma proof_of_sx_pivot_entail_wit_13_2 : sx_pivot_entail_wit_13_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(Hstep:simplex_pivot_columns_progress N_tableau_pivot D_tableau_pivot V_tableau_pivot
 R_tableau_pivot E_tableau_pivot leaving i_2 (j+1) FN_2 FD_2
 (replace_Znth(16+i_2*24+j)P_2 CN_2)(replace_Znth(16+i_2*24+j)Q_2 CD_2)).
 { eapply pivot_column_step__other_columns with (p:=P)(q:=Q);eauto;congruence. }
 pose proof(pivot_good_put__other_columns M_tableau_pivot V_tableau_pivot CN_2 CD_2
 (16+i_2*24+j)P_2 Q_2 ltac:(lia)ltac:(lia)ltac:(assumption)ltac:(assumption)ltac:(lia)
 PreH47 ltac:(lia)ltac:(lia)ltac:(assumption)) as Hgood.
 Exists FN_2 FD_2 (replace_Znth(16+i_2*24+j)Q_2 CD_2)(replace_Znth(16+i_2*24+j)P_2 CN_2).
 split_pure_spatial.
 - sep_apply(store_int_undef_store_int (&(( &( "term" ) )->ₛ "num")) P).
   sep_apply(store_int_undef_store_int (&(( &( "term" ) )->ₛ "den")) Q).
   csimpl. repeat const_array_simpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => multimatch L with context[?X ** _] => progress(cancel X) end end.
   sep_apply_r_atomic(pivot_matrix_update__other_columns S_tableau_pivot M_tableau_pivot V_tableau_pivot
   CN_2 CD_2 R_tableau_pivot i_2 j P_2 Q_2 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)
   ltac:(assumption)ltac:(assumption)).
   rewrite !pivot_matrix_cell__other_columns by lia.
   csimpl. repeat const_array_simpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => multimatch L with context[?X ** _] => progress(cancel X) end end.
   try reflexivity.
 - split_pures;dump_pre_spatial;try assumption;try (rewrite Zlength_replace_Znth by lia);auto;lia.
Qed.

Lemma proof_of_sx_pivot_entail_wit_13_3 : sx_pivot_entail_wit_13_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(Hstep:simplex_pivot_columns_progress N_tableau_pivot D_tableau_pivot V_tableau_pivot
 R_tableau_pivot E_tableau_pivot leaving i_2 (j+1) FN_2 FD_2
 (replace_Znth(16+i_2*24+j)P_2 CN_2)(replace_Znth(16+i_2*24+j)Q_2 CD_2)).
 { eapply pivot_column_step__other_columns with (p:=P)(q:=Q);eauto;congruence. }
 pose proof(pivot_good_put__other_columns M_tableau_pivot V_tableau_pivot CN_2 CD_2
 (16+i_2*24+j)P_2 Q_2 ltac:(lia)ltac:(lia)ltac:(assumption)ltac:(assumption)ltac:(lia)
 PreH47 ltac:(lia)ltac:(lia)ltac:(assumption)) as Hgood.
 Exists FN_2 FD_2 (replace_Znth(16+i_2*24+j)Q_2 CD_2)(replace_Znth(16+i_2*24+j)P_2 CN_2).
 split_pure_spatial.
 - sep_apply(store_int_undef_store_int (&(( &( "term" ) )->ₛ "num")) P).
   sep_apply(store_int_undef_store_int (&(( &( "term" ) )->ₛ "den")) Q).
   csimpl. repeat const_array_simpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => multimatch L with context[?X ** _] => progress(cancel X) end end.
   sep_apply_r_atomic(pivot_matrix_update__other_columns S_tableau_pivot M_tableau_pivot V_tableau_pivot
   CN_2 CD_2 R_tableau_pivot i_2 j P_2 Q_2 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)
   ltac:(assumption)ltac:(assumption)).
   rewrite !pivot_matrix_cell__other_columns by lia.
   csimpl. repeat const_array_simpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => multimatch L with context[?X ** _] => progress(cancel X) end end.
   try reflexivity.
 - split_pures;dump_pre_spatial;try assumption;try (rewrite Zlength_replace_Znth by lia);auto;lia.
Qed.

Lemma proof_of_sx_pivot_entail_wit_13_4 : sx_pivot_entail_wit_13_4.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(Hstep:simplex_pivot_columns_progress N_tableau_pivot D_tableau_pivot V_tableau_pivot
 R_tableau_pivot E_tableau_pivot leaving i_2 (j+1) FN_2 FD_2
 (replace_Znth(16+i_2*24+j)P_2 CN_2)(replace_Znth(16+i_2*24+j)Q_2 CD_2)).
 { eapply pivot_column_step__other_columns with (p:=P)(q:=Q);eauto;congruence. }
 pose proof(pivot_good_put__other_columns M_tableau_pivot V_tableau_pivot CN_2 CD_2
 (16+i_2*24+j)P_2 Q_2 ltac:(lia)ltac:(lia)ltac:(assumption)ltac:(assumption)ltac:(lia)
 PreH46 ltac:(lia)ltac:(lia)ltac:(assumption)) as Hgood.
 Exists FN_2 FD_2 (replace_Znth(16+i_2*24+j)Q_2 CD_2)(replace_Znth(16+i_2*24+j)P_2 CN_2).
 split_pure_spatial.
 - sep_apply(store_int_undef_store_int (&(( &( "term" ) )->ₛ "num")) P).
   sep_apply(store_int_undef_store_int (&(( &( "term" ) )->ₛ "den")) Q).
   csimpl. repeat const_array_simpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => multimatch L with context[?X ** _] => progress(cancel X) end end.
   sep_apply_r_atomic(pivot_matrix_update__other_columns S_tableau_pivot M_tableau_pivot V_tableau_pivot
   CN_2 CD_2 R_tableau_pivot i_2 j P_2 Q_2 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)
   ltac:(assumption)ltac:(assumption)).
   rewrite !pivot_matrix_cell__other_columns by lia.
   csimpl. repeat const_array_simpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => multimatch L with context[?X ** _] => progress(cancel X) end end.
   try reflexivity.
 - split_pures;dump_pre_spatial;try assumption;try (rewrite Zlength_replace_Znth by lia);auto;lia.
Qed.

Lemma proof_of_sx_pivot_entail_wit_13_5 : sx_pivot_entail_wit_13_5.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(HP:simplex_pivot_columns_progress N_tableau_pivot D_tableau_pivot V_tableau_pivot
 R_tableau_pivot E_tableau_pivot leaving i_2 (j+1) FN_2 FD_2 CN_2 CD_2).
 { eapply pivot_column_skip__other_columns;eauto. }
 Exists FN_2 FD_2 CD_2 CN_2.
 split_pure_spatial.
 - csimpl. repeat const_array_simpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => multimatch L with context[?X ** _] => progress(cancel X) end end.
   sep_apply_r_atomic(pivot_memory_merge__other_columns S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2
 (16+R_tableau_pivot*24+j)(16+i_2*24+j)ltac:(lia)ltac:(lia)
 (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot R_tableau_pivot j ltac:(lia)ltac:(lia))
 (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot i_2 j ltac:(lia)ltac:(lia))ltac:(lia)).
   rewrite !pivot_matrix_cell__other_columns by lia.
   csimpl. repeat const_array_simpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => multimatch L with context[?P ** _] => progress(cancel P) end end.
   try reflexivity.
 - split_pures;dump_pre_spatial;auto;lia.
Qed.

Lemma proof_of_sx_pivot_entail_wit_14_1 : sx_pivot_entail_wit_14_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(j=V_tableau_pivot) by lia. subst j.
 pose proof (PreH24 (16+i*24+E_tableau_pivot) (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot i E_tableau_pivot ltac:(lia) ltac:(lia))) as Hb.
 assert(Hready: simplex_pivot_other_ready N_tableau_pivot D_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot leaving i FN_2 FD_2 CN_2 CD_2).
 { apply other_ready_nonzero__outer_commit;assumption. }
 Exists FN_2 FD_2 CD_2 CN_2.
 split_pure_spatial.
 - sep_apply(memory_focus__outer_commit S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 (16+i*24+E_tableau_pivot) ltac:(lia) ltac:(lia) (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot i E_tableau_pivot ltac:(lia) ltac:(lia))).
   rewrite matrix_cell__outer_commit by lia.
   sep_apply(store_int_undef_store_int (&("j")) V_tableau_pivot).
   csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures;dump_pre_spatial;first[assumption|lia|tauto].
Qed.

Lemma proof_of_sx_pivot_entail_wit_14_2 : sx_pivot_entail_wit_14_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 pose proof(PreH24 (16+i*24+E_tableau_pivot) (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot i E_tableau_pivot ltac:(lia) ltac:(lia))) as Hb.
 assert(Hready:simplex_pivot_other_ready N_tableau_pivot D_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot leaving i FN_2 FD_2 CN_2 CD_2).
 { unfold simplex_pivot_other_ready. rewrite PreH1. exact PreH25. }
 Exists FN_2 FD_2 CD_2 CN_2. split_pure_spatial.
 - pose proof(memory_merge_two__outer_commit S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 i R_tableau_pivot ltac:(lia) ltac:(lia)
   (simplex_pivot_rhs_active M_tableau_pivot V_tableau_pivot i ltac:(lia)) (simplex_pivot_rhs_active M_tableau_pivot V_tableau_pivot R_tableau_pivot ltac:(lia)) ltac:(lia)) as HM.
   rewrite !rhs_native__outer_commit in HM by lia.
   pose proof(memory_focus__outer_commit S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 (16+i*24+E_tableau_pivot) ltac:(lia) ltac:(lia) (simplex_pivot_a_active M_tableau_pivot V_tableau_pivot i E_tableau_pivot ltac:(lia) ltac:(lia))) as HF.
   rewrite matrix_cell__outer_commit in HF by lia.
   revert HM HF;csimpl;intros HM HF. sepcon_right_assoc.
   cancel((&(( &( "pivot" ) )->ₛ "num")) # Int |-> Znth(16+R_tableau_pivot*24+E_tableau_pivot)N_tableau_pivot 0).
   cancel((&(( &( "pivot" ) )->ₛ "den")) # Int |-> Znth(16+R_tableau_pivot*24+E_tableau_pivot)D_tableau_pivot 1).
   cancel((&(( &( "one" ) )->ₛ "num")) # Int |-> 1).
   cancel((&(( &( "one" ) )->ₛ "den")) # Int |-> 1).
   cancel((&(( &( "term" ) )->ₛ "num")) # Int |->_).
   cancel((&(( &( "term" ) )->ₛ "den")) # Int |->_).
   cancel((&(( &( "factor" ) )->ₛ "num")) # Int |-> FN_2).
   cancel((&(( &( "factor" ) )->ₛ "den")) # Int |-> FD_2).
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end.
   sepcon_assoc_change_in HF. sep_apply_r_atomic HF. sep_apply_r_atomic HM.
   csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures;dump_pre_spatial;first[assumption|lia|tauto].
Qed.

Lemma proof_of_sx_pivot_entail_wit_15_1 : sx_pivot_entail_wit_15_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 pose proof(simplex_pivot_a_active M_tableau_pivot V_tableau_pivot i_2 E_tableau_pivot ltac:(lia) ltac:(lia)) as Hact.
 pose proof(simplex_pivot_slots_bounds M_tableau_pivot V_tableau_pivot (16+i_2*24+E_tableau_pivot) ltac:(lia) ltac:(lia) Hact) as Hslot.
 assert(Hprog:simplex_pivot_rows_progress N_tableau_pivot D_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot leaving(i_2+1)(replace_Znth(16+i_2*24+E_tableau_pivot)0 CN_2)(replace_Znth(16+i_2*24+E_tableau_pivot)1 CD_2)).
 { apply(other_complete__outer_commit _ _ _ _ _ _ _ FN FD);assumption. }
 assert(Hgood:forall k,In k(simplex_pivot_slots M_tableau_pivot V_tableau_pivot) ->
 -INT_MAX<=Znth k(replace_Znth(16+i_2*24+E_tableau_pivot)0 CN_2)0<=INT_MAX /\ 1<=Znth k(replace_Znth(16+i_2*24+E_tableau_pivot)1 CD_2)1<=INT_MAX /\ Z.gcd(Z.abs(Znth k(replace_Znth(16+i_2*24+E_tableau_pivot)0 CN_2)0))(Znth k(replace_Znth(16+i_2*24+E_tableau_pivot)1 CD_2)1)=1).
 { apply update_good__outer_commit;try assumption;try lia. intros k Hk. specialize(PreH23 k Hk). tauto. }
 Exists (replace_Znth(16+i_2*24+E_tableau_pivot)1 CD_2)(replace_Znth(16+i_2*24+E_tableau_pivot)0 CN_2).
 split_pure_spatial.
 - pose proof(memory_update__outer_commit S_tableau_pivot M_tableau_pivot V_tableau_pivot CN_2 CD_2 (16+i_2*24+E_tableau_pivot)0 1 ltac:(lia) ltac:(lia) PreH21 PreH22 Hact) as HM.
   rewrite matrix_cell__outer_commit in HM by lia. sepcon_right_assoc. sep_apply_r_atomic HM.
   sep_apply(store_int_undef_store_int (&(( &( "factor" ) )->ₛ "num")) FN).
   sep_apply(store_int_undef_store_int (&(( &( "factor" ) )->ₛ "den")) FD).
   csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures;dump_pre_spatial;first[assumption|rewrite Zlength_replace_Znth;assumption|lia|intros k Hk;specialize(Hgood k Hk);tauto].
Qed.

Lemma proof_of_sx_pivot_entail_wit_15_2_split_goal_1 : sx_pivot_entail_wit_15_2_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst i_2. apply skip_row__outer_commit;assumption.
Qed.

Lemma proof_of_sx_pivot_entail_wit_15_2 : sx_pivot_entail_wit_15_2.
Proof. aggressive_pre_process. Goal_apply proof_of_sx_pivot_entail_wit_15_2_split_goal_1. Qed.

Lemma proof_of_sx_pivot_entail_wit_16 : sx_pivot_entail_wit_16.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(i_3=M_tableau_pivot) by lia. subst i_3.
 prop_apply_p (IntArray.full_Zlength (&((S_tableau_pivot) # "SxState" ->ₛ "is_basic")) V_tableau_pivot IB_tableau_pivot).
 Intros_p Hlen.
 pose proof(PreH13 R_tableau_pivot ltac:(lia)) as HB. destruct HB as [_ HB]. rewrite <-PreH18 in HB.
 Exists CD_2 CN_2. split_pure_spatial.
 - sep_apply(IntArray.full_split_to_missing_i (&((S_tableau_pivot) # "SxState" ->ₛ "basic")) R_tableau_pivot M_tableau_pivot B_tableau_pivot 0 ltac:(lia)).
   sep_apply(flags_focus__outer_commit S_tableau_pivot V_tableau_pivot IB_tableau_pivot leaving E_tableau_pivot ltac:(lia) ltac:(lia) ltac:(lia)).
   unfold StoreIntAsElement.storeA. rewrite <-PreH18,HB,PreH15.
   csimpl. sepcon_right_assoc.
   repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures;dump_pre_spatial;assumption.
Qed.

Lemma proof_of_sx_pivot_return_wit_1 : sx_pivot_return_wit_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst leaving.
 prop_apply_p(IntArray.full_Zlength (&((S_tableau_pivot) # "SxState" ->ₛ "basic")) M_tableau_pivot (replace_Znth R_tableau_pivot E_tableau_pivot B_tableau_pivot)).
 Intros_p HBlen. rewrite Zlength_replace_Znth in HBlen.
 assert(HC:simplex_pivot_compute N_tableau_pivot D_tableau_pivot M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0)=(1,(CN,CD))) by exact PreH25.
 assert(HDpos:forall i,0<=i<M_tableau_pivot ->0<Znth i D_tableau_pivot 1 /\forall j,0<=j<V_tableau_pivot ->0<Znth(16+i*24+j)D_tableau_pivot 1).
 { intros i Hi. split.
   - pose proof(PreH17 i (simplex_pivot_rhs_active _ _ i Hi));lia.
   - intros j Hj. pose proof(PreH17 _ (simplex_pivot_a_active _ _ i j Hi Hj));lia. }
 assert(HCL:simplex_pivot_closed N_tableau_pivot D_tableau_pivot CN CD M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0)).
 { apply pivot_compute_closed__success_math;try assumption;lia. }
 assert(HZ:simplex_pivot_value N_tableau_pivot D_tableau_pivot(16+R_tableau_pivot*24+Znth R_tableau_pivot B_tableau_pivot 0)=Qcanon.Q2Qc (QArith_base.inject_Z 0)).
 { unfold simplex_pivot_value. rewrite (PreH16 R_tableau_pivot R_tableau_pivot ltac:(lia)). apply pivot_fraction_zero__success_math. exact(proj2(HDpos R_tableau_pivot ltac:(lia)) (Znth R_tableau_pivot B_tableau_pivot 0) ltac:(lia)). }
 assert(HEQ:simplex_pivot_equiv N_tableau_pivot D_tableau_pivot CN CD B_tableau_pivot M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot).
 { apply pivot_closed_equiv__success_math;try assumption;lia. }
 Exists CN CD. split_pure_spatial.
 - unfold simplex_pivot_basis. rewrite Z.eqb_refl.
   csimpl. sepcon_right_assoc. sep_apply_r_atomic(pivot_marks_merge__success_math S_tableau_pivot V_tableau_pivot IB_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0) E_tableau_pivot PreH11 ltac:(lia) ltac:(lia) ltac:(lia)).
   csimpl. sepcon_right_assoc. repeat multimatch goal with |- ?L |-- _ => multimatch L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures;dump_pre_spatial.
   + reflexivity.
   + exact HC.
   + intro. split;assumption.
   + exact PreH24.
Qed.

Lemma proof_of_sx_pivot_return_wit_2 : sx_pivot_return_wit_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst leaving.
 assert(Hres:simplex_pivot_result N_tableau_pivot D_tableau_pivot M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0) 0 CN CD).
 { eapply (other_failure_suffix__failure_matrix N_tableau_pivot D_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0) M_tableau_pivot i_2 j FN FD CN CD); [lia|lia|lia|lia|eassumption|eassumption|].
   unfold simplex_pivot_other_column.
   assert(Ej:Z.eqb j E_tableau_pivot=false) by (apply Z.eqb_neq;lia). rewrite Ej.
   eapply addmul_add_reject__failure_matrix;[lia|eassumption|lia].
 }
 Exists CN CD.
 unfold simplex_pivot_basis,simplex_pivot_marks. cbn [Z.eqb].
 split_pure_spatial.
 - sep_apply_r_atomic (memory_merge__failure_matrix S_tableau_pivot M_tableau_pivot V_tableau_pivot CN CD R_tableau_pivot i_2 j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   rewrite !matrix_cell__failure_matrix by lia.
   repeat const_array_simpl. csimpl. sepcon_right_assoc.
   repeat multimatch goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end.
   reflexivity.
 - split_pures;dump_pre_spatial; auto;try lia.
Qed.

Lemma proof_of_sx_pivot_return_wit_3 : sx_pivot_return_wit_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst leaving.
 assert(Hres:simplex_pivot_result N_tableau_pivot D_tableau_pivot M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0) 0 CN CD).
 { eapply (other_failure_suffix__failure_matrix N_tableau_pivot D_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0) M_tableau_pivot i_2 j FN FD CN CD); [lia|lia|lia|lia|eassumption|eassumption|].
   unfold simplex_pivot_other_column.
   assert(Ej:Z.eqb j E_tableau_pivot=false) by (apply Z.eqb_neq;lia). rewrite Ej.
   eapply addmul_add_reject__failure_matrix;[lia|eassumption|lia].
 }
 Exists CN CD.
 unfold simplex_pivot_basis,simplex_pivot_marks. cbn [Z.eqb].
 split_pure_spatial.
 - sep_apply_r_atomic (memory_merge__failure_matrix S_tableau_pivot M_tableau_pivot V_tableau_pivot CN CD R_tableau_pivot i_2 j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   rewrite !matrix_cell__failure_matrix by lia.
   repeat const_array_simpl. csimpl. sepcon_right_assoc.
   repeat multimatch goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end.
   reflexivity.
 - split_pures;dump_pre_spatial; auto;try lia.
Qed.

Lemma proof_of_sx_pivot_return_wit_4 : sx_pivot_return_wit_4.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst leaving.
 assert(Hres:simplex_pivot_result N_tableau_pivot D_tableau_pivot M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0) 0 CN CD).
 { eapply (other_failure_suffix__failure_matrix N_tableau_pivot D_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0) M_tableau_pivot i_2 j FN FD CN CD); [lia|lia|lia|lia|eassumption|eassumption|].
   unfold simplex_pivot_other_column.
   assert(Ej:Z.eqb j E_tableau_pivot=false) by (apply Z.eqb_neq;lia). rewrite Ej.
   eapply addmul_mul_reject__failure_matrix;lia.
 }
 Exists CN CD.
 unfold simplex_pivot_basis,simplex_pivot_marks. cbn [Z.eqb].
 split_pure_spatial.
 - sep_apply_r_atomic (memory_merge__failure_matrix S_tableau_pivot M_tableau_pivot V_tableau_pivot CN CD R_tableau_pivot i_2 j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   rewrite !matrix_cell__failure_matrix by lia.
   repeat const_array_simpl. csimpl. sepcon_right_assoc.
   repeat multimatch goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end.
   reflexivity.
 - split_pures;dump_pre_spatial; auto;try lia.
Qed.

Lemma proof_of_sx_pivot_return_wit_5 : sx_pivot_return_wit_5.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(HFC: FN=Znth(16+i_2*24+E_tableau_pivot)CN 0 /\ FD=Znth(16+i_2*24+E_tableau_pivot)CD 1).
 { eapply factor_current__failure_rhs; eauto. }
 destruct HFC as [HF HD].
 assert(HA:simplex_pivot_addmul FN FD R_tableau_pivot i_2 (1,(CN,CD))=(0,(CN,CD))).
 { eapply addmul_reject_add__failure_rhs; eauto;lia. }
 assert(HRES:simplex_pivot_result N_tableau_pivot D_tableau_pivot M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0) 0 CN CD).
 { replace(Znth R_tableau_pivot B_tableau_pivot 0) with leaving by congruence. eapply(rhs_failure_suffix__failure_rhs N_tableau_pivot D_tableau_pivot M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot leaving i_2 CN CD FN FD);eauto;lia. }
 Exists CN CD.
 unfold simplex_pivot_basis,simplex_pivot_marks. cbn [Z.eqb].
 split_pure_spatial.
 - pose proof(rhs_memory_merge__failure_rhs S_tableau_pivot M_tableau_pivot V_tableau_pivot CN CD i_2 R_tableau_pivot ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HM.
   rewrite !rhs_cell__failure_rhs in HM by lia.
   unfold simplex_scan_rat_memory in HM.
   sep_apply_r_atomic HM.
   csimpl. repeat const_array_simpl. sepcon_right_assoc.
   repeat multimatch goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures;dump_pre_spatial;auto;try congruence.
Qed.

Lemma proof_of_sx_pivot_return_wit_6 : sx_pivot_return_wit_6.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(HFC: FN=Znth(16+i_2*24+E_tableau_pivot)CN 0 /\ FD=Znth(16+i_2*24+E_tableau_pivot)CD 1).
 { eapply factor_current__failure_rhs; eauto. }
 destruct HFC as [HF HD].
 assert(HA:simplex_pivot_addmul FN FD R_tableau_pivot i_2 (1,(CN,CD))=(0,(CN,CD))).
 { eapply addmul_reject_add__failure_rhs; eauto;lia. }
 assert(HRES:simplex_pivot_result N_tableau_pivot D_tableau_pivot M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0) 0 CN CD).
 { replace(Znth R_tableau_pivot B_tableau_pivot 0) with leaving by congruence. eapply(rhs_failure_suffix__failure_rhs N_tableau_pivot D_tableau_pivot M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot leaving i_2 CN CD FN FD);eauto;lia. }
 Exists CN CD.
 unfold simplex_pivot_basis,simplex_pivot_marks. cbn [Z.eqb].
 split_pure_spatial.
 - pose proof(rhs_memory_merge__failure_rhs S_tableau_pivot M_tableau_pivot V_tableau_pivot CN CD i_2 R_tableau_pivot ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HM.
   rewrite !rhs_cell__failure_rhs in HM by lia.
   unfold simplex_scan_rat_memory in HM.
   sep_apply_r_atomic HM.
   csimpl. repeat const_array_simpl. sepcon_right_assoc.
   repeat multimatch goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures;dump_pre_spatial;auto;try congruence.
Qed.

Lemma proof_of_sx_pivot_return_wit_7 : sx_pivot_return_wit_7.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(HFC: FN=Znth(16+i_2*24+E_tableau_pivot)CN 0 /\ FD=Znth(16+i_2*24+E_tableau_pivot)CD 1).
 { eapply factor_current__failure_rhs; eauto. }
 destruct HFC as [HF HD].
 assert(HA:simplex_pivot_addmul FN FD R_tableau_pivot i_2 (1,(CN,CD))=(0,(CN,CD))).
 { eapply addmul_reject_mul__failure_rhs; eauto;lia. }
 assert(HRES:simplex_pivot_result N_tableau_pivot D_tableau_pivot M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0) 0 CN CD).
 { replace(Znth R_tableau_pivot B_tableau_pivot 0) with leaving by congruence. eapply(rhs_failure_suffix__failure_rhs N_tableau_pivot D_tableau_pivot M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot leaving i_2 CN CD FN FD);eauto;lia. }
 Exists CN CD.
 unfold simplex_pivot_basis,simplex_pivot_marks. cbn [Z.eqb].
 split_pure_spatial.
 - pose proof(rhs_memory_merge__failure_rhs S_tableau_pivot M_tableau_pivot V_tableau_pivot CN CD i_2 R_tableau_pivot ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HM.
   rewrite !rhs_cell__failure_rhs in HM by lia.
   unfold simplex_scan_rat_memory in HM.
   sep_apply_r_atomic HM.
   csimpl. repeat const_array_simpl. sepcon_right_assoc.
   repeat multimatch goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures;dump_pre_spatial;auto;try congruence.
Qed.

Lemma proof_of_sx_pivot_return_wit_8 : sx_pivot_return_wit_8.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(HR:simplex_pivot_result N_tableau_pivot D_tableau_pivot M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0) 0 CN CD).
 { subst leaving. apply fail_recip__failure_pivot; [exact PreH27|lia]. }
 pose proof(memory_merge__failure_pivot S_tableau_pivot M_tableau_pivot V_tableau_pivot CN CD (16+R_tableau_pivot*24+leaving) ltac:(lia) ltac:(lia) ltac:(apply simplex_pivot_a_active;lia)) as HM.
 rewrite matrix_native__failure_pivot in HM by lia.
 Exists CN CD.
 unfold simplex_pivot_basis, simplex_pivot_marks. simpl (Z.eqb 0 1).
 split_pure_spatial.
 - revert HM. csimpl. intro HM. sepcon_right_assoc.
   sep_apply_r_atomic HM.
   repeat match goal with |- ?L |-- _ => multimatch L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures;dump_pre_spatial;auto;try lia.
Qed.

Lemma proof_of_sx_pivot_return_wit_9 : sx_pivot_return_wit_9.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert(HR:simplex_pivot_result N_tableau_pivot D_tableau_pivot M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0) 0 CN CD).
 { subst leaving. eapply fail_column__failure_pivot with(j:=j); [lia|exact PreH4|exact PreH28|lia]. }
 pose proof(memory_merge__failure_pivot S_tableau_pivot M_tableau_pivot V_tableau_pivot CN CD (16+R_tableau_pivot*24+j) ltac:(lia) ltac:(lia) ltac:(apply simplex_pivot_a_active;lia)) as HM.
 rewrite matrix_native__failure_pivot in HM by lia.
 Exists CN CD.
 unfold simplex_pivot_basis, simplex_pivot_marks. simpl (Z.eqb 0 1).
 split_pure_spatial.
 - revert HM. csimpl. intro HM. sepcon_right_assoc.
   sep_apply_r_atomic HM.
   repeat match goal with |- ?L |-- _ => multimatch L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures;dump_pre_spatial;auto;try lia.
Qed.

Lemma proof_of_sx_pivot_return_wit_10 : sx_pivot_return_wit_10.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst CN CD.
 assert(HR:simplex_pivot_result N_tableau_pivot D_tableau_pivot M_tableau_pivot V_tableau_pivot R_tableau_pivot E_tableau_pivot (Znth R_tableau_pivot B_tableau_pivot 0) 0 N_tableau_pivot D_tableau_pivot).
 { apply fail_rhs__failure_pivot;lia. }
 pose proof(memory_merge__failure_pivot S_tableau_pivot M_tableau_pivot V_tableau_pivot N_tableau_pivot D_tableau_pivot R_tableau_pivot ltac:(lia) ltac:(lia) ltac:(apply simplex_pivot_rhs_active;lia)) as HM.
 rewrite rhs_native__failure_pivot in HM by lia.
 Exists N_tableau_pivot D_tableau_pivot.
 unfold simplex_pivot_basis, simplex_pivot_marks. simpl (Z.eqb 0 1).
 split_pure_spatial.
 - revert HM. csimpl. intro HM. sepcon_right_assoc.
   sep_apply_r_atomic HM.
   repeat match goal with |- ?L |-- _ => multimatch L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - split_pures;dump_pre_spatial;auto;try lia.
Qed.

