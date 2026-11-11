From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_find_violation_preserve Require Import simplex_find_violation_preserve_goal.
From SimpleC.EE.Applications_human.simplex_find_violation_preserve Require Import simplex_find_violation_preserve_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_rat_compare.simplex_rat_compare_lib.
Require Import SimpleC.EE.Applications_human.simplex_find_violation_preserve.simplex_find_violation_preserve_lib.
Local Open Scope sac.

Lemma proof_of_sx_find_violation_entail_wit_1_split_goal_1 : sx_find_violation_entail_wit_1_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
dump_pre_spatial. apply prefix_initial__init_finish.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_1_split_goal_2 : sx_find_violation_entail_wit_1_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_1_split_goal_3 : sx_find_violation_entail_wit_1_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_1_split_goal_4 : sx_find_violation_entail_wit_1_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_1_split_goal_5 : sx_find_violation_entail_wit_1_split_goal_5.
Proof.
LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_1_split_goal_spatial : sx_find_violation_entail_wit_1_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
rewrite PreH5. reflexivity.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_1 : sx_find_violation_entail_wit_1.
Proof.
aggressive_pre_process.
- Goal_apply proof_of_sx_find_violation_entail_wit_1_split_goal_spatial.
- Goal_apply proof_of_sx_find_violation_entail_wit_1_split_goal_1.
- Goal_apply proof_of_sx_find_violation_entail_wit_1_split_goal_2.
- Goal_apply proof_of_sx_find_violation_entail_wit_1_split_goal_3.
- Goal_apply proof_of_sx_find_violation_entail_wit_1_split_goal_4.
- Goal_apply proof_of_sx_find_violation_entail_wit_1_split_goal_5.

Qed.

Lemma proof_of_sx_find_violation_entail_wit_2 : sx_find_violation_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.full_Zlength &(S_framed_search # "SxState" ->ₛ "basic") M_framed_search BAS_framed_search).
  Intros_p Hlen.
  pose proof (nth_member__read_focus BAS_framed_search i ltac:(lia)) as Hin.
  pose proof (PreH10 i ltac:(lia)) as Hb.
  assert (HA : existsb (Z.eqb (Znth i BAS_framed_search 0)) BAS_framed_search = true).
  { apply existsb_exists. exists (Znth i BAS_framed_search 0). split; [exact Hin|apply Z.eqb_refl]. }
  sep_apply (read_slot_focus__read_focus S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search (Znth i BAS_framed_search 0) ltac:(lia)).
  unfold simplex_scan_read_slot. rewrite HA. simpl.
  destruct (Z.eqb_spec (Znth (Znth i BAS_framed_search 0) HL_framed_search 0) 0) as [HL|HL];
  destruct (Z.eqb_spec (Znth (Znth i BAS_framed_search 0) HU_framed_search 0) 0) as [HU|HU]; simpl;
    [Right | Left; Left; Left; Left | Left; Right | Left; Left; Left; Right].
  all: Exists R_2 D_2.
  all: split_pure_spatial.
  all: try (split_pures; dump_pre_spatial; first [assumption | reflexivity | lia]).
  all: unfold simplex_scan_rat_memory; csimpl; sepcon_right_assoc;
    repeat match goal with |- _ |-- ?p ** _ => cancel p end; cancel.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_1_split_goal_1 : sx_find_violation_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst b.
  eapply (row_prefix_step__upper_update BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search V_framed_search i best R_2 D_2); try eassumption; try lia.
  unfold simplex_scan_rows.
  apply simplex_scan_row_upper_override; try assumption; try congruence.
  left; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_1_split_goal_2 : sx_find_violation_entail_wit_7_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_1_split_goal_3 : sx_find_violation_entail_wit_7_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_1_split_goal_4 : sx_find_violation_entail_wit_7_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_1_split_goal_5 : sx_find_violation_entail_wit_7_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_1_split_goal_spatial : sx_find_violation_entail_wit_7_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
  assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = true) by (apply Z.eqb_eq; assumption).
  rewrite HA, HU, HL. simpl.
  unfold simplex_scan_rat_memory.
  rewrite !simplex_scan_rat_member_address.
  normalize.
  sepcon_assoc_change.
  cancel.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_1 : sx_find_violation_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_1_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_1_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_1_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_1_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_1_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_1_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_2_split_goal_1 : sx_find_violation_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst b.
  eapply (row_prefix_step__upper_update BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search V_framed_search i best R_2 D_2); try eassumption; try lia.
  unfold simplex_scan_rows.
  apply simplex_scan_row_upper_override; try assumption; try congruence.
  right; congruence.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_2_split_goal_2 : sx_find_violation_entail_wit_7_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_2_split_goal_3 : sx_find_violation_entail_wit_7_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_2_split_goal_4 : sx_find_violation_entail_wit_7_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_2_split_goal_5 : sx_find_violation_entail_wit_7_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_2_split_goal_spatial : sx_find_violation_entail_wit_7_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
  assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite HA, HU, HL. simpl.
  unfold simplex_scan_rat_memory.
  rewrite !simplex_scan_rat_member_address.
  normalize.
  sepcon_assoc_change.
  cancel.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_2 : sx_find_violation_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_2_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_2_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_2_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_2_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_2_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_2_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_3_split_goal_1 : sx_find_violation_entail_wit_7_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst b.
  eapply (row_prefix_step__upper_update BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search V_framed_search i best R_2 D_2); try eassumption; try lia.
  unfold simplex_scan_rows.
  apply simplex_scan_row_upper_override; try assumption; try congruence.
  right; congruence.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_3_split_goal_2 : sx_find_violation_entail_wit_7_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_3_split_goal_3 : sx_find_violation_entail_wit_7_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_3_split_goal_4 : sx_find_violation_entail_wit_7_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_3_split_goal_5 : sx_find_violation_entail_wit_7_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_3_split_goal_spatial : sx_find_violation_entail_wit_7_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
  assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite HA, HU, HL. simpl.
  unfold simplex_scan_rat_memory.
  rewrite !simplex_scan_rat_member_address.
  normalize.
  sepcon_assoc_change.
  cancel.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_3 : sx_find_violation_entail_wit_7_3.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_3_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_3_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_3_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_3_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_3_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_3_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_4_split_goal_1 : sx_find_violation_entail_wit_7_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst b.
  eapply (row_prefix_step__upper_update BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search V_framed_search i best R_2 D_2); try eassumption; try lia.
  unfold simplex_scan_rows.
  apply simplex_scan_row_upper_override; try assumption; try congruence.
  right; congruence.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_4_split_goal_2 : sx_find_violation_entail_wit_7_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_4_split_goal_3 : sx_find_violation_entail_wit_7_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_4_split_goal_4 : sx_find_violation_entail_wit_7_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_4_split_goal_5 : sx_find_violation_entail_wit_7_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_4_split_goal_spatial : sx_find_violation_entail_wit_7_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
  assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite HA, HU, HL. simpl.
  unfold simplex_scan_rat_memory.
  rewrite !simplex_scan_rat_member_address.
  normalize.
  sepcon_assoc_change.
  cancel.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_4 : sx_find_violation_entail_wit_7_4.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_4_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_4_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_4_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_4_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_4_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_4_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_5_split_goal_1 : sx_find_violation_entail_wit_7_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst b.
  eapply (row_prefix_step__upper_update BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search V_framed_search i best R_2 D_2); try eassumption; try lia.
  unfold simplex_scan_rows.
  apply simplex_scan_row_upper_override; try assumption; try congruence.
  right; congruence.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_5_split_goal_2 : sx_find_violation_entail_wit_7_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_5_split_goal_3 : sx_find_violation_entail_wit_7_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_5_split_goal_4 : sx_find_violation_entail_wit_7_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_5_split_goal_5 : sx_find_violation_entail_wit_7_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_5_split_goal_spatial : sx_find_violation_entail_wit_7_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
  assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite HA, HU, HL. simpl.
  unfold simplex_scan_rat_memory.
  rewrite !simplex_scan_rat_member_address.
  normalize.
  sepcon_assoc_change.
  cancel.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_5 : sx_find_violation_entail_wit_7_5.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_5_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_5_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_5_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_5_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_5_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  - Goal_apply (proof_of_sx_find_violation_entail_wit_7_5_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_6_split_goal_1 : sx_find_violation_entail_wit_7_6_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 replace b with (Znth i BAS_framed_search 0) by congruence.
 eapply row_prefix_step__lower_update; try eassumption; try lia.
 unfold simplex_scan_rows.
 apply row_lower__lower_update; try congruence; try lia.
 right. split; congruence.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_6_split_goal_2 : sx_find_violation_entail_wit_7_6_split_goal_2.
Proof. LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; assumption). Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_6_split_goal_3 : sx_find_violation_entail_wit_7_6_split_goal_3.
Proof. LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; assumption). Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_6_split_goal_4 : sx_find_violation_entail_wit_7_6_split_goal_4.
Proof. LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; assumption). Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_6_split_goal_5 : sx_find_violation_entail_wit_7_6_split_goal_5.
Proof. LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; assumption). Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_6_split_goal_spatial : sx_find_violation_entail_wit_7_6_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__lower_update S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
 unfold simplex_scan_read_slot.
 assert (EA : existsb (Z.eqb b) BAS_framed_search = true).
 { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
 assert (EL : Z.eqb (Znth b HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite EA, EL. simpl.
 assert (EU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite EU. simpl.
 unfold simplex_scan_rat_memory.
 rewrite !simplex_scan_rat_member_address.
 repeat rewrite <- sepcon_assoc.
 cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + b * sizeof(INT)) # Int |-> Znth b HL_framed_search 0).
 cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + b * sizeof(INT)) # Int |-> Znth b HU_framed_search 0).
 cancel.


Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_6 : sx_find_violation_entail_wit_7_6.
Proof.
 aggressive_pre_process.
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_6_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_6_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_6_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_6_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_6_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_6_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_7_split_goal_1 : sx_find_violation_entail_wit_7_7_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 replace b with (Znth i BAS_framed_search 0) by congruence.
 eapply row_prefix_step__lower_update; try eassumption; try lia.
 unfold simplex_scan_rows.
 apply row_lower__lower_update; try congruence; try lia.
 right. split; congruence.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_7_split_goal_2 : sx_find_violation_entail_wit_7_7_split_goal_2.
Proof. LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; assumption). Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_7_split_goal_3 : sx_find_violation_entail_wit_7_7_split_goal_3.
Proof. LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; assumption). Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_7_split_goal_4 : sx_find_violation_entail_wit_7_7_split_goal_4.
Proof. LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; assumption). Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_7_split_goal_5 : sx_find_violation_entail_wit_7_7_split_goal_5.
Proof. LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; assumption). Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_7_split_goal_spatial : sx_find_violation_entail_wit_7_7_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__lower_update S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
 unfold simplex_scan_read_slot.
 assert (EA : existsb (Z.eqb b) BAS_framed_search = true).
 { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
 assert (EL : Z.eqb (Znth b HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite EA, EL. simpl.
 assert (EU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite EU. simpl.
 unfold simplex_scan_rat_memory.
 rewrite !simplex_scan_rat_member_address.
 repeat rewrite <- sepcon_assoc.
 cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + b * sizeof(INT)) # Int |-> Znth b HL_framed_search 0).
 cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + b * sizeof(INT)) # Int |-> Znth b HU_framed_search 0).
 cancel.


Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_7 : sx_find_violation_entail_wit_7_7.
Proof.
 aggressive_pre_process.
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_7_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_7_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_7_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_7_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_7_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_7_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_8_split_goal_1 : sx_find_violation_entail_wit_7_8_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 replace b with (Znth i BAS_framed_search 0) by congruence.
 eapply row_prefix_step__lower_update; try eassumption; try lia.
 unfold simplex_scan_rows.
 apply row_lower__lower_update; try congruence; try lia.
 left. congruence.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_8_split_goal_2 : sx_find_violation_entail_wit_7_8_split_goal_2.
Proof. LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; assumption). Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_8_split_goal_3 : sx_find_violation_entail_wit_7_8_split_goal_3.
Proof. LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; assumption). Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_8_split_goal_4 : sx_find_violation_entail_wit_7_8_split_goal_4.
Proof. LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; assumption). Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_8_split_goal_5 : sx_find_violation_entail_wit_7_8_split_goal_5.
Proof. LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; assumption). Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_8_split_goal_spatial : sx_find_violation_entail_wit_7_8_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__lower_update S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
 unfold simplex_scan_read_slot.
 assert (EA : existsb (Z.eqb b) BAS_framed_search = true).
 { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
 assert (EL : Z.eqb (Znth b HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite EA, EL. simpl.
 assert (EU : Znth b HU_framed_search 0 = 0) by assumption.
 rewrite EU. simpl.
 unfold simplex_scan_rat_memory.
 rewrite !simplex_scan_rat_member_address.
 repeat rewrite <- sepcon_assoc.
 cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + b * sizeof(INT)) # Int |-> Znth b HL_framed_search 0).
 cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + b * sizeof(INT)) # Int |-> 0).
 cancel.
 reflexivity.


Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_8 : sx_find_violation_entail_wit_7_8.
Proof.
 aggressive_pre_process.
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_8_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_8_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_8_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_8_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_8_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39).
 - Goal_apply (proof_of_sx_find_violation_entail_wit_7_8_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_9_split_goal_1 : sx_find_violation_entail_wit_7_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply row_prefix_step__no_violation; eauto; try lia.
  unfold simplex_scan_rows.
  match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
  unfold simplex_scan_row.
  repeat match goal with
  | |- context [Z.eqb ?x ?y] =>
      let E := fresh "E" in destruct (Z.eqb x y) eqn:E;
      [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
      cbn [orb andb negb]; try congruence; try lia
  | |- context [Z.ltb ?x ?y] =>
      let E := fresh "E" in destruct (Z.ltb x y) eqn:E;
      [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
      cbn [orb andb negb]; try congruence; try lia
  end; reflexivity.

Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_9_split_goal_2 : sx_find_violation_entail_wit_7_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_9_split_goal_3 : sx_find_violation_entail_wit_7_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_9_split_goal_4 : sx_find_violation_entail_wit_7_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_9_split_goal_5 : sx_find_violation_entail_wit_7_9_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_9_split_goal_spatial : sx_find_violation_entail_wit_7_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__no_violation S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption | apply Z.eqb_refl]. }
  rewrite HA. cbn [andb].
  repeat match goal with
  | |- context [Z.eqb ?x 0] =>
      let E := fresh "E" in destruct (Z.eqb x 0) eqn:E;
      [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
      cbn [orb andb negb]; try contradiction; try lia
  end;
  rewrite ?simplex_scan_rat_memory_enabled;
  normalize_ptr_size; elim_emp; sepcon_right_assoc; cancel.
  all: cancel.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_9 : sx_find_violation_entail_wit_7_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_9_split_goal_spatial.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_9_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_9_split_goal_2.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_9_split_goal_3.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_9_split_goal_4.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_9_split_goal_5.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_10_split_goal_1 : sx_find_violation_entail_wit_7_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply row_prefix_step__no_violation; eauto; try lia.
  unfold simplex_scan_rows.
  match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
  unfold simplex_scan_row.
  repeat match goal with
  | |- context [Z.eqb ?x ?y] =>
      let E := fresh "E" in destruct (Z.eqb x y) eqn:E;
      [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
      cbn [orb andb negb]; try congruence; try lia
  | |- context [Z.ltb ?x ?y] =>
      let E := fresh "E" in destruct (Z.ltb x y) eqn:E;
      [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
      cbn [orb andb negb]; try congruence; try lia
  end; reflexivity.

Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_10_split_goal_2 : sx_find_violation_entail_wit_7_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_10_split_goal_3 : sx_find_violation_entail_wit_7_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_10_split_goal_4 : sx_find_violation_entail_wit_7_10_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_10_split_goal_5 : sx_find_violation_entail_wit_7_10_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_10_split_goal_spatial : sx_find_violation_entail_wit_7_10_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__no_violation S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption | apply Z.eqb_refl]. }
  rewrite HA. cbn [andb].
  repeat match goal with
  | |- context [Z.eqb ?x 0] =>
      let E := fresh "E" in destruct (Z.eqb x 0) eqn:E;
      [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
      cbn [orb andb negb]; try contradiction; try lia
  end;
  rewrite ?simplex_scan_rat_memory_enabled;
  normalize_ptr_size; elim_emp; sepcon_right_assoc; cancel.
  all: cancel.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_10 : sx_find_violation_entail_wit_7_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_10_split_goal_spatial.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_10_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_10_split_goal_2.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_10_split_goal_3.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_10_split_goal_4.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_10_split_goal_5.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_11_split_goal_1 : sx_find_violation_entail_wit_7_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply row_prefix_step__no_violation; eauto; try lia.
  unfold simplex_scan_rows.
  match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
  unfold simplex_scan_row.
  repeat match goal with
  | |- context [Z.eqb ?x ?y] =>
      let E := fresh "E" in destruct (Z.eqb x y) eqn:E;
      [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
      cbn [orb andb negb]; try congruence; try lia
  | |- context [Z.ltb ?x ?y] =>
      let E := fresh "E" in destruct (Z.ltb x y) eqn:E;
      [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
      cbn [orb andb negb]; try congruence; try lia
  end; reflexivity.

Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_11_split_goal_2 : sx_find_violation_entail_wit_7_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_11_split_goal_3 : sx_find_violation_entail_wit_7_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_11_split_goal_4 : sx_find_violation_entail_wit_7_11_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_11_split_goal_5 : sx_find_violation_entail_wit_7_11_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_11_split_goal_spatial : sx_find_violation_entail_wit_7_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__no_violation S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption | apply Z.eqb_refl]. }
  rewrite HA. cbn [andb].
  repeat match goal with
  | |- context [Z.eqb ?x 0] =>
      let E := fresh "E" in destruct (Z.eqb x 0) eqn:E;
      [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
      cbn [orb andb negb]; try contradiction; try lia
  end;
  rewrite ?simplex_scan_rat_memory_enabled;
  normalize_ptr_size; elim_emp; sepcon_right_assoc; cancel.
  all: cancel.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_11 : sx_find_violation_entail_wit_7_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_11_split_goal_spatial.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_11_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_11_split_goal_2.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_11_split_goal_3.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_11_split_goal_4.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_11_split_goal_5.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_12_split_goal_1 : sx_find_violation_entail_wit_7_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply row_prefix_step__no_violation; eauto; try lia.
  unfold simplex_scan_rows.
  match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
  unfold simplex_scan_row.
  repeat match goal with
  | |- context [Z.eqb ?x ?y] =>
      let E := fresh "E" in destruct (Z.eqb x y) eqn:E;
      [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
      cbn [orb andb negb]; try congruence; try lia
  | |- context [Z.ltb ?x ?y] =>
      let E := fresh "E" in destruct (Z.ltb x y) eqn:E;
      [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
      cbn [orb andb negb]; try congruence; try lia
  end; reflexivity.

Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_12_split_goal_2 : sx_find_violation_entail_wit_7_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_12_split_goal_3 : sx_find_violation_entail_wit_7_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_12_split_goal_4 : sx_find_violation_entail_wit_7_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_12_split_goal_5 : sx_find_violation_entail_wit_7_12_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_12_split_goal_spatial : sx_find_violation_entail_wit_7_12_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__no_violation S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption | apply Z.eqb_refl]. }
  rewrite HA. cbn [andb].
  repeat match goal with
  | |- context [Z.eqb ?x 0] =>
      let E := fresh "E" in destruct (Z.eqb x 0) eqn:E;
      [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
      cbn [orb andb negb]; try contradiction; try lia
  end;
  rewrite ?simplex_scan_rat_memory_enabled;
  normalize_ptr_size; elim_emp; sepcon_right_assoc; cancel.
  all: cancel.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_12 : sx_find_violation_entail_wit_7_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_12_split_goal_spatial.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_12_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_12_split_goal_2.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_12_split_goal_3.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_12_split_goal_4.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_12_split_goal_5.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_13_split_goal_1 : sx_find_violation_entail_wit_7_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply row_prefix_step__no_violation; eauto; try lia.
  unfold simplex_scan_rows.
  match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
  unfold simplex_scan_row.
  repeat match goal with
  | |- context [Z.eqb ?x ?y] =>
      let E := fresh "E" in destruct (Z.eqb x y) eqn:E;
      [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
      cbn [orb andb negb]; try congruence; try lia
  | |- context [Z.ltb ?x ?y] =>
      let E := fresh "E" in destruct (Z.ltb x y) eqn:E;
      [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
      cbn [orb andb negb]; try congruence; try lia
  end; reflexivity.

Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_13_split_goal_2 : sx_find_violation_entail_wit_7_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_13_split_goal_3 : sx_find_violation_entail_wit_7_13_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_13_split_goal_4 : sx_find_violation_entail_wit_7_13_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_13_split_goal_5 : sx_find_violation_entail_wit_7_13_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_13_split_goal_spatial : sx_find_violation_entail_wit_7_13_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__no_violation S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption | apply Z.eqb_refl]. }
  rewrite HA. cbn [andb].
  repeat match goal with
  | |- context [Z.eqb ?x 0] =>
      let E := fresh "E" in destruct (Z.eqb x 0) eqn:E;
      [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
      cbn [orb andb negb]; try contradiction; try lia
  end;
  rewrite ?simplex_scan_rat_memory_enabled;
  normalize_ptr_size; elim_emp; sepcon_right_assoc; cancel.
  all: cancel.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_13 : sx_find_violation_entail_wit_7_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_13_split_goal_spatial.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_13_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_13_split_goal_2.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_13_split_goal_3.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_13_split_goal_4.
  - Goal_apply proof_of_sx_find_violation_entail_wit_7_13_split_goal_5.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_14_split_goal_1 : sx_find_violation_entail_wit_7_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply row_prefix_step__keep_best_upper; try eassumption; try lia.
  unfold simplex_scan_rows.
  match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
  apply simplex_scan_row_upper_override; try lia; auto.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_14_split_goal_2 : sx_find_violation_entail_wit_7_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_14_split_goal_3 : sx_find_violation_entail_wit_7_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_14_split_goal_4 : sx_find_violation_entail_wit_7_14_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_14_split_goal_5 : sx_find_violation_entail_wit_7_14_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_14_split_goal_spatial : sx_find_violation_entail_wit_7_14_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__keep_best_upper S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
  rewrite HA. simpl.
  assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite HU. simpl.
  assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = true \/ Z.eqb (Znth b HL_framed_search 0) 0 = false) by (destruct (Z.eqb (Znth b HL_framed_search 0) 0); auto).
  destruct HL as [HL|HL]; rewrite HL; simpl; try (apply Z.eqb_eq in HL; exfalso; lia); try (apply Z.eqb_neq in HL; exfalso; lia).
  all: unfold simplex_scan_rat_memory; rewrite !simplex_scan_rat_member_address; cancel.
  all: cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + b * sizeof(INT)) # Int |-> Znth b HL_framed_search 0).
  all: cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + b * sizeof(INT)) # Int |-> Znth b HU_framed_search 0).
  all: sepcon_right_assoc; cancel.
  all: cancel emp.

Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_14 : sx_find_violation_entail_wit_7_14.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_14_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_14_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_14_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_14_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_14_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_14_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_15_split_goal_1 : sx_find_violation_entail_wit_7_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply row_prefix_step__keep_best_upper; try eassumption; try lia.
  unfold simplex_scan_rows.
  match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
  apply simplex_scan_row_upper_override; try lia; auto.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_15_split_goal_2 : sx_find_violation_entail_wit_7_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_15_split_goal_3 : sx_find_violation_entail_wit_7_15_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_15_split_goal_4 : sx_find_violation_entail_wit_7_15_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_15_split_goal_5 : sx_find_violation_entail_wit_7_15_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_15_split_goal_spatial : sx_find_violation_entail_wit_7_15_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__keep_best_upper S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
  rewrite HA. simpl.
  assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite HU. simpl.
  assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = true \/ Z.eqb (Znth b HL_framed_search 0) 0 = false) by (destruct (Z.eqb (Znth b HL_framed_search 0) 0); auto).
  destruct HL as [HL|HL]; rewrite HL; simpl; try (apply Z.eqb_eq in HL; exfalso; lia); try (apply Z.eqb_neq in HL; exfalso; lia).
  all: unfold simplex_scan_rat_memory; rewrite !simplex_scan_rat_member_address; cancel.
  all: cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + b * sizeof(INT)) # Int |-> Znth b HL_framed_search 0).
  all: cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + b * sizeof(INT)) # Int |-> Znth b HU_framed_search 0).
  all: sepcon_right_assoc; cancel.
  all: cancel emp.

Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_15 : sx_find_violation_entail_wit_7_15.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_15_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_15_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_15_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_15_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_15_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_15_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_16_split_goal_1 : sx_find_violation_entail_wit_7_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply row_prefix_step__keep_best_upper; try eassumption; try lia.
  unfold simplex_scan_rows.
  match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
  apply simplex_scan_row_upper_override; try lia; auto.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_16_split_goal_2 : sx_find_violation_entail_wit_7_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_16_split_goal_3 : sx_find_violation_entail_wit_7_16_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_16_split_goal_4 : sx_find_violation_entail_wit_7_16_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_16_split_goal_5 : sx_find_violation_entail_wit_7_16_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_16_split_goal_spatial : sx_find_violation_entail_wit_7_16_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__keep_best_upper S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
  rewrite HA. simpl.
  assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite HU. simpl.
  assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = true \/ Z.eqb (Znth b HL_framed_search 0) 0 = false) by (destruct (Z.eqb (Znth b HL_framed_search 0) 0); auto).
  destruct HL as [HL|HL]; rewrite HL; simpl; try (apply Z.eqb_eq in HL; exfalso; lia); try (apply Z.eqb_neq in HL; exfalso; lia).
  all: unfold simplex_scan_rat_memory; rewrite !simplex_scan_rat_member_address; cancel.
  all: cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + b * sizeof(INT)) # Int |-> Znth b HL_framed_search 0).
  all: cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + b * sizeof(INT)) # Int |-> Znth b HU_framed_search 0).
  all: sepcon_right_assoc; cancel.
  all: cancel emp.

Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_16 : sx_find_violation_entail_wit_7_16.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_16_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_16_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_16_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_16_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_16_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_16_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_17_split_goal_1 : sx_find_violation_entail_wit_7_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply row_prefix_step__keep_best_upper; try eassumption; try lia.
  unfold simplex_scan_rows.
  match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
  apply simplex_scan_row_upper_override; try lia; auto.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_17_split_goal_2 : sx_find_violation_entail_wit_7_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_17_split_goal_3 : sx_find_violation_entail_wit_7_17_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_17_split_goal_4 : sx_find_violation_entail_wit_7_17_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_17_split_goal_5 : sx_find_violation_entail_wit_7_17_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_17_split_goal_spatial : sx_find_violation_entail_wit_7_17_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__keep_best_upper S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
  rewrite HA. simpl.
  assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite HU. simpl.
  assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = true \/ Z.eqb (Znth b HL_framed_search 0) 0 = false) by (destruct (Z.eqb (Znth b HL_framed_search 0) 0); auto).
  destruct HL as [HL|HL]; rewrite HL; simpl; try (apply Z.eqb_eq in HL; exfalso; lia); try (apply Z.eqb_neq in HL; exfalso; lia).
  all: unfold simplex_scan_rat_memory; rewrite !simplex_scan_rat_member_address; cancel.
  all: cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + b * sizeof(INT)) # Int |-> Znth b HL_framed_search 0).
  all: cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + b * sizeof(INT)) # Int |-> Znth b HU_framed_search 0).
  all: sepcon_right_assoc; cancel.
  all: cancel emp.

Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_17 : sx_find_violation_entail_wit_7_17.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_17_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_17_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_17_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_17_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_17_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_17_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_18_split_goal_1 : sx_find_violation_entail_wit_7_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply row_prefix_step__keep_best_upper; try eassumption; try lia.
  unfold simplex_scan_rows.
  match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
  apply simplex_scan_row_upper_override; try lia; auto.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_18_split_goal_2 : sx_find_violation_entail_wit_7_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_18_split_goal_3 : sx_find_violation_entail_wit_7_18_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_18_split_goal_4 : sx_find_violation_entail_wit_7_18_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_18_split_goal_5 : sx_find_violation_entail_wit_7_18_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto); dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_18_split_goal_spatial : sx_find_violation_entail_wit_7_18_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__keep_best_upper S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
  rewrite HA. simpl.
  assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite HU. simpl.
  assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = true \/ Z.eqb (Znth b HL_framed_search 0) 0 = false) by (destruct (Z.eqb (Znth b HL_framed_search 0) 0); auto).
  destruct HL as [HL|HL]; rewrite HL; simpl; try (apply Z.eqb_eq in HL; exfalso; lia); try (apply Z.eqb_neq in HL; exfalso; lia).
  all: unfold simplex_scan_rat_memory; rewrite !simplex_scan_rat_member_address; cancel.
  all: cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + b * sizeof(INT)) # Int |-> Znth b HL_framed_search 0).
  all: cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + b * sizeof(INT)) # Int |-> Znth b HU_framed_search 0).
  all: sepcon_right_assoc; cancel.
  all: cancel emp.

Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_18 : sx_find_violation_entail_wit_7_18.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_18_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_18_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_18_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_18_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_18_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
  Goal_apply (proof_of_sx_find_violation_entail_wit_7_18_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_19_split_goal_1 : sx_find_violation_entail_wit_7_19_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 eapply row_prefix_step__keep_best_lower with (d:=1); try eassumption; try lia.
 unfold simplex_scan_rows. rewrite <- PreH30.
 unfold simplex_scan_row.
 repeat match goal with
 | |- context [Z.eqb ?x 0] => let E := fresh "E" in destruct (Z.eqb x 0) eqn:E; [apply Z.eqb_eq in E; try congruence|apply Z.eqb_neq in E; try tauto]
 end.
 all: repeat match goal with
 | H : ?x = simplex_rat_compare_flag _ _ _ _, H' : ?x = 1 |- _ => rewrite <- H, H'
 | |- context [Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E|apply Z.ltb_ge in E]; try lia
 end; reflexivity.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_19_split_goal_2 : sx_find_violation_entail_wit_7_19_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_19_split_goal_3 : sx_find_violation_entail_wit_7_19_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_19_split_goal_4 : sx_find_violation_entail_wit_7_19_split_goal_4.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_19_split_goal_5 : sx_find_violation_entail_wit_7_19_split_goal_5.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_19_split_goal_spatial : sx_find_violation_entail_wit_7_19_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__keep_best_lower S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
 assert (EA : existsb (Z.eqb b) BAS_framed_search = true).
 { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
 unfold simplex_scan_read_slot. rewrite EA. simpl.
 repeat match goal with
 | |- context [Z.eqb ?x 0] => let E := fresh "E" in destruct (Z.eqb x 0) eqn:E; [apply Z.eqb_eq in E; try congruence|apply Z.eqb_neq in E; try tauto]
 end.
 all: simpl; unfold simplex_scan_rat_memory; csimpl; cancel.
 all: sepcon_right_assoc; repeat match goal with |- _ |-- ?p ** _ => progress (cancel p); sepcon_right_assoc end; cancel.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_19 : sx_find_violation_entail_wit_7_19.
Proof.
 aggressive_pre_process.
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_19_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_19_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_19_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_19_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_19_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_19_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_20_split_goal_1 : sx_find_violation_entail_wit_7_20_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 eapply row_prefix_step__keep_best_lower with (d:=1); try eassumption; try lia.
 unfold simplex_scan_rows. rewrite <- PreH30.
 unfold simplex_scan_row.
 repeat match goal with
 | |- context [Z.eqb ?x 0] => let E := fresh "E" in destruct (Z.eqb x 0) eqn:E; [apply Z.eqb_eq in E; try congruence|apply Z.eqb_neq in E; try tauto]
 end.
 all: repeat match goal with
 | H : ?x = simplex_rat_compare_flag _ _ _ _, H' : ?x = 1 |- _ => rewrite <- H, H'
 | |- context [Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E|apply Z.ltb_ge in E]; try lia
 end; reflexivity.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_20_split_goal_2 : sx_find_violation_entail_wit_7_20_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_20_split_goal_3 : sx_find_violation_entail_wit_7_20_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_20_split_goal_4 : sx_find_violation_entail_wit_7_20_split_goal_4.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_20_split_goal_5 : sx_find_violation_entail_wit_7_20_split_goal_5.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_20_split_goal_spatial : sx_find_violation_entail_wit_7_20_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__keep_best_lower S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
 assert (EA : existsb (Z.eqb b) BAS_framed_search = true).
 { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
 unfold simplex_scan_read_slot. rewrite EA. simpl.
 repeat match goal with
 | |- context [Z.eqb ?x 0] => let E := fresh "E" in destruct (Z.eqb x 0) eqn:E; [apply Z.eqb_eq in E; try congruence|apply Z.eqb_neq in E; try tauto]
 end.
 all: simpl; unfold simplex_scan_rat_memory; csimpl; cancel.
 all: sepcon_right_assoc; repeat match goal with |- _ |-- ?p ** _ => progress (cancel p); sepcon_right_assoc end; cancel.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_20 : sx_find_violation_entail_wit_7_20.
Proof.
 aggressive_pre_process.
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_20_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_20_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_20_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_20_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_20_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_20_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_21_split_goal_1 : sx_find_violation_entail_wit_7_21_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 eapply row_prefix_step__keep_best_lower with (d:=1); try eassumption; try lia.
 unfold simplex_scan_rows. rewrite <- PreH22.
 unfold simplex_scan_row.
 repeat match goal with
 | |- context [Z.eqb ?x 0] => let E := fresh "E" in destruct (Z.eqb x 0) eqn:E; [apply Z.eqb_eq in E; try congruence|apply Z.eqb_neq in E; try tauto]
 end.
 all: repeat match goal with
 | H : ?x = simplex_rat_compare_flag _ _ _ _, H' : ?x = 1 |- _ => rewrite <- H, H'
 | |- context [Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E|apply Z.ltb_ge in E]; try lia
 end; reflexivity.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_21_split_goal_2 : sx_find_violation_entail_wit_7_21_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_21_split_goal_3 : sx_find_violation_entail_wit_7_21_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_21_split_goal_4 : sx_find_violation_entail_wit_7_21_split_goal_4.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_21_split_goal_5 : sx_find_violation_entail_wit_7_21_split_goal_5.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_21_split_goal_spatial : sx_find_violation_entail_wit_7_21_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__keep_best_lower S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
 assert (EA : existsb (Z.eqb b) BAS_framed_search = true).
 { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
 unfold simplex_scan_read_slot. rewrite EA. simpl.
 repeat match goal with
 | |- context [Z.eqb ?x 0] => let E := fresh "E" in destruct (Z.eqb x 0) eqn:E; [apply Z.eqb_eq in E; try congruence|apply Z.eqb_neq in E; try tauto]
 end.
 all: simpl; unfold simplex_scan_rat_memory; csimpl; cancel.
 all: sepcon_right_assoc; repeat match goal with |- _ |-- ?p ** _ => progress (cancel p); sepcon_right_assoc end; cancel.
Qed.

Lemma proof_of_sx_find_violation_entail_wit_7_21 : sx_find_violation_entail_wit_7_21.
Proof.
 aggressive_pre_process.
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_21_split_goal_spatial S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_21_split_goal_1 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_21_split_goal_2 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_21_split_goal_3 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_21_split_goal_4 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39).
 Goal_apply (proof_of_sx_find_violation_entail_wit_7_21_split_goal_5 S_framed_search V_framed_search M_framed_search UD_framed_search UN_framed_search LD_framed_search LN_framed_search VD_framed_search VN_framed_search HU_framed_search HL_framed_search BAS_framed_search R_2 D_2 i b best retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39).
Qed.

Lemma proof_of_sx_find_violation_return_wit_1_split_goal_1 : sx_find_violation_return_wit_1_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (i = M_framed_search) by lia. subst i. eapply prefix_finish__init_finish; exact PreH14.
Qed.

Lemma proof_of_sx_find_violation_return_wit_1 : sx_find_violation_return_wit_1.
Proof.
aggressive_pre_process.
Goal_apply proof_of_sx_find_violation_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_sx_find_violation_return_wit_2_split_goal_1 : sx_find_violation_return_wit_2_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 eapply prefix_failure__upper_failure; [eassumption|split; eassumption|].
 unfold simplex_scan_rows.
 match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
 apply simplex_scan_row_upper_failure; [assumption|congruence].
Qed.

Lemma proof_of_sx_find_violation_return_wit_2_split_goal_spatial : sx_find_violation_return_wit_2_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__upper_failure S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
 { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
 rewrite HA. cbn beta iota zeta.
 cbn [andb].
 assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite HU.
 assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = true) by (apply Z.eqb_eq; assumption).
 rewrite HL. cbn [andb orb negb].
 rewrite !simplex_scan_rat_memory_enabled.
 repeat rewrite sepcon_right_assoc.
 replace (sizeof(INT)) with 4 by reflexivity.
 all: try cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + b * 4) # Int |-> Znth b HL_framed_search 0).
 all: try cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + b * 4) # Int |-> Znth b HU_framed_search 0).
 repeat rewrite sepcon_right_assoc.
 all: try cancel.
 all: try cancel emp.
 all: try (match goal with |- ?G => idtac G end).
Qed.

Lemma proof_of_sx_find_violation_return_wit_2 : sx_find_violation_return_wit_2.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_violation_return_wit_2_split_goal_spatial.
 - Goal_apply proof_of_sx_find_violation_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_sx_find_violation_return_wit_3_split_goal_1 : sx_find_violation_return_wit_3_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 eapply prefix_failure__upper_failure; [eassumption|split; eassumption|].
 unfold simplex_scan_rows.
 match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
 apply simplex_scan_row_upper_failure; [assumption|congruence].
Qed.

Lemma proof_of_sx_find_violation_return_wit_3_split_goal_spatial : sx_find_violation_return_wit_3_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__upper_failure S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
 { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
 rewrite HA. cbn beta iota zeta.
 cbn [andb].
 assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite HU.
 assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite HL. cbn [andb orb negb].
 rewrite !simplex_scan_rat_memory_enabled.
 repeat rewrite sepcon_right_assoc.
 replace (sizeof(INT)) with 4 by reflexivity.
 all: try cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + b * 4) # Int |-> Znth b HL_framed_search 0).
 all: try cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + b * 4) # Int |-> Znth b HU_framed_search 0).
 repeat rewrite sepcon_right_assoc.
 all: try cancel.
 all: try cancel emp.
 all: try (match goal with |- ?G => idtac G end).
Qed.

Lemma proof_of_sx_find_violation_return_wit_3 : sx_find_violation_return_wit_3.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_violation_return_wit_3_split_goal_spatial.
 - Goal_apply proof_of_sx_find_violation_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_sx_find_violation_return_wit_4_split_goal_1 : sx_find_violation_return_wit_4_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 eapply prefix_failure__upper_failure; [eassumption|split; eassumption|].
 unfold simplex_scan_rows.
 match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
 apply simplex_scan_row_upper_failure; [assumption|congruence].
Qed.

Lemma proof_of_sx_find_violation_return_wit_4_split_goal_spatial : sx_find_violation_return_wit_4_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__upper_failure S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
 { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
 rewrite HA. cbn beta iota zeta.
 cbn [andb].
 assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite HU.
 assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite HL. cbn [andb orb negb].
 rewrite !simplex_scan_rat_memory_enabled.
 repeat rewrite sepcon_right_assoc.
 replace (sizeof(INT)) with 4 by reflexivity.
 all: try cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + b * 4) # Int |-> Znth b HL_framed_search 0).
 all: try cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + b * 4) # Int |-> Znth b HU_framed_search 0).
 repeat rewrite sepcon_right_assoc.
 all: try cancel.
 all: try cancel emp.
 all: try (match goal with |- ?G => idtac G end).
Qed.

Lemma proof_of_sx_find_violation_return_wit_4 : sx_find_violation_return_wit_4.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_violation_return_wit_4_split_goal_spatial.
 - Goal_apply proof_of_sx_find_violation_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_sx_find_violation_return_wit_5_split_goal_1 : sx_find_violation_return_wit_5_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 eapply prefix_failure__upper_failure; [eassumption|split; eassumption|].
 unfold simplex_scan_rows.
 match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
 apply simplex_scan_row_upper_failure; [assumption|congruence].
Qed.

Lemma proof_of_sx_find_violation_return_wit_5_split_goal_spatial : sx_find_violation_return_wit_5_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__upper_failure S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
 { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
 rewrite HA. cbn beta iota zeta.
 cbn [andb].
 assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite HU.
 assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite HL. cbn [andb orb negb].
 rewrite !simplex_scan_rat_memory_enabled.
 repeat rewrite sepcon_right_assoc.
 replace (sizeof(INT)) with 4 by reflexivity.
 all: try cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + b * 4) # Int |-> Znth b HL_framed_search 0).
 all: try cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + b * 4) # Int |-> Znth b HU_framed_search 0).
 repeat rewrite sepcon_right_assoc.
 all: try cancel.
 all: try cancel emp.
 all: try (match goal with |- ?G => idtac G end).
Qed.

Lemma proof_of_sx_find_violation_return_wit_5 : sx_find_violation_return_wit_5.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_violation_return_wit_5_split_goal_spatial.
 - Goal_apply proof_of_sx_find_violation_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_sx_find_violation_return_wit_6_split_goal_1 : sx_find_violation_return_wit_6_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 eapply prefix_failure__upper_failure; [eassumption|split; eassumption|].
 unfold simplex_scan_rows.
 match goal with H : b = Znth i BAS_framed_search 0 |- _ => rewrite <- H end.
 apply simplex_scan_row_upper_failure; [assumption|congruence].
Qed.

Lemma proof_of_sx_find_violation_return_wit_6_split_goal_spatial : sx_find_violation_return_wit_6_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__upper_failure S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
 { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
 rewrite HA. cbn beta iota zeta.
 cbn [andb].
 assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite HU.
 assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite HL. cbn [andb orb negb].
 rewrite !simplex_scan_rat_memory_enabled.
 repeat rewrite sepcon_right_assoc.
 replace (sizeof(INT)) with 4 by reflexivity.
 all: try cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + b * 4) # Int |-> Znth b HL_framed_search 0).
 all: try cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + b * 4) # Int |-> Znth b HU_framed_search 0).
 repeat rewrite sepcon_right_assoc.
 all: try cancel.
 all: try cancel emp.
 all: try (match goal with |- ?G => idtac G end).
Qed.

Lemma proof_of_sx_find_violation_return_wit_6 : sx_find_violation_return_wit_6.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_violation_return_wit_6_split_goal_spatial.
 - Goal_apply proof_of_sx_find_violation_return_wit_6_split_goal_1.
Qed.

Lemma proof_of_sx_find_violation_return_wit_7_split_goal_1 : sx_find_violation_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply prefix_failure__lower_failure with (i:=i) (best:=best); [lia|eassumption|].
  unfold simplex_scan_rows.
  rewrite <- PreH20.
  apply simplex_scan_row_lower_failure; [assumption|lia].
Qed.

Lemma proof_of_sx_find_violation_return_wit_7_split_goal_spatial : sx_find_violation_return_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__lower_failure S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
  assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = true) by (apply Z.eqb_eq; lia).
  rewrite HA, HL, HU.
  cbn [andb negb orb].
  unfold simplex_scan_rat_memory.
  repeat rewrite simplex_scan_rat_member_address.
  sepcon_right_assoc.
  repeat match goal with |- _ |-- ?P ** _ => progress (cancel P) end.
  all: match goal with |- _ |-- ?P => cancel P end.
Qed.

Lemma proof_of_sx_find_violation_return_wit_7 : sx_find_violation_return_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_return_wit_7_split_goal_spatial.
  - Goal_apply proof_of_sx_find_violation_return_wit_7_split_goal_1.
Qed.

Lemma proof_of_sx_find_violation_return_wit_8_split_goal_1 : sx_find_violation_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply prefix_failure__lower_failure with (i:=i) (best:=best); [lia|eassumption|].
  unfold simplex_scan_rows.
  rewrite <- PreH24.
  apply simplex_scan_row_lower_failure; [assumption|lia].
Qed.

Lemma proof_of_sx_find_violation_return_wit_8_split_goal_spatial : sx_find_violation_return_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__lower_failure S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
  assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
  rewrite HA, HL, HU.
  cbn [andb negb orb].
  unfold simplex_scan_rat_memory.
  repeat rewrite simplex_scan_rat_member_address.
  sepcon_right_assoc.
  repeat match goal with |- _ |-- ?P ** _ => progress (cancel P) end.
  all: match goal with |- _ |-- ?P => cancel P end.
Qed.

Lemma proof_of_sx_find_violation_return_wit_8 : sx_find_violation_return_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_return_wit_8_split_goal_spatial.
  - Goal_apply proof_of_sx_find_violation_return_wit_8_split_goal_1.
Qed.

Lemma proof_of_sx_find_violation_return_wit_9_split_goal_1 : sx_find_violation_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply prefix_failure__lower_failure with (i:=i) (best:=best); [lia|eassumption|].
  unfold simplex_scan_rows.
  rewrite <- PreH24.
  apply simplex_scan_row_lower_failure; [assumption|lia].
Qed.

Lemma proof_of_sx_find_violation_return_wit_9_split_goal_spatial : sx_find_violation_return_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (read_slot_merge__lower_failure S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search BAS_framed_search HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search b).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb b) BAS_framed_search = true).
  { apply existsb_exists. exists b. split; [assumption|apply Z.eqb_refl]. }
  assert (HL : Z.eqb (Znth b HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  assert (HU : Z.eqb (Znth b HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
  rewrite HA, HL, HU.
  cbn [andb negb orb].
  unfold simplex_scan_rat_memory.
  repeat rewrite simplex_scan_rat_member_address.
  sepcon_right_assoc.
  repeat match goal with |- _ |-- ?P ** _ => progress (cancel P) end.
  all: match goal with |- _ |-- ?P => cancel P end.
Qed.

Lemma proof_of_sx_find_violation_return_wit_9 : sx_find_violation_return_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_return_wit_9_split_goal_spatial.
  - Goal_apply proof_of_sx_find_violation_return_wit_9_split_goal_1.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_2_pure_split_goal_1 : sx_find_violation_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH42 b ltac:(auto)) as Hfraction.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_2_pure_split_goal_2 : sx_find_violation_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH43 b ltac:(auto)) as Hfraction.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_2_pure : sx_find_violation_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_2_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_3_pure_split_goal_1 : sx_find_violation_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH46 b ltac:(auto)) as Hfraction.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_3_pure_split_goal_2 : sx_find_violation_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH47 b ltac:(auto)) as Hfraction.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_3_pure : sx_find_violation_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_3_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_4_pure_split_goal_1 : sx_find_violation_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH46 b ltac:(auto)) as Hfraction.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_4_pure_split_goal_2 : sx_find_violation_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH47 b ltac:(auto)) as Hfraction.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_4_pure : sx_find_violation_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_4_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_5_pure_split_goal_1 : sx_find_violation_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH42 b ltac:(tauto)) as Hbounds.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_5_pure_split_goal_2 : sx_find_violation_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH44 b ltac:(tauto)) as Hbounds.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_5_pure : sx_find_violation_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_5_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_6_pure_split_goal_1 : sx_find_violation_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH52 b ltac:(tauto)) as Hbounds.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_6_pure_split_goal_2 : sx_find_violation_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH54 b ltac:(tauto)) as Hbounds.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_6_pure : sx_find_violation_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_6_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_6_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_7_pure_split_goal_1 : sx_find_violation_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH52 b ltac:(tauto)) as Hbounds.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_7_pure_split_goal_2 : sx_find_violation_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH54 b ltac:(tauto)) as Hbounds.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_7_pure : sx_find_violation_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_7_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_7_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_8_pure_split_goal_1 : sx_find_violation_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH52 b ltac:(tauto)) as Hbounds.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_8_pure_split_goal_2 : sx_find_violation_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH54 b ltac:(tauto)) as Hbounds.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_8_pure : sx_find_violation_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_8_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_8_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_9_pure_split_goal_1 : sx_find_violation_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH52 b ltac:(tauto)) as Hbounds.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_9_pure_split_goal_2 : sx_find_violation_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH54 b ltac:(tauto)) as Hbounds.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_9_pure : sx_find_violation_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_9_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_9_pure_split_goal_2.
Qed.

