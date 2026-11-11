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
From SimpleC.EE.Applications_human.simplex_find_violation_retry Require Import simplex_find_violation_retry_goal.
From SimpleC.EE.Applications_human.simplex_find_violation_retry Require Import simplex_find_violation_retry_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_rat_compare.simplex_rat_compare_lib.
Require Import SimpleC.EE.Applications_human.simplex_find_violation_retry.simplex_find_violation_retry_lib.
Local Open Scope sac.

Lemma proof_of_sx_find_violation_entail_wit_1_separated_search_split_goal_1 : sx_find_violation_entail_wit_1_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_1_separated_search_split_goal_2 : sx_find_violation_entail_wit_1_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_1_separated_search_split_goal_3 : sx_find_violation_entail_wit_1_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_1_separated_search_split_goal_4 : sx_find_violation_entail_wit_1_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_1_separated_search_split_goal_5 : sx_find_violation_entail_wit_1_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_1_separated_search_split_goal_spatial : sx_find_violation_entail_wit_1_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_1_separated_search : sx_find_violation_entail_wit_1_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst s_pre row_pre direction_pre.
  Exists (-1) 0.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold simplex_scan_prefix. split; [intros; lia|apply simplex_scan_candidate_empty].
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_2_separated_search : sx_find_violation_entail_wit_2_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sepcon_right_assoc.
  prop_apply (IntArray.full_Zlength &(S_separated_search # "SxState" ->ₛ "basic") M_separated_search BAS_separated_search).
  Intros_p Hlen.
  assert (Hin : In (Znth i BAS_separated_search 0) BAS_separated_search).
  { unfold Znth. apply nth_In. rewrite Zlength_correct in Hlen. lia. }
  pose proof (PreH10 i ltac:(lia)) as Hb.
  sep_apply (simplex_scan_slots_split S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search (Znth i BAS_separated_search 0) ltac:(lia)).
  rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search (Znth i BAS_separated_search 0) Hin).
  destruct (Z.eqb (Znth (Znth i BAS_separated_search 0) HL_separated_search 0) 0) eqn:EL;
  destruct (Z.eqb (Znth (Znth i BAS_separated_search 0) HU_separated_search 0) 0) eqn:EU.
  all: unfold simplex_scan_rat_memory; cbn [negb orb]; rewrite !simplex_scan_rat_member_address.
  - Left. Left. Left. Left.
    Exists R_2 D_2.
    split_pure_spatial.
    + sepcon_right_assoc. cancel.
    + apply Z.eqb_eq in EL; apply Z.eqb_eq in EU.
      split_pures; dump_pre_spatial; try assumption; try lia; tauto.
  - Right.
    Exists R_2 D_2.
    split_pure_spatial.
    + sepcon_right_assoc. cancel.
    + apply Z.eqb_eq in EL; apply Z.eqb_neq in EU.
      split_pures; dump_pre_spatial; try assumption; try lia; tauto.
  - Left. Left. Left. Right.
    Exists R_2 D_2.
    split_pure_spatial.
    + sepcon_right_assoc. cancel.
    + apply Z.eqb_neq in EL; apply Z.eqb_eq in EU.
      split_pures; dump_pre_spatial; try assumption; try lia; tauto.
  - Left. Left. Right.
    Exists R_2 D_2.
    split_pure_spatial.
    + sepcon_right_assoc. cancel.
    + apply Z.eqb_neq in EL; apply Z.eqb_neq in EU.
      split_pures; dump_pre_spatial; try assumption; try lia; tauto.
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_1_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_1_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_1_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_1_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_1_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_1_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_1_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_1_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_1_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_1_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_1_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_1_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_1_separated_search : sx_find_violation_entail_wit_7_1_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hb : b = Znth i BAS_separated_search 0) by assumption.
  assert (Hobs : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some (-1)).
  { unfold simplex_scan_rows.
    rewrite <- Hb.
    apply simplex_scan_row_upper_override; try assumption; try congruence.
    first [left; assumption | right; congruence]. }
  assert (Hnext : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) b i (-1)).
  { match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ i best R_2 D_2 |- _ =>
      destruct H as [Hchecks Hcand] end.
    unfold simplex_scan_prefix. split.
    - intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
      + unfold simplex_scan_check. rewrite Hobs. reflexivity.
      + apply Hchecks. lia.
    - pose proof (simplex_scan_candidate_step
        (fun j => Znth j BAS_separated_search 0)
        (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search))
        V_separated_search i best R_2 D_2 ltac:(lia) ltac:(cbn beta; rewrite <- Hb; lia) Hcand) as Hstep.
      assert (Hdir : simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search) i = -1).
      { unfold simplex_scan_direction. rewrite Hobs. reflexivity. }
      rewrite Hdir in Hstep. cbn beta in Hstep. rewrite <- Hb in Hstep.
      assert (Eb : Z.ltb b best = true) by (apply Z.ltb_lt; lia).
      rewrite Eb in Hstep. exact Hstep. }
  Exists i (-1).
  split_pure_spatial.
  2: { split_pures; dump_pre_spatial; solve [assumption | lia]. }
  sep_apply (store_int_undef_store_int (&("b")) b).
  sep_apply (store_int_undef_store_int (&("cmp")) (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
  sep_apply (store_int_undef_store_int (&("d")) (-1)).
  sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
  rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
  unfold simplex_scan_rat_memory.
  assert (Eu : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite Eu. simpl.
  first [
    assert (El : Z.eqb (Znth b HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; assumption)
  | assert (El : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption)].
  rewrite El. simpl.
  rewrite !simplex_scan_rat_member_address.
  sepcon_assoc_change.
  cancel.
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_2_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_2_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_2_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_2_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_2_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_2_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_2_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_2_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_2_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_2_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_2_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_2_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_2_separated_search : sx_find_violation_entail_wit_7_2_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hb : b = Znth i BAS_separated_search 0) by assumption.
  assert (Hobs : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some (-1)).
  { unfold simplex_scan_rows.
    rewrite <- Hb.
    apply simplex_scan_row_upper_override; try assumption; try congruence.
    first [left; assumption | right; congruence]. }
  assert (Hnext : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) b i (-1)).
  { match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ i best R_2 D_2 |- _ =>
      destruct H as [Hchecks Hcand] end.
    unfold simplex_scan_prefix. split.
    - intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
      + unfold simplex_scan_check. rewrite Hobs. reflexivity.
      + apply Hchecks. lia.
    - pose proof (simplex_scan_candidate_step
        (fun j => Znth j BAS_separated_search 0)
        (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search))
        V_separated_search i best R_2 D_2 ltac:(lia) ltac:(cbn beta; rewrite <- Hb; lia) Hcand) as Hstep.
      assert (Hdir : simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search) i = -1).
      { unfold simplex_scan_direction. rewrite Hobs. reflexivity. }
      rewrite Hdir in Hstep. cbn beta in Hstep. rewrite <- Hb in Hstep.
      assert (Eb : Z.ltb b best = true) by (apply Z.ltb_lt; lia).
      rewrite Eb in Hstep. exact Hstep. }
  Exists i (-1).
  split_pure_spatial.
  2: { split_pures; dump_pre_spatial; solve [assumption | lia]. }
  sep_apply (store_int_undef_store_int (&("b")) b).
  sep_apply (store_int_undef_store_int (&("cmp")) (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
  sep_apply (store_int_undef_store_int (&("d")) (-1)).
  sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
  rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
  unfold simplex_scan_rat_memory.
  assert (Eu : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite Eu. simpl.
  first [
    assert (El : Z.eqb (Znth b HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; assumption)
  | assert (El : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption)].
  rewrite El. simpl.
  rewrite !simplex_scan_rat_member_address.
  sepcon_assoc_change.
  cancel.
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_3_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_3_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_3_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_3_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_3_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_3_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_3_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_3_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_3_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_3_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_3_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_3_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_3_separated_search : sx_find_violation_entail_wit_7_3_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hb : b = Znth i BAS_separated_search 0) by assumption.
  assert (Hobs : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some (-1)).
  { unfold simplex_scan_rows.
    rewrite <- Hb.
    apply simplex_scan_row_upper_override; try assumption; try congruence.
    first [left; assumption | right; congruence]. }
  assert (Hnext : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) b i (-1)).
  { match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ i best R_2 D_2 |- _ =>
      destruct H as [Hchecks Hcand] end.
    unfold simplex_scan_prefix. split.
    - intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
      + unfold simplex_scan_check. rewrite Hobs. reflexivity.
      + apply Hchecks. lia.
    - pose proof (simplex_scan_candidate_step
        (fun j => Znth j BAS_separated_search 0)
        (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search))
        V_separated_search i best R_2 D_2 ltac:(lia) ltac:(cbn beta; rewrite <- Hb; lia) Hcand) as Hstep.
      assert (Hdir : simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search) i = -1).
      { unfold simplex_scan_direction. rewrite Hobs. reflexivity. }
      rewrite Hdir in Hstep. cbn beta in Hstep. rewrite <- Hb in Hstep.
      assert (Eb : Z.ltb b best = true) by (apply Z.ltb_lt; lia).
      rewrite Eb in Hstep. exact Hstep. }
  Exists i (-1).
  split_pure_spatial.
  2: { split_pures; dump_pre_spatial; solve [assumption | lia]. }
  sep_apply (store_int_undef_store_int (&("b")) b).
  sep_apply (store_int_undef_store_int (&("cmp")) (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
  sep_apply (store_int_undef_store_int (&("d")) (-1)).
  sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
  rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
  unfold simplex_scan_rat_memory.
  assert (Eu : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite Eu. simpl.
  first [
    assert (El : Z.eqb (Znth b HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; assumption)
  | assert (El : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption)].
  rewrite El. simpl.
  rewrite !simplex_scan_rat_member_address.
  sepcon_assoc_change.
  cancel.
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_4_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_4_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_4_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_4_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_4_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_4_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_4_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_4_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_4_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_4_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_4_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_4_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_4_separated_search : sx_find_violation_entail_wit_7_4_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hb : b = Znth i BAS_separated_search 0) by assumption.
  assert (Hobs : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some (-1)).
  { unfold simplex_scan_rows.
    rewrite <- Hb.
    apply simplex_scan_row_upper_override; try assumption; try congruence.
    first [left; assumption | right; congruence]. }
  assert (Hnext : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) b i (-1)).
  { match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ i best R_2 D_2 |- _ =>
      destruct H as [Hchecks Hcand] end.
    unfold simplex_scan_prefix. split.
    - intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
      + unfold simplex_scan_check. rewrite Hobs. reflexivity.
      + apply Hchecks. lia.
    - pose proof (simplex_scan_candidate_step
        (fun j => Znth j BAS_separated_search 0)
        (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search))
        V_separated_search i best R_2 D_2 ltac:(lia) ltac:(cbn beta; rewrite <- Hb; lia) Hcand) as Hstep.
      assert (Hdir : simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search) i = -1).
      { unfold simplex_scan_direction. rewrite Hobs. reflexivity. }
      rewrite Hdir in Hstep. cbn beta in Hstep. rewrite <- Hb in Hstep.
      assert (Eb : Z.ltb b best = true) by (apply Z.ltb_lt; lia).
      rewrite Eb in Hstep. exact Hstep. }
  Exists i (-1).
  split_pure_spatial.
  2: { split_pures; dump_pre_spatial; solve [assumption | lia]. }
  sep_apply (store_int_undef_store_int (&("b")) b).
  sep_apply (store_int_undef_store_int (&("cmp")) (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
  sep_apply (store_int_undef_store_int (&("d")) (-1)).
  sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
  rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
  unfold simplex_scan_rat_memory.
  assert (Eu : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite Eu. simpl.
  first [
    assert (El : Z.eqb (Znth b HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; assumption)
  | assert (El : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption)].
  rewrite El. simpl.
  rewrite !simplex_scan_rat_member_address.
  sepcon_assoc_change.
  cancel.
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_5_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_5_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_5_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_5_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_5_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_5_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_5_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_5_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_5_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_5_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_5_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_5_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_5_separated_search : sx_find_violation_entail_wit_7_5_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hb : b = Znth i BAS_separated_search 0) by assumption.
  assert (Hobs : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some (-1)).
  { unfold simplex_scan_rows.
    rewrite <- Hb.
    apply simplex_scan_row_upper_override; try assumption; try congruence.
    first [left; assumption | right; congruence]. }
  assert (Hnext : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) b i (-1)).
  { match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ i best R_2 D_2 |- _ =>
      destruct H as [Hchecks Hcand] end.
    unfold simplex_scan_prefix. split.
    - intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
      + unfold simplex_scan_check. rewrite Hobs. reflexivity.
      + apply Hchecks. lia.
    - pose proof (simplex_scan_candidate_step
        (fun j => Znth j BAS_separated_search 0)
        (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search))
        V_separated_search i best R_2 D_2 ltac:(lia) ltac:(cbn beta; rewrite <- Hb; lia) Hcand) as Hstep.
      assert (Hdir : simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search) i = -1).
      { unfold simplex_scan_direction. rewrite Hobs. reflexivity. }
      rewrite Hdir in Hstep. cbn beta in Hstep. rewrite <- Hb in Hstep.
      assert (Eb : Z.ltb b best = true) by (apply Z.ltb_lt; lia).
      rewrite Eb in Hstep. exact Hstep. }
  Exists i (-1).
  split_pure_spatial.
  2: { split_pures; dump_pre_spatial; solve [assumption | lia]. }
  sep_apply (store_int_undef_store_int (&("b")) b).
  sep_apply (store_int_undef_store_int (&("cmp")) (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
  sep_apply (store_int_undef_store_int (&("d")) (-1)).
  sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
  rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
  unfold simplex_scan_rat_memory.
  assert (Eu : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite Eu. simpl.
  first [
    assert (El : Z.eqb (Znth b HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; assumption)
  | assert (El : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption)].
  rewrite El. simpl.
  rewrite !simplex_scan_rat_member_address.
  sepcon_assoc_change.
  cancel.
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_6_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_6_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_6_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_6_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_6_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_6_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_6_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_6_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_6_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_6_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_6_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_6_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_6_separated_search : sx_find_violation_entail_wit_7_6_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 assert (EU : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 assert (FL : simplex_rat_compare_flag (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b LN_separated_search 0) (Znth b LD_separated_search 0) = 1) by congruence.
 assert (OL : Z.ltb (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b LN_separated_search 0) (Znth b LD_separated_search 0)) 0 = true) by (apply Z.ltb_lt; assumption).
 assert (FU : simplex_rat_compare_flag (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0) = 1) by congruence.
 assert (OU : Z.ltb 0 (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0)) = false) by (apply Z.ltb_ge; lia).
 assert (OBS : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some 1).
 { unfold simplex_scan_rows. match goal with H : b = Znth i BAS_separated_search 0 |- _ => rewrite <- H end.
 unfold simplex_scan_row. rewrite EL, EU, FL, OL, FU, OU. reflexivity. }
 match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
 unfold simplex_scan_prefix in H; destruct H as [CHECK CAND] end.
 assert (HBI : Znth i BAS_separated_search 0 < V_separated_search) by lia.
 pose proof (simplex_scan_candidate_step (fun j => Znth j BAS_separated_search 0)
 (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search)) V_separated_search i best R_2 D_2 ltac:(lia) HBI CAND) as STEP.
 assert (DIR : simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search) i = 1) by (unfold simplex_scan_direction; rewrite OBS; reflexivity).
 rewrite DIR in STEP. simpl in STEP.
 match goal with H : b = Znth i BAS_separated_search 0 |- _ => rewrite <- H in STEP end.
 assert (EB : Z.ltb b best = true) by (apply Z.ltb_lt; assumption).
 rewrite EB in STEP. simpl in STEP.
 Exists i 1.
 split_pure_spatial.
 - sep_apply_l_atomic (store_int_undef_store_int &("b") b).
   sep_apply_l_atomic (store_int_undef_store_int &("cmp") (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
   sep_apply_l_atomic (store_int_undef_store_int &("d") 1).
   sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
   rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
   unfold simplex_scan_rat_memory. rewrite EL, EU. simpl.
   rewrite (simplex_scan_rat_member_address S_separated_search "value" "num" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "value" "den" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
   sepcon_right_assoc. cancel.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   unfold simplex_scan_prefix. split; [|exact STEP].
   intros j HJ. destruct (Z.eq_dec j i); [subst; unfold simplex_scan_check; rewrite OBS; reflexivity|apply CHECK; lia].
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_7_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_7_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_7_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_7_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_7_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_7_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_7_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_7_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_7_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_7_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_7_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_7_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_7_separated_search : sx_find_violation_entail_wit_7_7_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 assert (EU : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 assert (FL : simplex_rat_compare_flag (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b LN_separated_search 0) (Znth b LD_separated_search 0) = 1) by congruence.
 assert (OL : Z.ltb (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b LN_separated_search 0) (Znth b LD_separated_search 0)) 0 = true) by (apply Z.ltb_lt; assumption).
 assert (FU : simplex_rat_compare_flag (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0) = 1) by congruence.
 assert (OU : Z.ltb 0 (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0)) = false) by (apply Z.ltb_ge; lia).
 assert (OBS : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some 1).
 { unfold simplex_scan_rows. match goal with H : b = Znth i BAS_separated_search 0 |- _ => rewrite <- H end.
 unfold simplex_scan_row. rewrite EL, EU, FL, OL, FU, OU. reflexivity. }
 match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
 unfold simplex_scan_prefix in H; destruct H as [CHECK CAND] end.
 assert (HBI : Znth i BAS_separated_search 0 < V_separated_search) by lia.
 pose proof (simplex_scan_candidate_step (fun j => Znth j BAS_separated_search 0)
 (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search)) V_separated_search i best R_2 D_2 ltac:(lia) HBI CAND) as STEP.
 assert (DIR : simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search) i = 1) by (unfold simplex_scan_direction; rewrite OBS; reflexivity).
 rewrite DIR in STEP. simpl in STEP.
 match goal with H : b = Znth i BAS_separated_search 0 |- _ => rewrite <- H in STEP end.
 assert (EB : Z.ltb b best = true) by (apply Z.ltb_lt; assumption).
 rewrite EB in STEP. simpl in STEP.
 Exists i 1.
 split_pure_spatial.
 - sep_apply_l_atomic (store_int_undef_store_int &("b") b).
   sep_apply_l_atomic (store_int_undef_store_int &("cmp") (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
   sep_apply_l_atomic (store_int_undef_store_int &("d") 1).
   sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
   rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
   unfold simplex_scan_rat_memory. rewrite EL, EU. simpl.
   rewrite (simplex_scan_rat_member_address S_separated_search "value" "num" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "value" "den" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
   sepcon_right_assoc. cancel.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   unfold simplex_scan_prefix. split; [|exact STEP].
   intros j HJ. destruct (Z.eq_dec j i); [subst; unfold simplex_scan_check; rewrite OBS; reflexivity|apply CHECK; lia].
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_8_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_8_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_8_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_8_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_8_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_8_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_8_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_8_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_8_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_8_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_8_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_8_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_8_separated_search : sx_find_violation_entail_wit_7_8_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 assert (EU : Z.eqb (Znth b HU_separated_search 0) 0 = true) by (apply Z.eqb_eq; assumption).
 assert (FL : simplex_rat_compare_flag (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b LN_separated_search 0) (Znth b LD_separated_search 0) = 1) by congruence.
 assert (OL : Z.ltb (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b LN_separated_search 0) (Znth b LD_separated_search 0)) 0 = true) by (apply Z.ltb_lt; assumption).
 assert (OBS : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some 1).
 { unfold simplex_scan_rows. match goal with H : b = Znth i BAS_separated_search 0 |- _ => rewrite <- H end.
 unfold simplex_scan_row. rewrite EL, EU, FL, OL. reflexivity. }
 match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
 unfold simplex_scan_prefix in H; destruct H as [CHECK CAND] end.
 assert (HBI : Znth i BAS_separated_search 0 < V_separated_search) by lia.
 pose proof (simplex_scan_candidate_step (fun j => Znth j BAS_separated_search 0)
 (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search)) V_separated_search i best R_2 D_2 ltac:(lia) HBI CAND) as STEP.
 assert (DIR : simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search) i = 1) by (unfold simplex_scan_direction; rewrite OBS; reflexivity).
 rewrite DIR in STEP. simpl in STEP.
 match goal with H : b = Znth i BAS_separated_search 0 |- _ => rewrite <- H in STEP end.
 assert (EB : Z.ltb b best = true) by (apply Z.ltb_lt; assumption).
 rewrite EB in STEP. simpl in STEP.
 Exists i 1.
 split_pure_spatial.
 - sep_apply_l_atomic (store_int_undef_store_int &("b") b).
   sep_apply_l_atomic (store_int_undef_store_int &("cmp") (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b LN_separated_search 0) (Znth b LD_separated_search 0))).
   sep_apply_l_atomic (store_int_undef_store_int &("d") 1).
   sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
   rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
   unfold simplex_scan_rat_memory. rewrite EL, EU. simpl.
   rewrite (simplex_scan_rat_member_address S_separated_search "value" "num" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "value" "den" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
   rewrite (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
   sepcon_right_assoc. cancel.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   unfold simplex_scan_prefix. split; [|exact STEP].
   intros j HJ. destruct (Z.eq_dec j i); [subst; unfold simplex_scan_check; rewrite OBS; reflexivity|apply CHECK; lia].
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_9_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_9_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_9_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_9_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_9_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_9_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_9_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_9_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_9_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_9_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_9_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_9_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_9_separated_search : sx_find_violation_entail_wit_7_9_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 assert (EU : Z.eqb (Znth b HU_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
 assert (HZ : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some 0).
 { unfold simplex_scan_rows.
   replace (Znth i BAS_separated_search 0) with b by assumption.
   unfold simplex_scan_row. rewrite EL, EU. simpl.
   repeat match goal with
   | |- context [Z.eqb ?x ?y] => let E := fresh "E" in destruct (Z.eqb x y) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; simpl
   | |- context [Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; simpl
   end; try reflexivity; lia. }
 assert (HP : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) best R_2 D_2).
 { eapply simplex_scan_prefix_zero_step__nonviolating_rows; eauto; lia. }
 Exists R_2 D_2.
 split_pure_spatial.
 - sep_apply_l_atomic (store_int_undef_store_int &("b") b).
   sep_apply_l_atomic (store_int_undef_store_int &("d") 0).
   sep_apply_l_atomic (store_int_undef_store_int &("cmp") (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b LN_separated_search 0) (Znth b LD_separated_search 0))).
   sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
   rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
   unfold simplex_scan_rat_memory. rewrite EL, EU. simpl.
   rewrite !simplex_scan_rat_member_address.
   cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
   cancel.

 - split_pures; dump_pre_spatial; auto; lia.
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_10_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_10_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_10_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_10_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_10_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_10_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_10_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_10_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_10_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_10_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_10_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_10_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_10_separated_search : sx_find_violation_entail_wit_7_10_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
 assert (EU : Z.eqb (Znth b HU_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
 assert (HZ : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some 0).
 { unfold simplex_scan_rows.
   replace (Znth i BAS_separated_search 0) with b by assumption.
   unfold simplex_scan_row. rewrite EL, EU. simpl.
   repeat match goal with
   | |- context [Z.eqb ?x ?y] => let E := fresh "E" in destruct (Z.eqb x y) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; simpl
   | |- context [Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; simpl
   end; try reflexivity; lia. }
 assert (HP : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) best R_2 D_2).
 { eapply simplex_scan_prefix_zero_step__nonviolating_rows; eauto; lia. }
 Exists R_2 D_2.
 split_pure_spatial.
 - sep_apply_l_atomic (store_int_undef_store_int &("b") b).
   sep_apply_l_atomic (store_int_undef_store_int &("d") 0).
   sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
   rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
   unfold simplex_scan_rat_memory. rewrite EL, EU. simpl.
   rewrite !simplex_scan_rat_member_address.
   cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
   cancel.

 - split_pures; dump_pre_spatial; auto; lia.
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_11_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_11_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_11_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_11_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_11_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_11_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_11_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_11_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_11_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_11_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_11_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_11_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_11_separated_search : sx_find_violation_entail_wit_7_11_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 assert (EU : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 assert (HZ : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some 0).
 { unfold simplex_scan_rows.
   replace (Znth i BAS_separated_search 0) with b by assumption.
   unfold simplex_scan_row. rewrite EL, EU. simpl.
   repeat match goal with
   | |- context [Z.eqb ?x ?y] => let E := fresh "E" in destruct (Z.eqb x y) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; simpl
   | |- context [Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; simpl
   end; try reflexivity; lia. }
 assert (HP : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) best R_2 D_2).
 { eapply simplex_scan_prefix_zero_step__nonviolating_rows; eauto; lia. }
 Exists R_2 D_2.
 split_pure_spatial.
 - sep_apply_l_atomic (store_int_undef_store_int &("b") b).
   sep_apply_l_atomic (store_int_undef_store_int &("d") 0).
   sep_apply_l_atomic (store_int_undef_store_int &("cmp") (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
   sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
   rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
   unfold simplex_scan_rat_memory. rewrite EL, EU. simpl.
   rewrite !simplex_scan_rat_member_address.
   cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
   cancel.

 - split_pures; dump_pre_spatial; auto; lia.
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_12_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_12_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_12_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_12_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_12_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_12_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_12_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_12_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_12_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_12_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_12_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_12_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_12_separated_search : sx_find_violation_entail_wit_7_12_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 assert (EU : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 assert (HZ : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some 0).
 { unfold simplex_scan_rows.
   replace (Znth i BAS_separated_search 0) with b by assumption.
   unfold simplex_scan_row. rewrite EL, EU. simpl.
   repeat match goal with
   | |- context [Z.eqb ?x ?y] => let E := fresh "E" in destruct (Z.eqb x y) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; simpl
   | |- context [Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; simpl
   end; try reflexivity; lia. }
 assert (HP : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) best R_2 D_2).
 { eapply simplex_scan_prefix_zero_step__nonviolating_rows; eauto; lia. }
 Exists R_2 D_2.
 split_pure_spatial.
 - sep_apply_l_atomic (store_int_undef_store_int &("b") b).
   sep_apply_l_atomic (store_int_undef_store_int &("d") 0).
   sep_apply_l_atomic (store_int_undef_store_int &("cmp") (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
   sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
   rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
   unfold simplex_scan_rat_memory. rewrite EL, EU. simpl.
   rewrite !simplex_scan_rat_member_address.
   cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
   cancel.

 - split_pures; dump_pre_spatial; auto; lia.
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_13_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_13_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_13_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_13_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_13_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_13_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_13_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_13_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_13_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_13_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_13_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_13_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_13_separated_search : sx_find_violation_entail_wit_7_13_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
 assert (EU : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 assert (HZ : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some 0).
 { unfold simplex_scan_rows.
   replace (Znth i BAS_separated_search 0) with b by assumption.
   unfold simplex_scan_row. rewrite EL, EU. simpl.
   repeat match goal with
   | |- context [Z.eqb ?x ?y] => let E := fresh "E" in destruct (Z.eqb x y) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; simpl
   | |- context [Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; simpl
   end; try reflexivity; lia. }
 assert (HP : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) best R_2 D_2).
 { eapply simplex_scan_prefix_zero_step__nonviolating_rows; eauto; lia. }
 Exists R_2 D_2.
 split_pure_spatial.
 - sep_apply_l_atomic (store_int_undef_store_int &("b") b).
   sep_apply_l_atomic (store_int_undef_store_int &("d") 0).
   sep_apply_l_atomic (store_int_undef_store_int &("cmp") (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
   sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
   rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
   unfold simplex_scan_rat_memory. rewrite EL, EU. simpl.
   rewrite !simplex_scan_rat_member_address.
   cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
   cancel.

 - split_pures; dump_pre_spatial; auto; lia.
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_14_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_14_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_14_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_14_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_14_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_14_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_14_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_14_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_14_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_14_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_14_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_14_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_14_separated_search : sx_find_violation_entail_wit_7_14_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hb : b = Znth i BAS_separated_search 0) by assumption.
  assert (EO : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some (-1)).
  { unfold simplex_scan_rows. rewrite <- Hb.
    apply simplex_scan_row_upper_override; try assumption; try congruence.
    first [left; assumption | right; congruence]. }
  assert (HN : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) best R_2 D_2).
  { match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct H as [HG HC] end.
    split.
    - intros j HJ. destruct (Z.eq_dec j i) as [->|Hne].
      + unfold simplex_scan_check. rewrite EO. reflexivity.
      + apply HG. lia.
    - pose proof (simplex_scan_candidate_step (fun j => Znth j BAS_separated_search 0)
        (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search))
        V_separated_search i best R_2 D_2 ltac:(lia) ltac:(change (Znth i BAS_separated_search 0 < V_separated_search); rewrite <- Hb; lia) HC) as HS.
      assert (HD : simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search) i = -1).
      { unfold simplex_scan_direction. rewrite EO. reflexivity. }
      rewrite HD in HS. simpl in HS.
      assert (EB : Z.ltb (Znth i BAS_separated_search 0) best = false)
        by (apply Z.ltb_ge; rewrite <- Hb; lia).
      rewrite EB in HS. exact HS. }
  Exists R_2 D_2.
  split_pure_spatial.
  - sepcon_right_assoc.
    sep_apply (store_int_undef_store_int &( "b" ) b).
    sep_apply (store_int_undef_store_int &( "cmp" )
      (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0)
       (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
    sep_apply (store_int_undef_store_int &( "d" ) (-1)).
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
    unfold simplex_scan_rat_memory.
    assert (EH : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; assumption).
    rewrite EH, EL. simpl.
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_15_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_15_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_15_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_15_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_15_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_15_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_15_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_15_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_15_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_15_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_15_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_15_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_15_separated_search : sx_find_violation_entail_wit_7_15_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hb : b = Znth i BAS_separated_search 0) by assumption.
  assert (EO : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some (-1)).
  { unfold simplex_scan_rows. rewrite <- Hb.
    apply simplex_scan_row_upper_override; try assumption; try congruence.
    first [left; assumption | right; congruence]. }
  assert (HN : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) best R_2 D_2).
  { match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct H as [HG HC] end.
    split.
    - intros j HJ. destruct (Z.eq_dec j i) as [->|Hne].
      + unfold simplex_scan_check. rewrite EO. reflexivity.
      + apply HG. lia.
    - pose proof (simplex_scan_candidate_step (fun j => Znth j BAS_separated_search 0)
        (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search))
        V_separated_search i best R_2 D_2 ltac:(lia) ltac:(change (Znth i BAS_separated_search 0 < V_separated_search); rewrite <- Hb; lia) HC) as HS.
      assert (HD : simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search) i = -1).
      { unfold simplex_scan_direction. rewrite EO. reflexivity. }
      rewrite HD in HS. simpl in HS.
      assert (EB : Z.ltb (Znth i BAS_separated_search 0) best = false)
        by (apply Z.ltb_ge; rewrite <- Hb; lia).
      rewrite EB in HS. exact HS. }
  Exists R_2 D_2.
  split_pure_spatial.
  - sepcon_right_assoc.
    sep_apply (store_int_undef_store_int &( "b" ) b).
    sep_apply (store_int_undef_store_int &( "cmp" )
      (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0)
       (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
    sep_apply (store_int_undef_store_int &( "d" ) (-1)).
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
    unfold simplex_scan_rat_memory.
    assert (EH : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    rewrite EH, EL. simpl.
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_16_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_16_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_16_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_16_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_16_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_16_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_16_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_16_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_16_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_16_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_16_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_16_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_16_separated_search : sx_find_violation_entail_wit_7_16_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hb : b = Znth i BAS_separated_search 0) by assumption.
  assert (EO : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some (-1)).
  { unfold simplex_scan_rows. rewrite <- Hb.
    apply simplex_scan_row_upper_override; try assumption; try congruence.
    first [left; assumption | right; congruence]. }
  assert (HN : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) best R_2 D_2).
  { match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct H as [HG HC] end.
    split.
    - intros j HJ. destruct (Z.eq_dec j i) as [->|Hne].
      + unfold simplex_scan_check. rewrite EO. reflexivity.
      + apply HG. lia.
    - pose proof (simplex_scan_candidate_step (fun j => Znth j BAS_separated_search 0)
        (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search))
        V_separated_search i best R_2 D_2 ltac:(lia) ltac:(change (Znth i BAS_separated_search 0 < V_separated_search); rewrite <- Hb; lia) HC) as HS.
      assert (HD : simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search) i = -1).
      { unfold simplex_scan_direction. rewrite EO. reflexivity. }
      rewrite HD in HS. simpl in HS.
      assert (EB : Z.ltb (Znth i BAS_separated_search 0) best = false)
        by (apply Z.ltb_ge; rewrite <- Hb; lia).
      rewrite EB in HS. exact HS. }
  Exists R_2 D_2.
  split_pure_spatial.
  - sepcon_right_assoc.
    sep_apply (store_int_undef_store_int &( "b" ) b).
    sep_apply (store_int_undef_store_int &( "cmp" )
      (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0)
       (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
    sep_apply (store_int_undef_store_int &( "d" ) (-1)).
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
    unfold simplex_scan_rat_memory.
    assert (EH : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    rewrite EH, EL. simpl.
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_17_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_17_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_17_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_17_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_17_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_17_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_17_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_17_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_17_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_17_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_17_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_17_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_17_separated_search : sx_find_violation_entail_wit_7_17_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hb : b = Znth i BAS_separated_search 0) by assumption.
  assert (EO : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some (-1)).
  { unfold simplex_scan_rows. rewrite <- Hb.
    apply simplex_scan_row_upper_override; try assumption; try congruence.
    first [left; assumption | right; congruence]. }
  assert (HN : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) best R_2 D_2).
  { match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct H as [HG HC] end.
    split.
    - intros j HJ. destruct (Z.eq_dec j i) as [->|Hne].
      + unfold simplex_scan_check. rewrite EO. reflexivity.
      + apply HG. lia.
    - pose proof (simplex_scan_candidate_step (fun j => Znth j BAS_separated_search 0)
        (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search))
        V_separated_search i best R_2 D_2 ltac:(lia) ltac:(change (Znth i BAS_separated_search 0 < V_separated_search); rewrite <- Hb; lia) HC) as HS.
      assert (HD : simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search) i = -1).
      { unfold simplex_scan_direction. rewrite EO. reflexivity. }
      rewrite HD in HS. simpl in HS.
      assert (EB : Z.ltb (Znth i BAS_separated_search 0) best = false)
        by (apply Z.ltb_ge; rewrite <- Hb; lia).
      rewrite EB in HS. exact HS. }
  Exists R_2 D_2.
  split_pure_spatial.
  - sepcon_right_assoc.
    sep_apply (store_int_undef_store_int &( "b" ) b).
    sep_apply (store_int_undef_store_int &( "cmp" )
      (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0)
       (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
    sep_apply (store_int_undef_store_int &( "d" ) (-1)).
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
    unfold simplex_scan_rat_memory.
    assert (EH : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    rewrite EH, EL. simpl.
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_18_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_18_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_18_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_18_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_18_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_18_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_18_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_18_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_18_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_18_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_18_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_18_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_18_separated_search : sx_find_violation_entail_wit_7_18_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hb : b = Znth i BAS_separated_search 0) by assumption.
  assert (EO : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some (-1)).
  { unfold simplex_scan_rows. rewrite <- Hb.
    apply simplex_scan_row_upper_override; try assumption; try congruence.
    first [left; assumption | right; congruence]. }
  assert (HN : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) best R_2 D_2).
  { match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct H as [HG HC] end.
    split.
    - intros j HJ. destruct (Z.eq_dec j i) as [->|Hne].
      + unfold simplex_scan_check. rewrite EO. reflexivity.
      + apply HG. lia.
    - pose proof (simplex_scan_candidate_step (fun j => Znth j BAS_separated_search 0)
        (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search))
        V_separated_search i best R_2 D_2 ltac:(lia) ltac:(change (Znth i BAS_separated_search 0 < V_separated_search); rewrite <- Hb; lia) HC) as HS.
      assert (HD : simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search) i = -1).
      { unfold simplex_scan_direction. rewrite EO. reflexivity. }
      rewrite HD in HS. simpl in HS.
      assert (EB : Z.ltb (Znth i BAS_separated_search 0) best = false)
        by (apply Z.ltb_ge; rewrite <- Hb; lia).
      rewrite EB in HS. exact HS. }
  Exists R_2 D_2.
  split_pure_spatial.
  - sepcon_right_assoc.
    sep_apply (store_int_undef_store_int &( "b" ) b).
    sep_apply (store_int_undef_store_int &( "cmp" )
      (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0)
       (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
    sep_apply (store_int_undef_store_int &( "d" ) (-1)).
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
    unfold simplex_scan_rat_memory.
    assert (EH : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    rewrite EH, EL. simpl.
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_19_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_19_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_19_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_19_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_19_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_19_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_19_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_19_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_19_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_19_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_19_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_19_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_19_separated_search : sx_find_violation_entail_wit_7_19_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
  assert (EU : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
  assert (ELO : Z.ltb (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0)
      (Znth b LN_separated_search 0) (Znth b LD_separated_search 0)) 0 = true) by (apply Z.ltb_lt; auto).
  assert (EUO : Z.ltb 0 (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0)) = false) by (apply Z.ltb_ge; auto).
  assert (Hrow : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some 1).
  { unfold simplex_scan_rows, simplex_scan_row.
    rewrite <- PreH14. rewrite <- PreH8, PreH9, <- PreH4, PreH5.
    rewrite EL, EU, ELO , EUO. reflexivity. }
  assert (HP : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) best R_2 D_2).
  { destruct PreH26 as [HC HK].
    split.
    - intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
      + unfold simplex_scan_check. rewrite Hrow. reflexivity.
      + apply HC. lia.
    - pose proof (simplex_scan_candidate_step (fun j => Znth j BAS_separated_search 0)
        (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search))
        V_separated_search i best R_2 D_2 ltac:(lia) ltac:(cbn beta; rewrite <- PreH14; lia) HK) as Hstep.
      assert (EB : Z.ltb (Znth i BAS_separated_search 0) best = false)
        by (apply Z.ltb_ge; rewrite <- PreH14; lia).
      cbn beta in Hstep. rewrite EB, Bool.andb_false_r in Hstep. exact Hstep. }
  Exists R_2 D_2.
  split_pure_spatial.
  - sep_apply_l_atomic (store_int_undef_store_int (&("b")) b).
    sep_apply_l_atomic (store_int_undef_store_int (&("cmp"))  (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
    sep_apply_l_atomic (store_int_undef_store_int (&("d")) 1).
    cancel (&(S_separated_search # "SxState" ->ₛ "rows") # Int |-> M_separated_search).
    cancel (&(S_separated_search # "SxState" ->ₛ "vars") # Int |-> V_separated_search).
    cancel (IntArray.full &(S_separated_search # "SxState" ->ₛ "basic") M_separated_search BAS_separated_search).
    cancel (simplex_scan_unused_memory S_separated_search M_separated_search).
    cancel (P_separated_search # Int |-> R_2).
    cancel (Q_separated_search # Int |-> D_2).
    cancel (&("b") # Int |->_).
    cancel (&("cmp") # Int |->_).
    cancel (&("d") # Int |->_).
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b PreH15).
    unfold simplex_scan_rat_memory.
    rewrite EL, EU. simpl.
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_20_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_20_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_20_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_20_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_20_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_20_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_20_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_20_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_20_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_20_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_20_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_20_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_20_separated_search : sx_find_violation_entail_wit_7_20_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
  assert (EU : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
  assert (ELO : Z.ltb (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0)
      (Znth b LN_separated_search 0) (Znth b LD_separated_search 0)) 0 = true) by (apply Z.ltb_lt; auto).
  assert (EUO : Z.ltb 0 (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0)) = false) by (apply Z.ltb_ge; auto).
  assert (Hrow : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some 1).
  { unfold simplex_scan_rows, simplex_scan_row.
    rewrite <- PreH14. rewrite <- PreH8, PreH9, <- PreH4, PreH5.
    rewrite EL, EU, ELO , EUO. reflexivity. }
  assert (HP : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) best R_2 D_2).
  { destruct PreH26 as [HC HK].
    split.
    - intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
      + unfold simplex_scan_check. rewrite Hrow. reflexivity.
      + apply HC. lia.
    - pose proof (simplex_scan_candidate_step (fun j => Znth j BAS_separated_search 0)
        (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search))
        V_separated_search i best R_2 D_2 ltac:(lia) ltac:(cbn beta; rewrite <- PreH14; lia) HK) as Hstep.
      assert (EB : Z.ltb (Znth i BAS_separated_search 0) best = false)
        by (apply Z.ltb_ge; rewrite <- PreH14; lia).
      cbn beta in Hstep. rewrite EB, Bool.andb_false_r in Hstep. exact Hstep. }
  Exists R_2 D_2.
  split_pure_spatial.
  - sep_apply_l_atomic (store_int_undef_store_int (&("b")) b).
    sep_apply_l_atomic (store_int_undef_store_int (&("cmp"))  (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b UN_separated_search 0) (Znth b UD_separated_search 0))).
    sep_apply_l_atomic (store_int_undef_store_int (&("d")) 1).
    cancel (&(S_separated_search # "SxState" ->ₛ "rows") # Int |-> M_separated_search).
    cancel (&(S_separated_search # "SxState" ->ₛ "vars") # Int |-> V_separated_search).
    cancel (IntArray.full &(S_separated_search # "SxState" ->ₛ "basic") M_separated_search BAS_separated_search).
    cancel (simplex_scan_unused_memory S_separated_search M_separated_search).
    cancel (P_separated_search # Int |-> R_2).
    cancel (Q_separated_search # Int |-> D_2).
    cancel (&("b") # Int |->_).
    cancel (&("cmp") # Int |->_).
    cancel (&("d") # Int |->_).
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b PreH15).
    unfold simplex_scan_rat_memory.
    rewrite EL, EU. simpl.
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed. 

Lemma proof_of_sx_find_violation_entail_wit_7_21_separated_search_split_goal_1 : sx_find_violation_entail_wit_7_21_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_21_separated_search_split_goal_2 : sx_find_violation_entail_wit_7_21_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_21_separated_search_split_goal_3 : sx_find_violation_entail_wit_7_21_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_21_separated_search_split_goal_4 : sx_find_violation_entail_wit_7_21_separated_search_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_21_separated_search_split_goal_5 : sx_find_violation_entail_wit_7_21_separated_search_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_21_separated_search_split_goal_spatial : sx_find_violation_entail_wit_7_21_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_entail_wit_7_21_separated_search : sx_find_violation_entail_wit_7_21_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
  assert (EU : Z.eqb (Znth b HU_separated_search 0) 0 = true) by (apply Z.eqb_eq; auto).
  assert (ELO : Z.ltb (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0)
      (Znth b LN_separated_search 0) (Znth b LD_separated_search 0)) 0 = true) by (apply Z.ltb_lt; auto).
  
  assert (Hrow : simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search i = Some 1).
  { unfold simplex_scan_rows, simplex_scan_row.
    rewrite <- PreH10. rewrite <- PreH4, PreH5.
    rewrite EL, EU, ELO . reflexivity. }
  assert (HP : simplex_scan_prefix BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search V_separated_search (i+1) best R_2 D_2).
  { destruct PreH22 as [HC HK].
    split.
    - intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
      + unfold simplex_scan_check. rewrite Hrow. reflexivity.
      + apply HC. lia.
    - pose proof (simplex_scan_candidate_step (fun j => Znth j BAS_separated_search 0)
        (simplex_scan_direction (simplex_scan_rows BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search))
        V_separated_search i best R_2 D_2 ltac:(lia) ltac:(cbn beta; rewrite <- PreH10; lia) HK) as Hstep.
      assert (EB : Z.ltb (Znth i BAS_separated_search 0) best = false)
        by (apply Z.ltb_ge; rewrite <- PreH10; lia).
      cbn beta in Hstep. rewrite EB, Bool.andb_false_r in Hstep. exact Hstep. }
  Exists R_2 D_2.
  split_pure_spatial.
  - sep_apply_l_atomic (store_int_undef_store_int (&("b")) b).
    sep_apply_l_atomic (store_int_undef_store_int (&("cmp"))  (simplex_rat_compare_order (Znth b VN_separated_search 0) (Znth b VD_separated_search 0) (Znth b LN_separated_search 0) (Znth b LD_separated_search 0))).
    sep_apply_l_atomic (store_int_undef_store_int (&("d")) 1).
    cancel (&(S_separated_search # "SxState" ->ₛ "rows") # Int |-> M_separated_search).
    cancel (&(S_separated_search # "SxState" ->ₛ "vars") # Int |-> V_separated_search).
    cancel (IntArray.full &(S_separated_search # "SxState" ->ₛ "basic") M_separated_search BAS_separated_search).
    cancel (simplex_scan_unused_memory S_separated_search M_separated_search).
    cancel (P_separated_search # Int |-> R_2).
    cancel (Q_separated_search # Int |-> D_2).
    cancel (&("b") # Int |->_).
    cancel (&("cmp") # Int |->_).
    cancel (&("d") # Int |->_).
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b PreH11).
    unfold simplex_scan_rat_memory.
    rewrite EL, EU. simpl.
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
    rewrite (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed. 

Lemma proof_of_sx_find_violation_return_wit_1_separated_search_split_goal_1 : sx_find_violation_return_wit_1_separated_search_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = M_separated_search) by lia. subst i.
  unfold simplex_find_violation_spec.
  unfold simplex_scan_prefix in *.
  eapply simplex_scan_finish_success with (best := best); tauto.
Qed.

Lemma proof_of_sx_find_violation_return_wit_1_separated_search : sx_find_violation_return_wit_1_separated_search.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_find_violation_return_wit_1_separated_search_split_goal_1.
Qed. 

Lemma proof_of_sx_find_violation_return_wit_2_separated_search_split_goal_1 : sx_find_violation_return_wit_2_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_2_separated_search_split_goal_spatial : sx_find_violation_return_wit_2_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_2_separated_search : sx_find_violation_return_wit_2_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists R_2 D_2.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
    assert (EHU : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EHL : Z.eqb (Znth b HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
    rewrite EHU, EHL. simpl.
    unfold simplex_scan_rat_memory.
    rewrite <- (simplex_scan_rat_member_address S_separated_search "value" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "value" "den" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
    sepcon_assoc_change.
    cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
    cancel.
  - dump_pre_spatial.
    unfold simplex_find_violation_spec.
    match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct H as [Hchecks Hcandidate] end.
    eapply simplex_scan_finish_failure with (k:=i) (best:=best); try lia; try eassumption.
    unfold simplex_scan_check, simplex_scan_rows.
    match goal with H : b = Znth i BAS_separated_search 0 |- _ => rewrite <- H end.
    rewrite simplex_scan_row_upper_failure; [reflexivity|assumption|lia].
Qed. 

Lemma proof_of_sx_find_violation_return_wit_3_separated_search_split_goal_1 : sx_find_violation_return_wit_3_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_3_separated_search_split_goal_spatial : sx_find_violation_return_wit_3_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_3_separated_search : sx_find_violation_return_wit_3_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists R_2 D_2.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
    assert (EHU : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EHL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    rewrite EHU, EHL. simpl.
    unfold simplex_scan_rat_memory.
    rewrite <- (simplex_scan_rat_member_address S_separated_search "value" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "value" "den" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
    sepcon_assoc_change.
    cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
    cancel.
  - dump_pre_spatial.
    unfold simplex_find_violation_spec.
    match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct H as [Hchecks Hcandidate] end.
    eapply simplex_scan_finish_failure with (k:=i) (best:=best); try lia; try eassumption.
    unfold simplex_scan_check, simplex_scan_rows.
    match goal with H : b = Znth i BAS_separated_search 0 |- _ => rewrite <- H end.
    rewrite simplex_scan_row_upper_failure; [reflexivity|assumption|lia].
Qed. 

Lemma proof_of_sx_find_violation_return_wit_4_separated_search_split_goal_1 : sx_find_violation_return_wit_4_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_4_separated_search_split_goal_spatial : sx_find_violation_return_wit_4_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_4_separated_search : sx_find_violation_return_wit_4_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists R_2 D_2.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
    assert (EHU : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EHL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    rewrite EHU, EHL. simpl.
    unfold simplex_scan_rat_memory.
    rewrite <- (simplex_scan_rat_member_address S_separated_search "value" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "value" "den" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
    sepcon_assoc_change.
    cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
    cancel.
  - dump_pre_spatial.
    unfold simplex_find_violation_spec.
    match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct H as [Hchecks Hcandidate] end.
    eapply simplex_scan_finish_failure with (k:=i) (best:=best); try lia; try eassumption.
    unfold simplex_scan_check, simplex_scan_rows.
    match goal with H : b = Znth i BAS_separated_search 0 |- _ => rewrite <- H end.
    rewrite simplex_scan_row_upper_failure; [reflexivity|assumption|lia].
Qed. 

Lemma proof_of_sx_find_violation_return_wit_5_separated_search_split_goal_1 : sx_find_violation_return_wit_5_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_5_separated_search_split_goal_spatial : sx_find_violation_return_wit_5_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_5_separated_search : sx_find_violation_return_wit_5_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists R_2 D_2.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
    assert (EHU : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EHL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    rewrite EHU, EHL. simpl.
    unfold simplex_scan_rat_memory.
    rewrite <- (simplex_scan_rat_member_address S_separated_search "value" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "value" "den" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
    sepcon_assoc_change.
    cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
    cancel.
  - dump_pre_spatial.
    unfold simplex_find_violation_spec.
    match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct H as [Hchecks Hcandidate] end.
    eapply simplex_scan_finish_failure with (k:=i) (best:=best); try lia; try eassumption.
    unfold simplex_scan_check, simplex_scan_rows.
    match goal with H : b = Znth i BAS_separated_search 0 |- _ => rewrite <- H end.
    rewrite simplex_scan_row_upper_failure; [reflexivity|assumption|lia].
Qed. 

Lemma proof_of_sx_find_violation_return_wit_6_separated_search_split_goal_1 : sx_find_violation_return_wit_6_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_6_separated_search_split_goal_spatial : sx_find_violation_return_wit_6_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_6_separated_search : sx_find_violation_return_wit_6_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists R_2 D_2.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(assumption)).
    assert (EHU : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EHL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    rewrite EHU, EHL. simpl.
    unfold simplex_scan_rat_memory.
    rewrite <- (simplex_scan_rat_member_address S_separated_search "value" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "value" "den" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "upper" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "lower" "num" b).
    rewrite <- (simplex_scan_rat_member_address S_separated_search "lower" "den" b).
    sepcon_assoc_change.
    cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
    cancel.
  - dump_pre_spatial.
    unfold simplex_find_violation_spec.
    match goal with H : simplex_scan_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct H as [Hchecks Hcandidate] end.
    eapply simplex_scan_finish_failure with (k:=i) (best:=best); try lia; try eassumption.
    unfold simplex_scan_check, simplex_scan_rows.
    match goal with H : b = Znth i BAS_separated_search 0 |- _ => rewrite <- H end.
    rewrite simplex_scan_row_upper_failure; [reflexivity|assumption|lia].
Qed. 

Lemma proof_of_sx_find_violation_return_wit_7_separated_search_split_goal_1 : sx_find_violation_return_wit_7_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_7_separated_search_split_goal_spatial : sx_find_violation_return_wit_7_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_7_separated_search : sx_find_violation_return_wit_7_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists R_2 D_2.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b PreH9).
    unfold simplex_scan_rat_memory.
    assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
    assert (EU : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
    rewrite EL, EU. simpl negb. simpl orb.
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "num" b),
      (simplex_scan_rat_member_address S_separated_search "value" "den" b),
      (simplex_scan_rat_member_address S_separated_search "lower" "num" b),
      (simplex_scan_rat_member_address S_separated_search "lower" "den" b),
      (simplex_scan_rat_member_address S_separated_search "upper" "num" b),
      (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    sepcon_assoc_change.
    cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
    cancel.
  - dump_pre_spatial.
    unfold simplex_find_violation_spec.
    unfold simplex_scan_prefix in PreH20.
    eapply simplex_scan_finish_failure with (k := i) (best := best).
    + lia.
    + unfold simplex_scan_check, simplex_scan_rows.
      rewrite <- PreH8.
      rewrite (simplex_scan_row_lower_failure
        (Znth b HL_separated_search 0) (Znth b HU_separated_search 0)
        (Znth b VN_separated_search 0) (Znth b VD_separated_search 0)
        (Znth b LN_separated_search 0) (Znth b LD_separated_search 0)
        (Znth b UN_separated_search 0) (Znth b UD_separated_search 0)
        PreH24 ltac:(lia)).
      reflexivity.
    + tauto.
    + tauto.
Qed. 

Lemma proof_of_sx_find_violation_return_wit_8_separated_search_split_goal_1 : sx_find_violation_return_wit_8_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_8_separated_search_split_goal_spatial : sx_find_violation_return_wit_8_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_8_separated_search : sx_find_violation_return_wit_8_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists R_2 D_2.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b PreH9).
    unfold simplex_scan_rat_memory.
    assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
    assert (EU : Z.eqb (Znth b HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
    rewrite EL, EU. simpl negb. simpl orb.
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "num" b),
      (simplex_scan_rat_member_address S_separated_search "value" "den" b),
      (simplex_scan_rat_member_address S_separated_search "lower" "num" b),
      (simplex_scan_rat_member_address S_separated_search "lower" "den" b),
      (simplex_scan_rat_member_address S_separated_search "upper" "num" b),
      (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    sepcon_assoc_change.
    cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
    cancel.
  - dump_pre_spatial.
    unfold simplex_find_violation_spec.
    unfold simplex_scan_prefix in PreH20.
    eapply simplex_scan_finish_failure with (k := i) (best := best).
    + lia.
    + unfold simplex_scan_check, simplex_scan_rows.
      rewrite <- PreH8.
      rewrite (simplex_scan_row_lower_failure
        (Znth b HL_separated_search 0) (Znth b HU_separated_search 0)
        (Znth b VN_separated_search 0) (Znth b VD_separated_search 0)
        (Znth b LN_separated_search 0) (Znth b LD_separated_search 0)
        (Znth b UN_separated_search 0) (Znth b UD_separated_search 0)
        PreH24 ltac:(lia)).
      reflexivity.
    + tauto.
    + tauto.
Qed. 

Lemma proof_of_sx_find_violation_return_wit_9_separated_search_split_goal_1 : sx_find_violation_return_wit_9_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_9_separated_search_split_goal_spatial : sx_find_violation_return_wit_9_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_violation_return_wit_9_separated_search : sx_find_violation_return_wit_9_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists R_2 D_2.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_scan_slots_merge S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b ltac:(lia)).
    rewrite (simplex_scan_slot_active S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b PreH9).
    unfold simplex_scan_rat_memory.
    assert (EL : Z.eqb (Znth b HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
    assert (EU : Z.eqb (Znth b HU_separated_search 0) 0 = true) by (apply Z.eqb_eq; tauto).
    rewrite EL, EU. simpl negb. simpl orb.
    rewrite (simplex_scan_rat_member_address S_separated_search "value" "num" b),
      (simplex_scan_rat_member_address S_separated_search "value" "den" b),
      (simplex_scan_rat_member_address S_separated_search "lower" "num" b),
      (simplex_scan_rat_member_address S_separated_search "lower" "den" b),
      (simplex_scan_rat_member_address S_separated_search "upper" "num" b),
      (simplex_scan_rat_member_address S_separated_search "upper" "den" b).
    sepcon_assoc_change.
    cancel (simplex_scan_slots_except S_separated_search BAS_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search b).
    cancel.
  - dump_pre_spatial.
    unfold simplex_find_violation_spec.
    unfold simplex_scan_prefix in PreH20.
    eapply simplex_scan_finish_failure with (k := i) (best := best).
    + lia.
    + unfold simplex_scan_check, simplex_scan_rows.
      rewrite <- PreH8.
      rewrite (simplex_scan_row_lower_failure
        (Znth b HL_separated_search 0) (Znth b HU_separated_search 0)
        (Znth b VN_separated_search 0) (Znth b VD_separated_search 0)
        (Znth b LN_separated_search 0) (Znth b LD_separated_search 0)
        (Znth b UN_separated_search 0) (Znth b UD_separated_search 0)
        PreH24 ltac:(lia)).
      reflexivity.
    + tauto.
    + tauto.
Qed. 

Lemma proof_of_sx_find_violation_partial_solve_wit_2_separated_search_pure_split_goal_1 : sx_find_violation_partial_solve_wit_2_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH46 b ltac:(auto)) as Hden.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_2_separated_search_pure_split_goal_2 : sx_find_violation_partial_solve_wit_2_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH47 b ltac:(auto)) as Hden.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_2_separated_search_pure : sx_find_violation_partial_solve_wit_2_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_2_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_2_separated_search_pure_split_goal_2.
Qed. 

Lemma proof_of_sx_find_violation_partial_solve_wit_3_separated_search_pure_split_goal_1 : sx_find_violation_partial_solve_wit_3_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH46 b ltac:(auto)) as Hden.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_3_separated_search_pure_split_goal_2 : sx_find_violation_partial_solve_wit_3_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH47 b ltac:(auto)) as Hden.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_3_separated_search_pure : sx_find_violation_partial_solve_wit_3_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_3_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_3_separated_search_pure_split_goal_2.
Qed. 

Lemma proof_of_sx_find_violation_partial_solve_wit_4_separated_search_pure_split_goal_1 : sx_find_violation_partial_solve_wit_4_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH42 b ltac:(auto)) as Hden.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_4_separated_search_pure_split_goal_2 : sx_find_violation_partial_solve_wit_4_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (PreH43 b ltac:(auto)) as Hden.
  tauto.
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_4_separated_search_pure : sx_find_violation_partial_solve_wit_4_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_4_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_4_separated_search_pure_split_goal_2.
Qed. 

Lemma proof_of_sx_find_violation_partial_solve_wit_5_separated_search_pure_split_goal_1 : sx_find_violation_partial_solve_wit_5_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH42 b (conj PreH34 (or_intror PreH50))) as Hdomain.
  dump_pre_spatial.
  exact (proj2 (proj1 Hdomain)).
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_5_separated_search_pure_split_goal_2 : sx_find_violation_partial_solve_wit_5_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH44 b (conj PreH34 PreH50)) as Hdomain.
  dump_pre_spatial.
  exact (proj2 (proj1 Hdomain)).
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_5_separated_search_pure : sx_find_violation_partial_solve_wit_5_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_5_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_5_separated_search_pure_split_goal_2.
Qed. 

Lemma proof_of_sx_find_violation_partial_solve_wit_6_separated_search_pure_split_goal_1 : sx_find_violation_partial_solve_wit_6_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH52 b (conj PreH44 (or_intror PreH60))) as Hdomain.
  dump_pre_spatial.
  exact (proj2 (proj1 Hdomain)).
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_6_separated_search_pure_split_goal_2 : sx_find_violation_partial_solve_wit_6_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH54 b (conj PreH44 PreH60)) as Hdomain.
  dump_pre_spatial.
  exact (proj2 (proj1 Hdomain)).
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_6_separated_search_pure : sx_find_violation_partial_solve_wit_6_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_6_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_6_separated_search_pure_split_goal_2.
Qed. 

Lemma proof_of_sx_find_violation_partial_solve_wit_7_separated_search_pure_split_goal_1 : sx_find_violation_partial_solve_wit_7_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH52 b (conj PreH44 (or_intror PreH60))) as Hdomain.
  dump_pre_spatial.
  exact (proj2 (proj1 Hdomain)).
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_7_separated_search_pure_split_goal_2 : sx_find_violation_partial_solve_wit_7_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH54 b (conj PreH44 PreH60)) as Hdomain.
  dump_pre_spatial.
  exact (proj2 (proj1 Hdomain)).
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_7_separated_search_pure : sx_find_violation_partial_solve_wit_7_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_7_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_7_separated_search_pure_split_goal_2.
Qed. 

Lemma proof_of_sx_find_violation_partial_solve_wit_8_separated_search_pure_split_goal_1 : sx_find_violation_partial_solve_wit_8_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH52 b (conj PreH44 (or_intror PreH60))) as Hdomain.
  dump_pre_spatial.
  exact (proj2 (proj1 Hdomain)).
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_8_separated_search_pure_split_goal_2 : sx_find_violation_partial_solve_wit_8_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH54 b (conj PreH44 PreH60)) as Hdomain.
  dump_pre_spatial.
  exact (proj2 (proj1 Hdomain)).
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_8_separated_search_pure : sx_find_violation_partial_solve_wit_8_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_8_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_8_separated_search_pure_split_goal_2.
Qed. 

Lemma proof_of_sx_find_violation_partial_solve_wit_9_separated_search_pure_split_goal_1 : sx_find_violation_partial_solve_wit_9_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH52 b (conj PreH44 (or_intror PreH60))) as Hdomain.
  dump_pre_spatial.
  exact (proj2 (proj1 Hdomain)).
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_9_separated_search_pure_split_goal_2 : sx_find_violation_partial_solve_wit_9_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH54 b (conj PreH44 PreH60)) as Hdomain.
  dump_pre_spatial.
  exact (proj2 (proj1 Hdomain)).
Qed.

Lemma proof_of_sx_find_violation_partial_solve_wit_9_separated_search_pure : sx_find_violation_partial_solve_wit_9_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_9_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_violation_partial_solve_wit_9_separated_search_pure_split_goal_2.
Qed. 

