From SimpleC.SL Require Export Mem SeparationLogic.
From AUXLib Require Export ListLib.
From SumLib Require Export ZRange.
From Coq Require Import ZArith List String.
From SimpleC.EE.Applications_human.simplex_find_violation_retry Require Export simplex_find_violation_retry_lib.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string_scope.

(* Same conditional read footprint as the established search: a slot contributes
   only fields actually inspected. Every absent field is emp, so a caller can
   frame its prior known value; old undef predicates remain unchanged. *)
Definition simplex_scan_read_slot (s : Z)
    (basic hl hu vn vd ln ld un ud : list Z) (j : Z) : Assertion :=
  let active := existsb (Z.eqb j) basic in
  let low := (active && negb (Z.eqb (Znth j hl 0) 0))%bool in
  let high := (active && negb (Z.eqb (Znth j hu 0) 0))%bool in
  (if active then
    (&(s # "SxState" ->ₛ "has_lower") + j * sizeof(INT)) # Int |-> Znth j hl 0 **
    (&(s # "SxState" ->ₛ "has_upper") + j * sizeof(INT)) # Int |-> Znth j hu 0
   else emp) **
  (if (low || high)%bool then simplex_scan_rat_memory s "value" j true (Znth j vn 0) (Znth j vd 0) else emp) **
  (if low then simplex_scan_rat_memory s "lower" j true (Znth j ln 0) (Znth j ld 0) else emp) **
  (if high then simplex_scan_rat_memory s "upper" j true (Znth j un 0) (Znth j ud 0) else emp).

(* Enumerates physical variable slots, not the possibly repeated basis list. *)
Definition simplex_scan_read_memory (s : Z)
    (basic hl hu vn vd ln ld un ud : list Z) : Assertion :=
  iter_sepcon (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24)).

(* Temporary cut after selecting one basic index; standard remove_Znth/iter_sepcon. *)
Definition simplex_scan_read_except (s : Z)
    (basic hl hu vn vd ln ld un ud : list Z) (j : Z) : Assertion :=
  iter_sepcon (remove_Znth j (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24))).


From Coq Require Import Lia.
Lemma read_slot_nth__read_focus : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  Znth j (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24)) emp =
  simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j.
Proof.
 intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity.
Qed.
Lemma read_slot_focus__read_focus : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  simplex_scan_read_memory s basic hl hu vn vd ln ld un ud |--
  simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j **
  simplex_scan_read_except s basic hl hu vn vd ln ld un ud j.
Proof.
 intros. unfold simplex_scan_read_memory, simplex_scan_read_except.
 pose proof (iter_sepcon_split_remove_Znth j
    (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24)) emp) as HS.
 rewrite read_slot_nth__read_focus in HS by auto. apply HS.
 rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma nth_member__read_focus : forall (l:list Z) i,
  0 <= i < Zlength l -> In (Znth i l 0) l.
Proof. intros l i H. unfold Znth. apply nth_In. rewrite Zlength_correct in H. lia. Qed.
Lemma prefix_initial__init_finish : forall (b hl hu vn vd ln ld un ud : list Z) v,
 simplex_scan_prefix b hl hu vn vd ln ld un ud v 0 v (-1) 0.
Proof.
 intros. unfold simplex_scan_prefix. split.
 - intros j Hj. lia.
 - apply simplex_scan_candidate_empty.
Qed.
Lemma prefix_finish__init_finish : forall (b hl hu vn vd ln ld un ud : list Z) v m best row direction,
 simplex_scan_prefix b hl hu vn vd ln ld un ud v m best row direction ->
 simplex_find_violation_spec b hl hu vn vd ln ld un ud v m 1 row direction.
Proof.
 intros b hl hu vn vd ln ld un ud v m best row direction H.
 unfold simplex_scan_prefix in H. destruct H as [HC HW].
 unfold simplex_find_violation_spec. eapply simplex_scan_finish_success; eauto.
Qed.
Lemma read_slot_map_nth__upper_update : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  Znth j (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24)) emp =
  simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j.
Proof.
  intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
  rewrite simplex_scan_range_nth by lia. reflexivity.
Qed.
Lemma read_slot_merge__upper_update : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j **
  simplex_scan_read_except s basic hl hu vn vd ln ld un ud j |--
  simplex_scan_read_memory s basic hl hu vn vd ln ld un ud.
Proof.
  intros. unfold simplex_scan_read_memory, simplex_scan_read_except.
  pose proof (iter_sepcon_merge_remove_Znth j
    (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24))
    (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j)) as HM.
  rewrite <- (read_slot_map_nth__upper_update s basic hl hu vn vd ln ld un ud j H) in HM.
  rewrite replace_Znth_Znth in HM.
  rewrite read_slot_map_nth__upper_update in HM by auto. apply HM.
  rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma row_prefix_step__upper_update : forall basic hl hu vn vd ln ld un ud vars k best row direction,
  0 <= k -> Znth k basic 0 < vars -> Znth k basic 0 < best ->
  simplex_scan_prefix basic hl hu vn vd ln ld un ud vars k best row direction ->
  simplex_scan_rows basic hl hu vn vd ln ld un ud k = Some (-1) ->
  simplex_scan_prefix basic hl hu vn vd ln ld un ud vars (k+1) (Znth k basic 0) k (-1).
Proof.
  intros basic hl hu vn vd ln ld un ud vars k best row direction HK HB HBest [HP HC] HO.
  unfold simplex_scan_prefix. split.
  - intros j HJ. destruct (Z.eq_dec j k) as [->|HN].
    + unfold simplex_scan_check. rewrite HO. reflexivity.
    + apply HP. lia.
  - pose proof (simplex_scan_candidate_step (fun i => Znth i basic 0)
      (simplex_scan_direction (simplex_scan_rows basic hl hu vn vd ln ld un ud))
      vars k best row direction HK HB HC) as HS.
    assert (HD : simplex_scan_direction (simplex_scan_rows basic hl hu vn vd ln ld un ud) k = -1).
    { unfold simplex_scan_direction. rewrite HO. reflexivity. }
    rewrite HD in HS. simpl in HS.
    assert (EB : Z.ltb (Znth k basic 0) best = true) by (apply Z.ltb_lt; auto).
    rewrite EB in HS. exact HS.
Qed.
Lemma read_slot_nth__lower_update : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  Znth j (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24)) emp =
  simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j.
Proof.
  intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
  rewrite simplex_scan_range_nth by lia. reflexivity.
Qed.
Lemma read_slot_merge__lower_update : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j **
  simplex_scan_read_except s basic hl hu vn vd ln ld un ud j |--
  simplex_scan_read_memory s basic hl hu vn vd ln ld un ud.
Proof.
  intros. unfold simplex_scan_read_memory, simplex_scan_read_except.
  pose proof (iter_sepcon_merge_remove_Znth j
    (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24))
    (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j)) as HM.
  rewrite <- (read_slot_nth__lower_update s basic hl hu vn vd ln ld un ud j H) in HM.
  rewrite replace_Znth_Znth in HM.
  rewrite read_slot_nth__lower_update in HM by auto. apply HM.
  rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma row_prefix_step__lower_update : forall basic hl hu vn vd ln ld un ud vars k best row direction,
  0 <= k -> Znth k basic 0 < vars -> Znth k basic 0 < best ->
  simplex_scan_rows basic hl hu vn vd ln ld un ud k = Some 1 ->
  simplex_scan_prefix basic hl hu vn vd ln ld un ud vars k best row direction ->
  simplex_scan_prefix basic hl hu vn vd ln ld un ud vars (k+1) (Znth k basic 0) k 1.
Proof.
 intros basic hl hu vn vd ln ld un ud vars k best row direction HK HB HBetter HE [HC HW].
 split.
 - intros j HJ. destruct (Z.eq_dec j k) as [->|HN].
   + unfold simplex_scan_check. rewrite HE. reflexivity.
   + apply HC. lia.
 - pose proof (simplex_scan_candidate_step (fun j => Znth j basic 0)
     (simplex_scan_direction (simplex_scan_rows basic hl hu vn vd ln ld un ud))
     vars k best row direction HK HB HW) as HS.
   assert (ED : simplex_scan_direction (simplex_scan_rows basic hl hu vn vd ln ld un ud) k = 1).
   { unfold simplex_scan_direction. rewrite HE. reflexivity. }
   rewrite ED in HS. simpl in HS.
   rewrite (proj2 (Z.ltb_lt _ _) HBetter) in HS. exact HS.
Qed.
Lemma row_lower__lower_update : forall hl hu vn vd ln ld un ud,
  hl <> 0 -> simplex_rat_compare_flag vn vd ln ld = 1 ->
  simplex_rat_compare_order vn vd ln ld < 0 ->
  (hu = 0 \/ (simplex_rat_compare_flag vn vd un ud = 1 /\ simplex_rat_compare_order vn vd un ud <= 0)) ->
  simplex_scan_row hl hu vn vd ln ld un ud = Some 1.
Proof.
 intros hl hu vn vd ln ld un ud HL FL OL HU.
 unfold simplex_scan_row.
 assert (EL : Z.eqb hl 0 = false) by (apply Z.eqb_neq; auto).
 assert (EO : Z.ltb (simplex_rat_compare_order vn vd ln ld) 0 = true) by (apply Z.ltb_lt; auto).
 rewrite EL, FL, EO. simpl.
 destruct HU as [->|[FU OU]]; [reflexivity|].
 rewrite FU, Bool.orb_true_r. simpl.
 rewrite (proj2 (Z.ltb_ge _ _) OU), Bool.andb_false_r. reflexivity.
Qed.
Lemma read_slot_merge__no_violation : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j **
  simplex_scan_read_except s basic hl hu vn vd ln ld un ud j |--
  simplex_scan_read_memory s basic hl hu vn vd ln ld un ud.
Proof.
 intros. unfold simplex_scan_read_memory, simplex_scan_read_except.
 assert (HN : Znth j (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24)) emp =
   simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j).
 { rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
   rewrite simplex_scan_range_nth by lia. reflexivity. }
 pose proof (iter_sepcon_merge_remove_Znth j
   (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24))
   (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j)) as HM.
 rewrite <- HN in HM. rewrite replace_Znth_Znth in HM.
 rewrite HN in HM. apply HM. rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma row_prefix_step__no_violation : forall basic hl hu vn vd ln ld un ud vars k best row direction,
  0 <= k -> Znth k basic 0 < vars ->
  simplex_scan_rows basic hl hu vn vd ln ld un ud k = Some 0 ->
  simplex_scan_prefix basic hl hu vn vd ln ld un ud vars k best row direction ->
  simplex_scan_prefix basic hl hu vn vd ln ld un ud vars (k+1) best row direction.
Proof. exact simplex_scan_prefix_zero_step__nonviolating_rows. Qed.
Lemma read_slot_merge__keep_best_upper : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j **
  simplex_scan_read_except s basic hl hu vn vd ln ld un ud j |--
  simplex_scan_read_memory s basic hl hu vn vd ln ld un ud.
Proof.
  intros. unfold simplex_scan_read_memory, simplex_scan_read_except.
  assert (HN : Znth j (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24)) emp = simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j).
  { rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
    rewrite simplex_scan_range_nth by lia. reflexivity. }
  pose proof (iter_sepcon_merge_remove_Znth j
    (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24))
    (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j)) as HM.
  rewrite <- HN in HM. rewrite replace_Znth_Znth in HM.
  rewrite HN in HM. apply HM.
  rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma row_prefix_step__keep_best_upper : forall basic hl hu vn vd ln ld un ud vars k best row direction,
  0 <= k -> Znth k basic 0 < vars -> best <= Znth k basic 0 ->
  simplex_scan_rows basic hl hu vn vd ln ld un ud k = Some (-1) ->
  simplex_scan_prefix basic hl hu vn vd ln ld un ud vars k best row direction ->
  simplex_scan_prefix basic hl hu vn vd ln ld un ud vars (k+1) best row direction.
Proof.
 intros basic hl hu vn vd ln ld un ud vars k best row direction HK HB HKeep HE [HC HW].
 split.
 - intros j HJ. destruct (Z.eq_dec j k) as [->|HN].
   + unfold simplex_scan_check. rewrite HE. reflexivity.
   + apply HC. lia.
 - pose proof (simplex_scan_candidate_step (fun j => Znth j basic 0)
     (simplex_scan_direction (simplex_scan_rows basic hl hu vn vd ln ld un ud))
     vars k best row direction HK HB HW) as HS.
   assert (HD : simplex_scan_direction (simplex_scan_rows basic hl hu vn vd ln ld un ud) k = -1).
   { unfold simplex_scan_direction. rewrite HE. reflexivity. }
   rewrite HD in HS.
   assert (EK : Z.ltb (Znth k basic 0) best = false) by (apply Z.ltb_ge; lia).
   rewrite EK in HS. simpl in HS. exact HS.
Qed.
Lemma row_prefix_step__keep_best_lower : forall basic hl hu vn vd ln ld un ud vars k best row direction d,
  0 <= k -> Znth k basic 0 < vars -> best <= Znth k basic 0 ->
  simplex_scan_rows basic hl hu vn vd ln ld un ud k = Some d ->
  simplex_scan_prefix basic hl hu vn vd ln ld un ud vars k best row direction ->
  simplex_scan_prefix basic hl hu vn vd ln ld un ud vars (k+1) best row direction.
Proof.
 intros basic hl hu vn vd ln ld un ud vars k best row direction d HK HB Hkeep HE [HC HW].
 split.
 - intros j HJ. destruct (Z.eq_dec j k) as [->|HN].
   + unfold simplex_scan_check. rewrite HE. reflexivity.
   + apply HC. lia.
 - pose proof (simplex_scan_candidate_step (fun j => Znth j basic 0)
     (simplex_scan_direction (simplex_scan_rows basic hl hu vn vd ln ld un ud))
     vars k best row direction HK HB HW) as HS.
   assert (EB : Z.ltb (Znth k basic 0) best = false) by (apply Z.ltb_ge; lia).
   cbn beta in HS. rewrite EB, Bool.andb_false_r in HS. exact HS.
Qed.
Lemma read_slot_merge__keep_best_lower : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j **
  simplex_scan_read_except s basic hl hu vn vd ln ld un ud j |--
  simplex_scan_read_memory s basic hl hu vn vd ln ld un ud.
Proof.
 intros. unfold simplex_scan_read_memory, simplex_scan_read_except.
 assert (EN : Znth j (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24)) emp = simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j).
 { rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
   rewrite simplex_scan_range_nth by lia. reflexivity. }
 pose proof (iter_sepcon_merge_remove_Znth j
    (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24))
    (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j)) as HM.
 rewrite <- EN in HM. rewrite replace_Znth_Znth in HM.
 rewrite EN in HM. apply HM.
 rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma prefix_failure__upper_failure : forall basic hl hu vn vd ln ld un ud vars rows i best row dir,
  simplex_scan_prefix basic hl hu vn vd ln ld un ud vars i best row dir ->
  0 <= i < rows -> simplex_scan_rows basic hl hu vn vd ln ld un ud i = None ->
  simplex_find_violation_spec basic hl hu vn vd ln ld un ud vars rows 0 row dir.
Proof.
 intros basic hl hu vn vd ln ld un ud vars rows i best row dir [HP HC] HI HF.
 unfold simplex_find_violation_spec.
 eapply simplex_scan_finish_failure with (k:=i) (best:=best); eauto.
 unfold simplex_scan_check. rewrite HF. reflexivity.
Qed.
Lemma read_slot_nth__upper_failure : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  Znth j (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24)) emp =
  simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j.
Proof.
 intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity.
Qed.
Lemma read_slot_merge__upper_failure : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j **
  simplex_scan_read_except s basic hl hu vn vd ln ld un ud j |--
  simplex_scan_read_memory s basic hl hu vn vd ln ld un ud.
Proof.
 intros. unfold simplex_scan_read_memory, simplex_scan_read_except.
 pose proof (iter_sepcon_merge_remove_Znth j
 (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24))
 (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j)) as HM.
 rewrite <- (read_slot_nth__upper_failure s basic hl hu vn vd ln ld un ud j H) in HM.
 rewrite replace_Znth_Znth in HM.
 rewrite read_slot_nth__upper_failure in HM by auto. apply HM.
 rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma prefix_failure__lower_failure : forall basic hl hu vn vd ln ld un ud vars rows i best row direction,
  0 <= i < rows ->
  simplex_scan_prefix basic hl hu vn vd ln ld un ud vars i best row direction ->
  simplex_scan_rows basic hl hu vn vd ln ld un ud i = None ->
  simplex_find_violation_spec basic hl hu vn vd ln ld un ud vars rows 0 row direction.
Proof.
  intros basic hl hu vn vd ln ld un ud vars rows i best row direction HI [HP HC] HF.
  unfold simplex_find_violation_spec. eapply simplex_scan_finish_failure; eauto.
  unfold simplex_scan_check. rewrite HF. reflexivity.
Qed.
Lemma read_slot_merge__lower_failure : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j **
  simplex_scan_read_except s basic hl hu vn vd ln ld un ud j |--
  simplex_scan_read_memory s basic hl hu vn vd ln ld un ud.
Proof.
  intros. unfold simplex_scan_read_memory, simplex_scan_read_except.
  assert (HN : Znth j (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24)) emp = simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j).
  { rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
    rewrite simplex_scan_range_nth by lia. reflexivity. }
  pose proof (iter_sepcon_merge_remove_Znth j
    (map (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud) (Zrange 0 24))
    (simplex_scan_read_slot s basic hl hu vn vd ln ld un ud j)) as HM.
  rewrite <- HN in HM. rewrite replace_Znth_Znth in HM. rewrite HN in HM.
  apply HM. rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
