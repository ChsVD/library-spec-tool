From SimpleC.SL Require Export Mem SeparationLogic.
From AUXLib Require Export ListLib.
From SumLib Require Export ZRange.
From Coq Require Import ZArith List Lia.
From SimpleC.EE.Applications_human.simplex_find_entering Require Export simplex_find_entering_lib.
From SimpleC.EE.Applications_human.simplex_find_violation_preserve Require Export simplex_find_violation_preserve_lib.
From Coq Require Import String.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string_scope.

(* The selected row's active numerator cells, using the exact native 24-rational
   row stride. No denominator, other row, or inactive cell is owned. In particular
   vars=0 has emp for every row value, including an out-of-range machine int.
   This is a transparent composition of established field stores and iter_sepcon,
   not a new foundational spatial model. *)
Definition simplex_enter_num_cell (s row : Z) (cn : list Z) (j : Z) : Assertion :=
  eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const ((&(s # "SxState" ->ₛ "a") + row * (sizeof("SxRat") * 24)) + j * sizeof("SxRat")) (FET_alias "SxRat")) "num")) # Int |-> Znth j cn 0.
Definition simplex_enter_num_memory (s row vars : Z) (cn : list Z) : Assertion :=
  iter_sepcon (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)).
(* Standard remove_Znth remainder used to expose one read cell. *)
Definition simplex_enter_num_except (s row vars : Z) (cn : list Z) (j : Z) : Assertion :=
  iter_sepcon (remove_Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars))).

(* A concrete compiled consumer of the previously proved pure computation
   interface: the preserving contract retains precisely its original result. *)
Theorem simplex_enter_preserve_compute_iff : forall ib cn hl hu vn vd ln ld un ud d v q e,
  0 <= v ->
  (simplex_find_entering_spec ib cn hl hu vn vd ln ld un ud d v q e <->
   simplex_enter_compute (simplex_enter_observations ib cn hl hu vn vd ln ld un ud d) v = (q,e)).
Proof. intros. apply simplex_enter_compute_iff; auto. Qed.


Lemma num_focus__entry_focus : forall s row vars cn j,
  0 <= j < vars ->
  simplex_enter_num_memory s row vars cn |--
  simplex_enter_num_cell s row cn j ** simplex_enter_num_except s row vars cn j.
Proof.
 intros s row vars cn j H.
 unfold simplex_enter_num_memory, simplex_enter_num_except.
 pose proof (iter_sepcon_split_remove_Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) emp) as HS.
 rewrite (Znth_map _ _ _ 0 emp) in HS by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth in HS by lia.

 apply HS. rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma num_nth__upper_skip : forall s row vars cn j,
  0 <= j < vars ->
  Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) emp = simplex_enter_num_cell s row cn j.
Proof.
 intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity.
Qed.
Lemma num_restore__upper_skip : forall s row vars cn j,
  0 <= j < vars ->
  simplex_enter_num_cell s row cn j ** simplex_enter_num_except s row vars cn j |-- simplex_enter_num_memory s row vars cn.
Proof.
 intros. unfold simplex_enter_num_memory, simplex_enter_num_except.
 pose proof (iter_sepcon_merge_remove_Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) (simplex_enter_num_cell s row cn j)) as HM.
 rewrite <- (num_nth__upper_skip s row vars cn j H) in HM.
 rewrite replace_Znth_Znth in HM. rewrite num_nth__upper_skip in HM by auto.
 apply HM. rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma active__upper_skip : forall j v, 0 <= j < v -> existsb (Z.eqb j) (Zrange 0 v) = true.
Proof.
 intros. apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl].
Qed.
Lemma num_nth__upper_candidate : forall s row vars cn j,
  0 <= j < vars ->
  Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) emp = simplex_enter_num_cell s row cn j.
Proof.
 intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity.
Qed.
Lemma num_restore__upper_candidate : forall s row vars cn j,
  0 <= j < vars ->
  simplex_enter_num_cell s row cn j ** simplex_enter_num_except s row vars cn j |-- simplex_enter_num_memory s row vars cn.
Proof.
 intros. unfold simplex_enter_num_memory, simplex_enter_num_except.
 pose proof (iter_sepcon_merge_remove_Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) (simplex_enter_num_cell s row cn j)) as HM.
 rewrite <- (num_nth__upper_candidate s row vars cn j H) in HM.
 rewrite replace_Znth_Znth in HM. rewrite num_nth__upper_candidate in HM by auto.
 apply HM. rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma active__upper_candidate : forall j v, 0 <= j < v -> existsb (Z.eqb j) (Zrange 0 v) = true.
Proof.
 intros. apply existsb_exists. exists j. split.
 - replace j with (Znth j (Zrange 0 v) 0) at 1 by (rewrite simplex_scan_range_nth by lia; lia).
   apply nth_member__read_focus. rewrite simplex_scan_range_length; lia.
 - apply Z.eqb_refl.
Qed.
Lemma range_len_aux__lower_skip : forall n lo,
 Zlength (Zrange_aux lo n) = Z.of_nat n.
Proof. induction n; intros; simpl; [reflexivity|rewrite Zlength_cons, IHn; lia]. Qed.
Lemma range_len__lower_skip : forall v, 0<=v -> Zlength (Zrange 0 v)=v.
Proof. intros. unfold Zrange. rewrite range_len_aux__lower_skip, Z.sub_0_r, Z2Nat.id by lia. reflexivity. Qed.
Lemma range_nth_aux__lower_skip : forall n lo i, 0<=i<Z.of_nat n ->
 Znth i (Zrange_aux lo n) 0 = lo+i.
Proof.
 induction n; intros lo i H; [lia|].
 simpl. destruct (Z.eq_dec i 0); [subst; change (lo = lo+0); lia|].
 rewrite Znth_cons by lia. rewrite IHn by lia. lia.
Qed.
Lemma range_nth__lower_skip : forall v j, 0<=j<v -> Znth j (Zrange 0 v) 0=j.
Proof. intros. unfold Zrange. rewrite range_nth_aux__lower_skip by (rewrite Z.sub_0_r, Z2Nat.id by lia; lia). lia. Qed.
Lemma num_restore__lower_skip : forall s row vars cn j, 0<=j<vars ->
 simplex_enter_num_cell s row cn j ** simplex_enter_num_except s row vars cn j |--
 simplex_enter_num_memory s row vars cn.
Proof.
 intros. unfold simplex_enter_num_memory, simplex_enter_num_except.
 assert (HN : Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) emp = simplex_enter_num_cell s row cn j).
 { rewrite (Znth_map _ _ _ 0 emp) by (rewrite range_len__lower_skip; lia).
   rewrite range_nth__lower_skip by lia. reflexivity. }
 pose proof (iter_sepcon_merge_remove_Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) (simplex_enter_num_cell s row cn j)) as HM.
 rewrite <- HN in HM. rewrite replace_Znth_Znth in HM. rewrite HN in HM.
 apply HM. rewrite Zlength_map, range_len__lower_skip; lia.
Qed.
Lemma num_restore__lower_candidate : forall s row vars cn j,
  0 <= j < vars ->
  simplex_enter_num_cell s row cn j ** simplex_enter_num_except s row vars cn j |--
  simplex_enter_num_memory s row vars cn.
Proof.
  intros s row vars cn j H.
  unfold simplex_enter_num_except, simplex_enter_num_memory.
  pose proof (iter_sepcon_merge_remove_Znth j
    (map (simplex_enter_num_cell s row cn) (Zrange 0 vars))
    (Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) emp)) as HM.
  rewrite replace_Znth_Znth in HM.
  rewrite (Znth_map _ _ _ 0 emp) in HM by (rewrite simplex_scan_range_length; lia).
  rewrite simplex_scan_range_nth in HM by lia. apply HM.
  rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma num_nth__basic_skip : forall s row vars cn j,
  0 <= j < vars ->
  Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) emp = simplex_enter_num_cell s row cn j.
Proof.
 intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length by lia; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity.
Qed.
Lemma num_restore__basic_skip : forall s row vars cn j,
  0 <= j < vars ->
  simplex_enter_num_cell s row cn j ** simplex_enter_num_except s row vars cn j |-- simplex_enter_num_memory s row vars cn.
Proof.
 intros. unfold simplex_enter_num_except, simplex_enter_num_memory.
 pose proof (iter_sepcon_merge_remove_Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) (simplex_enter_num_cell s row cn j)) as HM.
 rewrite <- (num_nth__basic_skip s row vars cn j H) in HM.
 rewrite replace_Znth_Znth in HM.
 rewrite num_nth__basic_skip in HM by auto. apply HM.
 rewrite Zlength_map, simplex_scan_range_length by lia. lia.
Qed.
Lemma active__basic_skip : forall j v, 0 <= j < v -> existsb (Z.eqb j) (Zrange 0 v) = true.
Proof.
 intros. apply existsb_exists. exists j. split.
 - rewrite <- (simplex_scan_range_nth v ltac:(lia) j H) at 1.
   apply nth_member__read_focus. rewrite simplex_scan_range_length by lia. lia.
 - apply Z.eqb_refl.
Qed.
Lemma num_restore__zero_coeff_skip : forall s row vars cn j,
  0 <= j < vars ->
  simplex_enter_num_cell s row cn j ** simplex_enter_num_except s row vars cn j |--
  simplex_enter_num_memory s row vars cn.
Proof.
 intros s row vars cn j H.
 unfold simplex_enter_num_memory, simplex_enter_num_except.
 assert (HN: Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) emp =
   simplex_enter_num_cell s row cn j).
 { rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length by lia; lia).
   rewrite simplex_scan_range_nth by lia. reflexivity. }
 pose proof (iter_sepcon_merge_remove_Znth j
   (map (simplex_enter_num_cell s row cn) (Zrange 0 vars))
   (simplex_enter_num_cell s row cn j)) as HM.
 rewrite <- HN in HM. rewrite replace_Znth_Znth in HM.
 rewrite HN in HM. apply HM. rewrite Zlength_map, simplex_scan_range_length by lia. lia.
Qed.
Lemma range_active__zero_coeff_skip : forall j v, 0 <= j < v ->
 existsb (Z.eqb j) (Zrange 0 v) = true.
Proof.
 intros j v H. apply existsb_exists. exists j. split.
 - rewrite <- (simplex_scan_range_nth v ltac:(lia) j H) at 1.
   apply nth_member__read_focus. rewrite simplex_scan_range_length by lia. exact H.
 - apply Z.eqb_refl.
Qed.
Lemma basic_restore__zero_coeff_skip : forall x j v ib,
 0 <= j < v ->
 (x + j * sizeof(INT)) # Int |-> Znth j ib 0 **
 IntArray.missing_i x j 0 v ib |-- IntArray.full x v ib.
Proof.
 intros x j v ib H.
 pose proof (IntArray.missing_i_merge_to_full x j v (Znth j ib 0) ib H) as HM.
 rewrite replace_Znth_Znth in HM. exact HM.
Qed.
Lemma num_restore__upper_rejection : forall s row vars cn j,
  0 <= j < vars ->
  simplex_enter_num_cell s row cn j ** simplex_enter_num_except s row vars cn j |--
  simplex_enter_num_memory s row vars cn.
Proof.
  intros s row vars cn j HJ.
  unfold simplex_enter_num_memory, simplex_enter_num_except.
  pose proof (iter_sepcon_merge_remove_Znth j
    (map (simplex_enter_num_cell s row cn) (Zrange 0 vars))
    (Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) emp)) as HM.
  rewrite replace_Znth_Znth in HM.
  rewrite (Znth_map _ _ _ 0 emp) in HM by (rewrite simplex_scan_range_length; lia).
  rewrite simplex_scan_range_nth in HM by lia.
  apply HM. rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma active__upper_rejection : forall j v, 0 <= j < v ->
  existsb (Z.eqb j) (Zrange 0 v) = true.
Proof.
 intros j v H. apply existsb_exists. exists j.
 split; [apply In_Zrange; lia | apply Z.eqb_refl].
Qed.
Lemma num_nth__lower_rejection : forall s row vars cn j,
  0<=j<vars ->
  Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) emp = simplex_enter_num_cell s row cn j.
Proof.
 intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity.
Qed.
Lemma num_restore__lower_rejection : forall s row vars cn j,
  0<=j<vars -> simplex_enter_num_cell s row cn j ** simplex_enter_num_except s row vars cn j |-- simplex_enter_num_memory s row vars cn.
Proof.
 intros. unfold simplex_enter_num_except, simplex_enter_num_memory.
 pose proof (iter_sepcon_merge_remove_Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) (simplex_enter_num_cell s row cn j)) as HM.
 rewrite <- (num_nth__lower_rejection s row vars cn j H) in HM.
 rewrite replace_Znth_Znth in HM.
 rewrite num_nth__lower_rejection in HM by auto. apply HM.
 rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma num_nth__exit_and_empty_slot : forall s row vars cn j,
  0 <= j < vars ->
  Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) emp = simplex_enter_num_cell s row cn j.
Proof.
  intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length by lia; lia).
  rewrite simplex_scan_range_nth by lia. reflexivity.
Qed.
Lemma num_restore__exit_and_empty_slot : forall s row vars cn j,
  0 <= j < vars ->
  simplex_enter_num_cell s row cn j ** simplex_enter_num_except s row vars cn j |-- simplex_enter_num_memory s row vars cn.
Proof.
  intros. unfold simplex_enter_num_except, simplex_enter_num_memory.
  pose proof (iter_sepcon_merge_remove_Znth j
    (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) (simplex_enter_num_cell s row cn j)) as HM.
  rewrite <- (num_nth__exit_and_empty_slot s row vars cn j H) in HM.
  rewrite replace_Znth_Znth in HM.
  rewrite num_nth__exit_and_empty_slot in HM by auto. apply HM.
  rewrite Zlength_map, simplex_scan_range_length by lia. lia.
Qed.
Lemma num_restore__unbounded_one_side : forall s row vars cn j,
  0 <= j < vars ->
  simplex_enter_num_cell s row cn j ** simplex_enter_num_except s row vars cn j |-- simplex_enter_num_memory s row vars cn.
Proof.
 intros s row vars cn j HJ.
 unfold simplex_enter_num_except, simplex_enter_num_memory.
 assert (HE: Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) emp = simplex_enter_num_cell s row cn j).
 { rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length;lia).
   rewrite simplex_scan_range_nth by lia. reflexivity. }
 pose proof (iter_sepcon_merge_remove_Znth j (map (simplex_enter_num_cell s row cn) (Zrange 0 vars)) (simplex_enter_num_cell s row cn j)) as HM.
 rewrite <- HE in HM. rewrite replace_Znth_Znth in HM. rewrite HE in HM.
 apply HM. rewrite Zlength_map, simplex_scan_range_length;lia.
Qed.
Lemma active_range__unbounded_one_side : forall j v,
 0 <= j < v -> existsb (Z.eqb j) (Zrange 0 v) = true.
Proof. intros j v H. apply existsb_exists. exists j. split.
 apply In_Zrange;lia. apply Z.eqb_refl.
Qed.
