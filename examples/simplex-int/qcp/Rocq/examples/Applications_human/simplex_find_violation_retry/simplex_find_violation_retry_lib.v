From Coq Require Import ZArith List Lia.
From AUXLib Require Export ListLib.
From MaxMinLib Require Export MaxMin.
From SumLib Require Export ZRange.
From SimpleC.EE.Applications_human.simplex_rat_compare
  Require Export simplex_rat_compare_lib.
Import ListNotations.
Local Open Scope Z_scope.

(* Reference audit 2026-11-02: FME algorithm.v's integer LP_sol,
   satisfy_LP, eliminate_xn and FME_step_sound do not model checked rational
   scans. implement_lemma.v eliminate_xn_step_{re,lo,up} classify constraint
   lists but supply neither first arithmetic failure nor stable minimum.
   We reuse the already-proved rational checked-comparison interface, and
   MaxMinLib for minima. No FME theorem is falsely cast as a scan theorem.
   Bounds/ownership/initialization belong to the C contract, not this model. *)

(* One row: lower is checked first, upper second. Nonzero flags enable
   bounds. Failed rows return None and cannot commit even a lower candidate. *)
Definition simplex_scan_row (hl hu vn vd ln ld un ud : Z) : option Z :=
  if (Z.eqb hl 0 || Z.eqb (simplex_rat_compare_flag vn vd ln ld) 1)%bool
  then if (Z.eqb hu 0 || Z.eqb (simplex_rat_compare_flag vn vd un ud) 1)%bool
       then Some (if (negb (Z.eqb hu 0) &&
                     Z.ltb 0 (simplex_rat_compare_order vn vd un ud))%bool
                  then -1
                  else if (negb (Z.eqb hl 0) &&
                           Z.ltb (simplex_rat_compare_order vn vd ln ld) 0)%bool
                       then 1 else 0)
       else None
  else None.

Lemma simplex_scan_row_disabled : forall vn vd ln ld un ud,
  simplex_scan_row 0 0 vn vd ln ld un ud = Some 0.
Proof. reflexivity. Qed.

Lemma simplex_scan_row_lower_failure : forall hl hu vn vd ln ld un ud,
  hl <> 0 -> simplex_rat_compare_flag vn vd ln ld = 0 ->
  simplex_scan_row hl hu vn vd ln ld un ud = None.
Proof.
  intros. unfold simplex_scan_row. rewrite H0.
  destruct (Z.eqb hl 0) eqn:E; [apply Z.eqb_eq in E; contradiction|reflexivity].
Qed.

Lemma simplex_scan_row_upper_failure : forall hl hu vn vd ln ld un ud,
  hu <> 0 -> simplex_rat_compare_flag vn vd un ud = 0 ->
  simplex_scan_row hl hu vn vd ln ld un ud = None.
Proof.
  intros. unfold simplex_scan_row. rewrite H0.
  destruct (Z.eqb hu 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
  destruct (_ || _)%bool; reflexivity.
Qed.

Lemma simplex_scan_row_upper_override : forall hl hu vn vd ln ld un ud,
  hu <> 0 -> simplex_rat_compare_flag vn vd un ud = 1 ->
  (hl = 0 \/ simplex_rat_compare_flag vn vd ln ld = 1) ->
  simplex_rat_compare_order vn vd un ud > 0 ->
  simplex_scan_row hl hu vn vd ln ld un ud = Some (-1).
Proof.
  intros hl hu vn vd ln ld un ud Hu HF HL HO.
  unfold simplex_scan_row. rewrite HF.
  assert (EH : Z.eqb hu 0 = false) by (apply Z.eqb_neq; auto).
  assert (EO : Z.ltb 0 (simplex_rat_compare_order vn vd un ud) = true)
    by (apply Z.ltb_lt; lia).
  rewrite EH, EO. simpl.
  destruct HL as [->|HL]; [reflexivity|rewrite HL; rewrite Bool.orb_true_r; reflexivity].
Qed.

(* Mathematical prefix winner. The first minimum selects the least basic
   index; the second selects the earliest physical row among equal indices.
   Empty prefixes and empty violating sets retain the exact sentinel. *)
Definition simplex_scan_candidate (basic dir : Z -> Z)
    (vars k best row direction : Z) : Prop :=
  (row = -1 /\ direction = 0 /\ best = vars /\
  forall j, 0 <= j < k -> dir j = 0) \/
  (0 <= row < k /\ dir row <> 0 /\ direction = dir row /\ best = basic row /\
  min_value_of_subset Z.le (fun j => 0 <= j < k /\ dir j <> 0) basic best /\
  min_value_of_subset Z.le
     (fun j => 0 <= j < k /\ dir j <> 0 /\ basic j = best)
     (fun j => j) row).

Lemma simplex_scan_candidate_empty : forall basic dir vars,
  simplex_scan_candidate basic dir vars 0 vars (-1) 0.
Proof. intros. left. repeat split; auto; intros; lia. Qed.

(* Consumer form of the two MaxMinLib statements. This is a bridge lemma,
   not a second definition of minimum. *)
Lemma simplex_scan_candidate_facts : forall basic dir vars k best row direction,
  simplex_scan_candidate basic dir vars k best row direction ->
  (row = -1 /\ direction = 0 /\ best = vars /\
  forall j, 0 <= j < k -> dir j = 0) \/
  (0 <= row < k /\ dir row <> 0 /\ direction = dir row /\ best = basic row /\
  (forall j, 0 <= j < k -> dir j <> 0 -> best <= basic j) /\
  (forall j, 0 <= j < k -> dir j <> 0 -> basic j = best -> row <= j)).
Proof.
  intros basic dir vars k best row direction [H|H]; [auto|right].
  destruct H as [HR [HD [HV [HB [[x [[HX HM] HE]] [y [[HY HN] HF]]]]]]].
  repeat split; try tauto.
  - intros j HJ HDj. rewrite <- HE. apply HM. change (0 <= j < k /\ dir j <> 0). auto.
  - intros j HJ HDj HBj. rewrite <- HF. apply HN. change (0 <= j < k /\ dir j <> 0 /\ basic j = best). auto.
Qed.

Lemma simplex_scan_candidate_intro : forall basic dir vars k best row direction,
  0 <= row < k -> dir row <> 0 -> direction = dir row -> best = basic row ->
  (forall j, 0 <= j < k -> dir j <> 0 -> best <= basic j) ->
  (forall j, 0 <= j < k -> dir j <> 0 -> basic j = best -> row <= j) ->
  simplex_scan_candidate basic dir vars k best row direction.
Proof.
  intros basic dir vars k best row direction HR HD HV HB HM HE.
  assert (M : min_value_of_subset Z.le
    (fun j => 0 <= j < k /\ dir j <> 0) basic best).
  { exists row. split.
    - split; [exact (conj HR HD)|]. intros j [HJ HDj]. rewrite <- HB. apply HM; auto.
    - symmetry. exact HB. }
  assert (E : min_value_of_subset Z.le
    (fun j => 0 <= j < k /\ dir j <> 0 /\ basic j = best) (fun j => j) row).
  { exists row. split.
    - split; [repeat split; try tauto; congruence|]. intros j [HJ [HDj HBj]]. apply HE; auto.
    - reflexivity. }
  right. tauto.
Qed.

Lemma simplex_scan_candidate_unique : forall basic dir vars k b r d b' r' d',
  simplex_scan_candidate basic dir vars k b r d ->
  simplex_scan_candidate basic dir vars k b' r' d' ->
  b=b' /\ r=r' /\ d=d'.
Proof.
  intros. apply simplex_scan_candidate_facts in H.
  apply simplex_scan_candidate_facts in H0.
  destruct H as [[? [? [? HZ]]]|[HR [HD [HV [HB [HM HE]]]]]];
  destruct H0 as [[? [? [? HZ']]]|[HR' [HD' [HV' [HB' [HM' HE']]]]]];
  try (repeat split; congruence).
  - specialize (HZ r' HR'). contradiction.
  - specialize (HZ' r HR). contradiction.
  - assert (b=b') by (specialize (HM r' HR' HD'); specialize (HM' r HR HD); lia).
    assert (r=r') by (specialize (HE r' HR' HD'); specialize (HE' r HR HD); lia).
    subst. auto.
Qed.

(* Exact result, including first checked failure and the winner of only the
   completed prefix. No successful-comparison restriction is an input. *)
Definition simplex_find_violation_result (basic check dir : Z -> Z)
    (vars rows ret row direction : Z) : Prop :=
  (ret = 1 /\ (forall j, 0 <= j < rows -> check j = 1) /\
  exists best, simplex_scan_candidate basic dir vars rows best row direction) \/
  (ret = 0 /\ exists k best,
    0 <= k < rows /\ check k = 0 /\
  (forall j, 0 <= j < k -> check j = 1) /\
  simplex_scan_candidate basic dir vars k best row direction).

Lemma simplex_scan_finish_success : forall basic check dir vars rows best row direction,
  (forall j, 0 <= j < rows -> check j = 1) ->
  simplex_scan_candidate basic dir vars rows best row direction ->
  simplex_find_violation_result basic check dir vars rows 1 row direction.
Proof. intros. left. repeat split; auto. eauto. Qed.

Lemma simplex_scan_finish_failure : forall basic check dir vars rows k best row direction,
  0 <= k < rows -> check k = 0 ->
  (forall j, 0 <= j < k -> check j = 1) ->
  simplex_scan_candidate basic dir vars k best row direction ->
  simplex_find_violation_result basic check dir vars rows 0 row direction.
Proof. intros. right. split; auto. exists k, best. auto. Qed.

Lemma simplex_find_violation_result_unique : forall basic check dir vars rows q r d q' r' d',
  simplex_find_violation_result basic check dir vars rows q r d ->
  simplex_find_violation_result basic check dir vars rows q' r' d' ->
  q=q' /\ r=r' /\ d=d'.
Proof.
  intros basic check dir vars rows q r d q' r' d' H H'.
  destruct H as [[-> [HG [b HC]]]|[-> [k [b [HK [HF [HG HC]]]]]]];
  destruct H' as [[-> [HG' [b' HC']]]|[-> [k' [b' [HK' [HF' [HG' HC']]]]]]].
  - pose proof (simplex_scan_candidate_unique _ _ _ _ _ _ _ _ _ _ HC HC'); tauto.
  - specialize (HG k' HK'). congruence.
  - specialize (HG' k HK). congruence.
  - assert (k=k').
    { destruct (Z.lt_trichotomy k k') as [HL|[HE|HR]]; auto.
      - specialize (HG' k ltac:(lia)). congruence.
      - specialize (HG k' ltac:(lia)). congruence. }
    subst. pose proof (simplex_scan_candidate_unique _ _ _ _ _ _ _ _ _ _ HC HC'); tauto.
Qed.


(* Prefix extension consumer bridge. Strict comparison with best retains
   the earliest row on duplicate basic indices. *)
Lemma simplex_scan_candidate_step : forall basic dir vars k best row direction,
  0 <= k -> basic k < vars ->
  simplex_scan_candidate basic dir vars k best row direction ->
  simplex_scan_candidate basic dir vars (k+1)
    (if (negb (Z.eqb (dir k) 0) && Z.ltb (basic k) best)%bool then basic k else best)
    (if (negb (Z.eqb (dir k) 0) && Z.ltb (basic k) best)%bool then k else row)
    (if (negb (Z.eqb (dir k) 0) && Z.ltb (basic k) best)%bool then dir k else direction).
Proof.
  intros basic dir vars k best row direction HK HB HC.
  apply simplex_scan_candidate_facts in HC.
  destruct (Z.eqb (dir k) 0) eqn:ED;
    [apply Z.eqb_eq in ED|apply Z.eqb_neq in ED]; simpl.
  - destruct HC as [[HR [HD [HV HZ]]]|[HR [HD [HV [HB' [HM HE]]]]]].
    + left. repeat split; auto. intros j HJ.
      destruct (Z.eq_dec j k); [subst; auto|apply HZ; lia].
    + apply simplex_scan_candidate_intro; try tauto; try lia.
      * intros j HJ HDj. destruct (Z.eq_dec j k); [subst; contradiction|apply HM; auto; lia].
      * intros j HJ HDj HBj. destruct (Z.eq_dec j k); [subst; contradiction|apply HE; auto; lia].
  - destruct (Z.ltb (basic k) best) eqn:EB;
      [apply Z.ltb_lt in EB|apply Z.ltb_ge in EB]; simpl.
    + apply simplex_scan_candidate_intro; try lia; auto.
      * intros j HJ HDj. destruct (Z.eq_dec j k); [subst; lia|].
        destruct HC as [[HR [HD [HV HZ]]]|[HR [HD [HV [HB' [HM HE]]]]]].
        -- specialize (HZ j ltac:(lia)). contradiction.
        -- specialize (HM j ltac:(lia) HDj). lia.
      * intros j HJ HDj HBj. destruct (Z.eq_dec j k); [subst; lia|].
        destruct HC as [[HR [HD [HV HZ]]]|[HR [HD [HV [HB' [HM HE]]]]]].
        -- specialize (HZ j ltac:(lia)). contradiction.
        -- specialize (HM j ltac:(lia) HDj). lia.
    + destruct HC as [[HR [HD [HV HZ]]]|[HR [HD [HV [HB' [HM HE]]]]]].
      * lia.
      * apply simplex_scan_candidate_intro; try tauto; try lia.
        -- intros j HJ HDj. destruct (Z.eq_dec j k); [subst; lia|apply HM; auto; lia].
        -- intros j HJ HDj HBj. destruct (Z.eq_dec j k); [subst; lia|apply HE; auto; lia].
Qed.

(* The concrete snapshot is nine lists, decoded at physical row i and then
   basic index b. Values in disabled slots are irrelevant to the row model;
   no initialized-memory requirement is inferred for those list defaults. *)
Definition simplex_scan_rows (basic hl hu vn vd ln ld un ud : list Z)
    (i : Z) : option Z :=
  let b := Znth i basic 0 in
  simplex_scan_row (Znth b hl 0) (Znth b hu 0)
    (Znth b vn 0) (Znth b vd 0) (Znth b ln 0) (Znth b ld 0)
    (Znth b un 0) (Znth b ud 0).

Definition simplex_scan_check (observations : Z -> option Z) (i : Z) : Z :=
  match observations i with Some _ => 1 | None => 0 end.
Definition simplex_scan_direction (observations : Z -> option Z) (i : Z) : Z :=
  match observations i with Some d => d | None => 0 end.

Definition simplex_scan_step (basic : Z -> Z) (obs : Z -> option Z)
    (state : Z * (Z * (Z * Z))) (i : Z) : Z * (Z * (Z * Z)) :=
  let '(q,(best,(row,direction))) := state in
  if Z.eqb q 0 then state else
  match obs i with
  | None => (0,(best,(row,direction)))
  | Some d => if (negb (Z.eqb d 0) && Z.ltb (basic i) best)%bool
              then (1,(basic i,(i,d))) else (1,(best,(row,direction)))
  end.

Definition simplex_scan_compute (basic : Z -> Z) (obs : Z -> option Z)
    (vars rows : Z) : Z * (Z * (Z * Z)) :=
  fold_left (simplex_scan_step basic obs) (Zrange 0 rows) (1,(vars,(-1,0))).

Lemma simplex_scan_range_snoc : forall k, 0 <= k ->
  Zrange 0 (k+1) = Zrange 0 k ++ [k].
Proof.
  intros k HK. unfold Zrange.
  replace (k+1-0) with (k+1) by lia.
  replace (k-0) with k by lia.
  rewrite Z2Nat.inj_add by lia. rewrite Zrange_aux_app.
  rewrite Z2Nat.id by lia. simpl. replace (0+k) with k by lia. reflexivity.
Qed.

Lemma simplex_scan_compute_empty : forall basic obs vars,
  simplex_scan_compute basic obs vars 0 = (1,(vars,(-1,0))).
Proof. reflexivity. Qed.

Lemma simplex_scan_compute_step : forall basic obs vars k,
  0 <= k -> simplex_scan_compute basic obs vars (k+1) =
  simplex_scan_step basic obs (simplex_scan_compute basic obs vars k) k.
Proof.
  intros. unfold simplex_scan_compute. rewrite simplex_scan_range_snoc by auto.
  rewrite fold_left_app. reflexivity.
Qed.

Lemma simplex_scan_failed_state_fixed : forall basic obs best row direction i,
  simplex_scan_step basic obs (0,(best,(row,direction))) i =
  (0,(best,(row,direction))).
Proof. reflexivity. Qed.

Lemma simplex_scan_failed_row_no_commit : forall basic obs best row direction i,
  obs i = None ->
  simplex_scan_step basic obs (1,(best,(row,direction))) i =
  (0,(best,(row,direction))).
Proof. intros. unfold simplex_scan_step. rewrite H. reflexivity. Qed.


Theorem simplex_scan_compute_prefix : forall basic obs vars k, 0 <= k ->
  (forall j, 0 <= j < k -> basic j < vars) ->
  forall q best row direction,
  simplex_scan_compute basic obs vars k = (q,(best,(row,direction))) ->
  (q = 1 /\ (forall j, 0 <= j < k -> simplex_scan_check obs j = 1) /\
    simplex_scan_candidate basic (simplex_scan_direction obs) vars k best row direction) \/
  (q = 0 /\ exists t,
    0 <= t < k /\ simplex_scan_check obs t = 0 /\
    (forall j, 0 <= j < t -> simplex_scan_check obs j = 1) /\
    simplex_scan_candidate basic (simplex_scan_direction obs) vars t best row direction).
Proof.
  intros basic obs vars k HK.
  revert k HK. refine (natlike_ind (fun k => _) _ _).
  - intros HB q best row direction HE.
    rewrite simplex_scan_compute_empty in HE. inversion HE; subst q best row direction.
    left. split; [reflexivity|]. split; [intros; lia|].
    apply simplex_scan_candidate_empty.
  - intros k HK IH HB q best row direction HE.
    replace (Z.succ k) with (k+1) in * by lia.
    rewrite simplex_scan_compute_step in HE by auto.
    destruct (simplex_scan_compute basic obs vars k) as [q0 [b0 [r0 d0]]] eqn:EC.
    specialize (IH ltac:(intros; apply HB; lia) q0 b0 r0 d0 eq_refl).
    destruct IH as [[HQ [HG HC]]|[HQ [t [HT [HF [HG HC]]]]]]; subst q0.
    + destruct (obs k) as [d|] eqn:EO.
      * assert (HD : simplex_scan_direction obs k = d).
        { unfold simplex_scan_direction. rewrite EO. reflexivity. }
        pose proof (simplex_scan_candidate_step basic (simplex_scan_direction obs)
          vars k b0 r0 d0 HK (HB k ltac:(lia)) HC) as HSTEP.
        rewrite HD in HSTEP.
        unfold simplex_scan_step in HE. rewrite EO in HE. simpl in HE.
        destruct (negb (Z.eqb d 0) && Z.ltb (basic k) b0)%bool eqn:ET;
          inversion HE; subst q best row direction; left; split; [reflexivity|..]; split.
        -- intros j HJ. destruct (Z.eq_dec j k); [subst; unfold simplex_scan_check; rewrite EO; reflexivity|apply HG; lia].
        -- exact HSTEP.
        -- intros j HJ. destruct (Z.eq_dec j k); [subst; unfold simplex_scan_check; rewrite EO; reflexivity|apply HG; lia].
        -- exact HSTEP.
      * unfold simplex_scan_step in HE. rewrite EO in HE. inversion HE; subst q best row direction.
        right. split; [reflexivity|]. exists k. repeat split; try lia; auto.
        unfold simplex_scan_check. rewrite EO. reflexivity.
    + rewrite simplex_scan_failed_state_fixed in HE. inversion HE; subst q best row direction.
      right. split; [reflexivity|]. exists t. repeat split; try lia; auto.
Qed.

Theorem simplex_scan_compute_correct : forall basic obs vars rows q best row direction,
  0 <= rows -> (forall j, 0 <= j < rows -> basic j < vars) ->
  simplex_scan_compute basic obs vars rows = (q,(best,(row,direction))) ->
  simplex_find_violation_result basic (simplex_scan_check obs)
    (simplex_scan_direction obs) vars rows q row direction.
Proof.
  intros. pose proof (simplex_scan_compute_prefix _ _ _ _ H H0 _ _ _ _ H1) as HC.
  destruct HC as [[-> [HG HC]]|[-> [t [HT [HF [HG HC]]]]]].
  - eapply simplex_scan_finish_success; eauto.
  - eapply simplex_scan_finish_failure; eauto.
Qed.

(* Direct, fully determined public result: the relational statement and
   pure fold computation agree for all basic indices below the sentinel.
   No check-success assumption is needed. *)
Theorem simplex_find_violation_compute_iff : forall basic obs vars rows q row direction,
  0 <= rows -> (forall j, 0 <= j < rows -> basic j < vars) ->
  (simplex_find_violation_result basic (simplex_scan_check obs)
      (simplex_scan_direction obs) vars rows q row direction <->
   exists best, simplex_scan_compute basic obs vars rows = (q,(best,(row,direction)))).
Proof.
  intros basic obs vars rows q row direction HR HB. split.
  - intros HS. destruct (simplex_scan_compute basic obs vars rows)
      as [q0 [best [row0 direction0]]] eqn:EC.
    pose proof (simplex_scan_compute_correct _ _ _ _ _ _ _ _ HR HB EC) as HS0.
    destruct (simplex_find_violation_result_unique _ _ _ _ _ _ _ _ _ _ _ HS HS0)
      as [-> [-> ->]]. eauto.
  - intros [best HC]. eapply simplex_scan_compute_correct; eauto.
Qed.


(* Representation decoding bridge used by the target C contract. *)
Definition simplex_find_violation_spec
    (basic hl hu vn vd ln ld un ud : list Z)
    (vars rows ret row direction : Z) : Prop :=
  let obs := simplex_scan_rows basic hl hu vn vd ln ld un ud in
  simplex_find_violation_result (fun i => Znth i basic 0)
    (simplex_scan_check obs) (simplex_scan_direction obs)
    vars rows ret row direction.

Example simplex_scan_zero_rows : forall basic obs vars,
  simplex_scan_compute basic obs vars 0 = (1,(vars,(-1,0))).
Proof. reflexivity. Qed.

Example simplex_scan_partial_failure_keeps_candidate :
  simplex_scan_compute (fun i => if Z.eqb i 0 then 2 else 0)
    (fun i => if Z.eqb i 0 then Some 1 else None) 3 2 = (0,(2,(0,1))).
Proof. vm_compute. reflexivity. Qed.

Example simplex_scan_duplicate_basic_earliest_row :
  simplex_scan_compute (fun _ => 1) (fun i => Some (if Z.eqb i 0 then 1 else -1))
    3 2 = (1,(1,(0,1))).
Proof. vm_compute. reflexivity. Qed.

Example simplex_scan_smaller_basic_later_row :
  simplex_scan_compute (fun i => if Z.eqb i 0 then 2 else 1)
    (fun i => Some (if Z.eqb i 0 then 1 else -1)) 3 2 = (1,(1,(1,-1))).
Proof. vm_compute. reflexivity. Qed.

(* Inconsistent bounds are legal scan inputs: upper violation overrides
   lower violation, and nonzero flags are not restricted to the value 1. *)
Example simplex_scan_upper_overrides_lower :
  simplex_scan_row (-7) 2 1 1 2 1 0 1 = Some (-1).
Proof. vm_compute. reflexivity. Qed.

Example simplex_scan_min_num_is_failure :
  simplex_scan_row 1 0 (-2147483648) 1 0 1 0 1 = None.
Proof. vm_compute. reflexivity. Qed.


(* State footprint uses symbolic typed member addresses; matrix rows use
   the native 24*sizeof(SxRat) stride, never nested CNotation [i][j]. *)
From Coq Require Import String.
From SimpleC.SL Require Export Mem SeparationLogic.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string_scope.

Definition simplex_scan_rat_memory (s : Z) (field : string) (j : Z)
    (enabled : bool) (n d : Z) : Assertion :=
  if enabled then
    &(s # "SxState" ->ₛ field [j] .ₛ "num") # Int |-> n **
    &(s # "SxState" ->ₛ field [j] .ₛ "den") # Int |-> d
  else
    &(s # "SxState" ->ₛ field [j] .ₛ "num") # Int |->_ **
    &(s # "SxState" ->ₛ field [j] .ₛ "den") # Int |->_ .

Definition simplex_scan_slot_memory (s : Z)
    (basic hl hu vn vd ln ld un ud : list Z) (j : Z) : Assertion :=
  let active := existsb (Z.eqb j) basic in
  let low := (active && negb (Z.eqb (Znth j hl 0) 0))%bool in
  let high := (active && negb (Z.eqb (Znth j hu 0) 0))%bool in
  (if active then
    (&(s # "SxState" ->ₛ "has_lower") + j * sizeof(INT)) # Int |-> Znth j hl 0 **
    (&(s # "SxState" ->ₛ "has_upper") + j * sizeof(INT)) # Int |-> Znth j hu 0
   else
    (&(s # "SxState" ->ₛ "has_lower") + j * sizeof(INT)) # Int |->_ **
    (&(s # "SxState" ->ₛ "has_upper") + j * sizeof(INT)) # Int |->_) **
  simplex_scan_rat_memory s "value" j (low || high)%bool (Znth j vn 0) (Znth j vd 0) **
  simplex_scan_rat_memory s "lower" j low (Znth j ln 0) (Znth j ld 0) **
  simplex_scan_rat_memory s "upper" j high (Znth j un 0) (Znth j ud 0).

Definition simplex_scan_slots_memory (s : Z)
    (basic hl hu vn vd ln ld un ud : list Z) : Assertion :=
  iter_sepcon (map (simplex_scan_slot_memory s basic hl hu vn vd ln ld un ud) (Zrange 0 24)).

Definition simplex_scan_slots_except (s : Z)
    (basic hl hu vn vd ln ld un ud : list Z) (j : Z) : Assertion :=
  iter_sepcon (remove_Znth j
    (map (simplex_scan_slot_memory s basic hl hu vn vd ln ld un ud) (Zrange 0 24))).

Definition simplex_scan_unused_memory (s rows : Z) : Assertion :=
  &(s # "SxState" ->ₛ "inputs") # Int |->_ **
  IntArray.undef_seg &(s # "SxState" ->ₛ "basic") rows 16 **
  IntArray.undef_full &(s # "SxState" ->ₛ "is_basic") 24 **
  iter_sepcon (map (fun i => simplex_scan_rat_memory s "rhs" i false 0 0) (Zrange 0 16)) **
  iter_sepcon (map (fun i => iter_sepcon (map (fun j =>
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const ((&(s # "SxState" ->ₛ "a") + i * (sizeof("SxRat") * 24)) + j * sizeof("SxRat"))
        (FET_alias "SxRat")) "num")) # Int |->_ **
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const ((&(s # "SxState" ->ₛ "a") + i * (sizeof("SxRat") * 24)) + j * sizeof("SxRat"))
        (FET_alias "SxRat")) "den")) # Int |->_)
    (Zrange 0 24))) (Zrange 0 16)).

Local Open Scope Z_scope.
Definition simplex_scan_prefix (basic hl hu vn vd ln ld un ud : list Z)
    (vars k best row direction : Z) : Prop :=
  let obs := simplex_scan_rows basic hl hu vn vd ln ld un ud in
  (forall j, 0 <= j < k -> simplex_scan_check obs j = 1) /\
  simplex_scan_candidate (fun i => Znth i basic 0) (simplex_scan_direction obs)
    vars k best row direction.


(* Entire-object output separation, including unused slots/padding. This
   concerns address ranges only; it supplies no initialized-value premise. *)
Definition simplex_scan_output_separation (s row direction : Z) : Prop :=
  (row + sizeof(INT) <= s \/ s + sizeof("SxState") <= row) /\
  (direction + sizeof(INT) <= s \/ s + sizeof("SxState") <= direction) /\
  (row + sizeof(INT) <= direction \/ direction + sizeof(INT) <= row).

Lemma simplex_scan_range_length : forall k, 0 <= k -> Zlength (Zrange 0 k) = k.
Proof.
  refine (natlike_ind (fun k => Zlength (Zrange 0 k) = k) _ _).
  - reflexivity.
  - intros k HK IH. replace (Z.succ k) with (k+1) by lia.
    rewrite simplex_scan_range_snoc by auto.
    rewrite Zlength_app, Zlength_cons, Zlength_nil, IH. lia.
Qed.

Lemma simplex_scan_range_nth : forall k, 0 <= k ->
  forall j, 0 <= j < k -> Znth j (Zrange 0 k) 0 = j.
Proof.
  refine (natlike_ind (fun k => forall j, 0 <= j < k -> Znth j (Zrange 0 k) 0 = j) _ _).
  - intros; lia.
  - intros k HK IH j HJ. replace (Z.succ k) with (k+1) in HJ by lia.
    replace (Z.succ k) with (k+1) by lia.
    rewrite simplex_scan_range_snoc by auto.
    destruct (Z_lt_dec j k).
    + rewrite app_Znth1; [apply IH; lia|rewrite simplex_scan_range_length; lia].
    + assert (j=k) by lia. subst j.
      rewrite app_Znth2; [rewrite simplex_scan_range_length by auto;
        replace (k-k) with 0 by lia; reflexivity|rewrite simplex_scan_range_length; lia].
Qed.

Lemma simplex_scan_slot_map_nth : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  Znth j (map (simplex_scan_slot_memory s basic hl hu vn vd ln ld un ud) (Zrange 0 24)) emp =
  simplex_scan_slot_memory s basic hl hu vn vd ln ld un ud j.
Proof.
  intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
  rewrite simplex_scan_range_nth by lia. reflexivity.
Qed.

Lemma simplex_scan_slots_split : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  simplex_scan_slots_memory s basic hl hu vn vd ln ld un ud |--
  simplex_scan_slot_memory s basic hl hu vn vd ln ld un ud j **
  simplex_scan_slots_except s basic hl hu vn vd ln ld un ud j.
Proof.
  intros. unfold simplex_scan_slots_memory, simplex_scan_slots_except.
  pose proof (iter_sepcon_split_remove_Znth j
    (map (simplex_scan_slot_memory s basic hl hu vn vd ln ld un ud) (Zrange 0 24)) emp) as HS.
  rewrite simplex_scan_slot_map_nth in HS by auto. apply HS.
  rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.

Lemma simplex_scan_slots_merge : forall s basic hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  simplex_scan_slot_memory s basic hl hu vn vd ln ld un ud j **
  simplex_scan_slots_except s basic hl hu vn vd ln ld un ud j |--
  simplex_scan_slots_memory s basic hl hu vn vd ln ld un ud.
Proof.
  intros. unfold simplex_scan_slots_memory, simplex_scan_slots_except.
  pose proof (iter_sepcon_merge_remove_Znth j
    (map (simplex_scan_slot_memory s basic hl hu vn vd ln ld un ud) (Zrange 0 24))
    (simplex_scan_slot_memory s basic hl hu vn vd ln ld un ud j)) as HM.
  rewrite <- (simplex_scan_slot_map_nth s basic hl hu vn vd ln ld un ud j H) in HM.
  rewrite replace_Znth_Znth in HM.
  rewrite simplex_scan_slot_map_nth in HM by auto. apply HM.
  rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.


(* QCP emits native array-pointer arithmetic at the current-slot Assert.
   Use the framework's existing address equivalences; no layout equation
   or new axiom is introduced. *)
Lemma simplex_scan_rat_member_address : forall s field member j,
  &(s # "SxState" ->ₛ field [j] .ₛ member) =
  eval_addr_expr (RE_addr_of (LE_arrow_field
    (RE_const (&(s # "SxState" ->ₛ field) + j * sizeof("SxRat"))
      (FET_alias "SxRat")) member)).
Proof. intros. csimpl. reflexivity. Qed.


Lemma simplex_scan_slot_active : forall s basic hl hu vn vd ln ld un ud j,
  In j basic ->
  simplex_scan_slot_memory s basic hl hu vn vd ln ld un ud j --||--
  ((&(s # "SxState" ->ₛ "has_lower") + j * sizeof(INT)) # Int |-> Znth j hl 0 **
   (&(s # "SxState" ->ₛ "has_upper") + j * sizeof(INT)) # Int |-> Znth j hu 0 **
   simplex_scan_rat_memory s "value" j
     (negb (Z.eqb (Znth j hl 0) 0) || negb (Z.eqb (Znth j hu 0) 0))%bool
     (Znth j vn 0) (Znth j vd 0) **
   simplex_scan_rat_memory s "lower" j (negb (Z.eqb (Znth j hl 0) 0))
     (Znth j ln 0) (Znth j ld 0) **
   simplex_scan_rat_memory s "upper" j (negb (Z.eqb (Znth j hu 0) 0))
     (Znth j un 0) (Znth j ud 0)).
Proof.
  intros. unfold simplex_scan_slot_memory.
  assert (HA : existsb (Z.eqb j) basic = true).
  { apply existsb_exists. exists j. split; [auto|apply Z.eqb_refl]. }
  rewrite HA. simpl. reflexivity.
Qed.


Definition simplex_scan_value_memory (s j lower upper n d : Z) : Assertion :=
  simplex_scan_rat_memory s "value" j
    (negb (Z.eqb lower 0) || negb (Z.eqb upper 0))%bool n d.
Definition simplex_scan_lower_memory (s j flag n d : Z) : Assertion :=
  simplex_scan_rat_memory s "lower" j (negb (Z.eqb flag 0)) n d.
Definition simplex_scan_upper_memory (s j flag n d : Z) : Assertion :=
  simplex_scan_rat_memory s "upper" j (negb (Z.eqb flag 0)) n d.

Lemma simplex_scan_slot_active_folded : forall s basic hl hu vn vd ln ld un ud j,
  In j basic ->
  simplex_scan_slot_memory s basic hl hu vn vd ln ld un ud j --||--
  ((&(s # "SxState" ->ₛ "has_lower") + j * sizeof(INT)) # Int |-> Znth j hl 0 **
   (&(s # "SxState" ->ₛ "has_upper") + j * sizeof(INT)) # Int |-> Znth j hu 0 **
   simplex_scan_value_memory s j (Znth j hl 0) (Znth j hu 0) (Znth j vn 0) (Znth j vd 0) **
   simplex_scan_lower_memory s j (Znth j hl 0) (Znth j ln 0) (Znth j ld 0) **
   simplex_scan_upper_memory s j (Znth j hu 0) (Znth j un 0) (Znth j ud 0)).
Proof. intros. apply simplex_scan_slot_active; auto. Qed.

Lemma simplex_scan_rat_memory_enabled : forall s field j n d,
  simplex_scan_rat_memory s field j true n d --||--
  eval_addr_expr (RE_addr_of (LE_arrow_field
    (RE_const (&(s # "SxState" ->ₛ field) + j * sizeof("SxRat"))
      (FET_alias "SxRat")) "num")) # Int |-> n **
  eval_addr_expr (RE_addr_of (LE_arrow_field
    (RE_const (&(s # "SxState" ->ₛ field) + j * sizeof("SxRat"))
      (FET_alias "SxRat")) "den")) # Int |-> d.
Proof.
  intros. unfold simplex_scan_rat_memory.
  rewrite !simplex_scan_rat_member_address. reflexivity.
Qed.

Lemma simplex_scan_lower_memory_enabled : forall s j flag n d,
  flag <> 0 -> simplex_scan_lower_memory s j flag n d --||--
  simplex_scan_rat_memory s "lower" j true n d.
Proof. intros. unfold simplex_scan_lower_memory. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.
Lemma simplex_scan_upper_memory_enabled : forall s j flag n d,
  flag <> 0 -> simplex_scan_upper_memory s j flag n d --||--
  simplex_scan_rat_memory s "upper" j true n d.
Proof. intros. unfold simplex_scan_upper_memory. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.
Lemma simplex_scan_value_memory_enabled : forall s j lower upper n d,
  lower <> 0 \/ upper <> 0 -> simplex_scan_value_memory s j lower upper n d --||--
  simplex_scan_rat_memory s "value" j true n d.
Proof.
  intros. unfold simplex_scan_value_memory. destruct H as [H|H];
  apply Z.eqb_neq in H; rewrite H; simpl; [reflexivity|rewrite Bool.orb_true_r; reflexivity].
Qed.

(* Native generated arrow syntax and the explicit typed row-stride expression
   denote the same member address. The old nested notation loses row type;
   no equality to that old representation is asserted. *)
(* Representation bridge exposes the unused matrix with the exact native
   row stride. All cells remain unknown writable permissions. *)
Lemma simplex_scan_unused_native_shape : forall s rows,
  simplex_scan_unused_memory s rows --||--
  (&(s # "SxState" ->ₛ "inputs") # Int |->_ **
   IntArray.undef_seg &(s # "SxState" ->ₛ "basic") rows 16 **
   IntArray.undef_full &(s # "SxState" ->ₛ "is_basic") 24 **
   iter_sepcon (map (fun i => simplex_scan_rat_memory s "rhs" i false 0 0) (Zrange 0 16)) **
   iter_sepcon (map (fun i => iter_sepcon (map (fun j =>
     (&((((&((s) # "SxState" ->ₛ "a") + (i * (sizeof("SxRat") * 24))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |->_ **
     (&((((&((s) # "SxState" ->ₛ "a") + (i * (sizeof("SxRat") * 24))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |->_)
     (Zrange 0 24))) (Zrange 0 16))).
Proof. intros. unfold simplex_scan_unused_memory. reflexivity. Qed.


Lemma simplex_scan_prefix_zero_step__nonviolating_rows : forall basic hl hu vn vd ln ld un ud vars k best row direction,
  0 <= k -> Znth k basic 0 < vars ->
  simplex_scan_rows basic hl hu vn vd ln ld un ud k = Some 0 ->
  simplex_scan_prefix basic hl hu vn vd ln ld un ud vars k best row direction ->
  simplex_scan_prefix basic hl hu vn vd ln ld un ud vars (k+1) best row direction.
Proof.
 intros basic hl hu vn vd ln ld un ud vars k best row direction HK HB HE [HC HW].
 split.
 - intros j HJ. destruct (Z.eq_dec j k) as [->|HN].
   + unfold simplex_scan_check. rewrite HE. reflexivity.
   + apply HC. lia.
 - pose proof (simplex_scan_candidate_step (fun j => Znth j basic 0)
     (simplex_scan_direction (simplex_scan_rows basic hl hu vn vd ln ld un ud))
     vars k best row direction HK HB HW) as HS.
   unfold simplex_scan_direction in HS. rewrite HE in HS. simpl in HS. exact HS.
Qed.
