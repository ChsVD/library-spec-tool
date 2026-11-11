From Coq Require Import ZArith List Lia.
From SimpleC.EE.Applications_human.simplex_find_violation
  Require Export simplex_find_violation_lib.
Import ListNotations.
Local Open Scope Z_scope.

(* FME's algorithm.v uses integer LP_sol and positive linear combinations;
   neither FME_step_sound nor its implementation classification lemmas supply
   checked rational first-choice search. Reuse only the verified rational/QCP
   foundations and prior common range/resource lemmas, never its C contract.
   Some false = skip; Some true = choose; None = checked failure. *)
Definition simplex_enter_column (basic coeff direction hl hu vn vd ln ld un ud : Z)
    : option bool :=
  if (negb (Z.eqb basic 0) || Z.eqb coeff 0)%bool then Some false else
  let increase := ((Z.ltb 0 coeff && Z.ltb 0 direction) ||
                   (Z.ltb coeff 0 && Z.ltb direction 0))%bool in
  if increase then
    if Z.eqb hu 0 then Some true else
    if Z.eqb (simplex_rat_compare_flag vn vd un ud) 1 then
      Some (Z.ltb (simplex_rat_compare_order vn vd un ud) 0) else None
  else
    if Z.eqb hl 0 then Some true else
    if Z.eqb (simplex_rat_compare_flag vn vd ln ld) 1 then
      Some (Z.ltb 0 (simplex_rat_compare_order vn vd ln ld)) else None.

Definition simplex_enter_observations
    (basic coeff hl hu vn vd ln ld un ud : list Z) (direction j : Z) :=
  simplex_enter_column (Znth j basic 0) (Znth j coeff 0) direction
    (Znth j hl 0) (Znth j hu 0) (Znth j vn 0) (Znth j vd 0)
    (Znth j ln 0) (Znth j ld 0) (Znth j un 0) (Znth j ud 0).

(* First terminal observation; all earlier observations must be skips.
   No condition on later columns can alter a first choice or failure. *)
Definition simplex_enter_result (obs : Z -> option bool) (vars q e : Z) : Prop :=
  (q = 1 /\ e = -1 /\ forall j, 0 <= j < vars -> obs j = Some false) \/
  (exists k, 0 <= k < vars /\
    (forall j, 0 <= j < k -> obs j = Some false) /\
    ((q = 1 /\ e = k /\ obs k = Some true) \/
     (q = 0 /\ e = -1 /\ obs k = None))).

Lemma simplex_enter_result_unique : forall obs v q e q' e',
  simplex_enter_result obs v q e -> simplex_enter_result obs v q' e' ->
  q=q' /\ e=e'.
Proof.
  intros obs v q e q' e' H H'.
  destruct H as [[-> [-> HS]]|[k [HK [HS HT]]]];
  destruct H' as [[-> [-> HS']]|[k' [HK' [HS' HT']]]].
  - auto.
  - specialize (HS k' HK'). destruct HT' as [[? [? HC]]|[? [? HC]]]; congruence.
  - specialize (HS' k HK). destruct HT as [[? [? HC]]|[? [? HC]]]; congruence.
  - assert (k=k').
    { destruct (Z.lt_trichotomy k k') as [HL|[HE|HR]]; auto.
      - specialize (HS' k ltac:(lia)). destruct HT as [[? [? HC]]|[? [? HC]]]; congruence.
      - specialize (HS k' ltac:(lia)). destruct HT' as [[? [? HC]]|[? [? HC]]]; congruence. }
    subst k'. destruct HT as [[? [? HC]]|[? [? HC]]];
    destruct HT' as [[? [? HC']]|[? [? HC']]]; split; congruence.
Qed.

Definition simplex_enter_step (obs : Z -> option bool) (state : Z * Z) (j : Z) :=
  let '(q,e) := state in
  if (Z.eqb q 1 && Z.eqb e (-1))%bool then
    match obs j with
    | Some false => state
    | Some true => (1,j)
    | None => (0,-1)
    end
  else state.
Definition simplex_enter_compute (obs : Z -> option bool) (vars : Z) :=
  fold_left (simplex_enter_step obs) (Zrange 0 vars) (1,-1).
Lemma simplex_enter_compute_step : forall obs k, 0 <= k ->
  simplex_enter_compute obs (k+1) =
    simplex_enter_step obs (simplex_enter_compute obs k) k.
Proof.
  intros. unfold simplex_enter_compute. rewrite simplex_scan_range_snoc by auto.
  rewrite fold_left_app. reflexivity.
Qed.

Lemma simplex_enter_result_extend : forall obs k q e,
  0 <= k -> simplex_enter_result obs k q e ->
  simplex_enter_result obs (k+1)
    (fst (simplex_enter_step obs (q,e) k))
    (snd (simplex_enter_step obs (q,e) k)).
Proof.
  intros obs k q e HK [[-> [-> HS]]|[t [HT [HS HC]]]].
  - unfold simplex_enter_step. simpl.
    destruct (obs k) as [[|]|] eqn:HO; simpl.
    + right. exists k. repeat split; try lia; auto.
    + left. repeat split; auto. intros j HJ.
      destruct (Z.eq_dec j k); [subst; auto|apply HS; lia].
    + right. exists k. repeat split; try lia; auto.
  - destruct HC as [[-> [-> HO]]|[-> [-> HO]]]; unfold simplex_enter_step; simpl.
    + assert (Z.eqb t (-1) = false) by (apply Z.eqb_neq; lia).
      rewrite H. simpl. right. exists t. repeat split; try lia; auto.
    + right. exists t. repeat split; try lia; auto.
Qed.

Theorem simplex_enter_compute_correct : forall obs v,
  0 <= v -> simplex_enter_result obs v
    (fst (simplex_enter_compute obs v)) (snd (simplex_enter_compute obs v)).
Proof.
  intros obs. refine (natlike_ind (fun v => _) _ _).
  - left. simpl. repeat split; auto; intros; lia.
  - intros k HK IH. replace (Z.succ k) with (k+1) by lia.
    rewrite simplex_enter_compute_step by auto.
    destruct (simplex_enter_compute obs k) as [q e] eqn:HC.
    simpl in IH. apply simplex_enter_result_extend; auto.
Qed.

Theorem simplex_enter_compute_iff : forall obs v q e, 0 <= v ->
  (simplex_enter_result obs v q e <-> simplex_enter_compute obs v = (q,e)).
Proof.
  intros obs v q e HV. pose proof (simplex_enter_compute_correct obs v HV) as HC.
  destruct (simplex_enter_compute obs v) as [q0 e0] eqn:HE. simpl in HC.
  split.
  - intros H. destruct (simplex_enter_result_unique _ _ _ _ _ _ H HC) as [-> ->]. reflexivity.
  - intros H. inversion H; subst. exact HC.
Qed.

Definition simplex_find_entering_spec
    (basic coeff hl hu vn vd ln ld un ud : list Z) (direction vars q e : Z) : Prop :=
  simplex_enter_result
    (simplex_enter_observations basic coeff hl hu vn vd ln ld un ud direction) vars q e.

Example simplex_enter_empty : forall obs, simplex_enter_compute obs 0 = (1,-1).
Proof. reflexivity. Qed.
Example simplex_enter_choice_preempts_failure :
  simplex_enter_compute (fun j => if Z.eqb j 0 then Some true else None) 24 = (1,0).
Proof. vm_compute. reflexivity. Qed.
Example simplex_enter_failure_preempts_choice :
  simplex_enter_compute (fun j => if Z.eqb j 0 then None else Some true) 24 = (0,-1).
Proof. vm_compute. reflexivity. Qed.
Example simplex_enter_direction_zero_decreases :
  simplex_enter_column 0 1 0 0 1 0 1 0 1 1 1 = Some true.
Proof. vm_compute. reflexivity. Qed.
Example simplex_enter_unreduced_equality_skips :
  simplex_enter_column 0 1 1 0 1 1 2 0 1 2 4 = Some false.
Proof. vm_compute. reflexivity. Qed.
Example simplex_enter_second_check_failure :
  simplex_enter_column 0 1 1 0 1 0 2147483647 0 1 2 1 = None.
Proof. vm_compute. reflexivity. Qed.

(* A skip-prefix is the loop's mathematical progress, not a new execution
   semantics. The exit result is shared with the public relation. *)
Lemma simplex_enter_skip_extend : forall obs k,
  (forall j, 0 <= j < k -> obs j = Some false) -> obs k = Some false ->
  forall j, 0 <= j < k+1 -> obs j = Some false.
Proof. intros obs k HS HK j HJ. destruct (Z.eq_dec j k); [subst; auto|apply HS; lia]. Qed.
Lemma simplex_enter_finish : forall obs vars k q e,
  0 <= k < vars -> (forall j, 0 <= j < k -> obs j = Some false) ->
  ((q=1 /\ e=k /\ obs k=Some true) \/ (q=0 /\ e= -1 /\ obs k=None)) ->
  simplex_enter_result obs vars q e.
Proof. intros. right. exists k. auto. Qed.

From Coq Require Import String.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string_scope.

(* The native C frontend represents the fixed 24-element row as a byte
   offset 24*sizeof(SxRat), then a typed SxRat column/member address.
   CNotation nested [i][j] has no array-row frontend_type, so it cannot
   represent this stride. Use exactly the native generated typed addresses;
   this corrects ownership representation, never asserts equality to the old
   nested notation. All inactive/disabled permissions use the same layout. *)
(* Each column owns its typed rational cells, without reinterpreting struct
   arrays as int arrays. Flags use built-in IntArray in the C contract.
   Only selected-row active coefficients and active values are initialized;
   disabled bounds and every other coefficient retain unknown permission. *)
Definition simplex_enter_coeff_memory (s row vars : Z) (cn cd : list Z)
    (j i : Z) : Assertion :=
  if (Z.eqb i row && Z.ltb j vars)%bool then
    eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const ((&(s # "SxState" ->ₛ "a") + i * (sizeof("SxRat") * 24)) + j * sizeof("SxRat")) (FET_alias "SxRat")) "num")) # Int |-> Znth j cn 0 **
    eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const ((&(s # "SxState" ->ₛ "a") + i * (sizeof("SxRat") * 24)) + j * sizeof("SxRat")) (FET_alias "SxRat")) "den")) # Int |-> Znth j cd 0
  else
    eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const ((&(s # "SxState" ->ₛ "a") + i * (sizeof("SxRat") * 24)) + j * sizeof("SxRat")) (FET_alias "SxRat")) "num")) # Int |->_ **
    eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const ((&(s # "SxState" ->ₛ "a") + i * (sizeof("SxRat") * 24)) + j * sizeof("SxRat")) (FET_alias "SxRat")) "den")) # Int |->_ .
Definition simplex_enter_slot_memory (s row vars : Z)
    (cn cd hl hu vn vd ln ld un ud : list Z) (j : Z) : Assertion :=
  simplex_scan_rat_memory s "value" j (Z.ltb j vars) (Znth j vn 0) (Znth j vd 0) **
  simplex_scan_rat_memory s "lower" j
    (Z.ltb j vars && negb (Z.eqb (Znth j hl 0) 0))%bool (Znth j ln 0) (Znth j ld 0) **
  simplex_scan_rat_memory s "upper" j
    (Z.ltb j vars && negb (Z.eqb (Znth j hu 0) 0))%bool (Znth j un 0) (Znth j ud 0) **
  iter_sepcon (map (simplex_enter_coeff_memory s row vars cn cd j) (Zrange 0 16)).
Definition simplex_enter_slots_memory (s row vars : Z)
    (cn cd hl hu vn vd ln ld un ud : list Z) : Assertion :=
  iter_sepcon (map (simplex_enter_slot_memory s row vars cn cd hl hu vn vd ln ld un ud) (Zrange 0 24)).
Definition simplex_enter_slots_except (s row vars : Z)
    (cn cd hl hu vn vd ln ld un ud : list Z) (j : Z) : Assertion :=
  iter_sepcon (remove_Znth j
    (map (simplex_enter_slot_memory s row vars cn cd hl hu vn vd ln ld un ud) (Zrange 0 24))).
Definition simplex_enter_unused_memory (s : Z) : Assertion :=
  &(s # "SxState" ->ₛ "rows") # Int |->_ **
  &(s # "SxState" ->ₛ "inputs") # Int |->_ **
  IntArray.undef_full &(s # "SxState" ->ₛ "basic") 16 **
  iter_sepcon (map (fun i => simplex_scan_rat_memory s "rhs" i false 0 0) (Zrange 0 16)).

Local Open Scope Z_scope.
Lemma simplex_enter_slot_map_nth : forall s row vars cn cd hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  Znth j (map (simplex_enter_slot_memory s row vars cn cd hl hu vn vd ln ld un ud) (Zrange 0 24)) emp =
  simplex_enter_slot_memory s row vars cn cd hl hu vn vd ln ld un ud j.
Proof.
  intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
  rewrite simplex_scan_range_nth by lia. reflexivity.
Qed.
Lemma simplex_enter_slots_split : forall s row vars cn cd hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  simplex_enter_slots_memory s row vars cn cd hl hu vn vd ln ld un ud |--
  simplex_enter_slot_memory s row vars cn cd hl hu vn vd ln ld un ud j **
  simplex_enter_slots_except s row vars cn cd hl hu vn vd ln ld un ud j.
Proof.
  intros. unfold simplex_enter_slots_memory, simplex_enter_slots_except.
  pose proof (iter_sepcon_split_remove_Znth j
    (map (simplex_enter_slot_memory s row vars cn cd hl hu vn vd ln ld un ud) (Zrange 0 24)) emp) as HS.
  rewrite simplex_enter_slot_map_nth in HS by auto. apply HS.
  rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma simplex_enter_slots_merge : forall s row vars cn cd hl hu vn vd ln ld un ud j,
  0 <= j < 24 ->
  simplex_enter_slot_memory s row vars cn cd hl hu vn vd ln ld un ud j **
  simplex_enter_slots_except s row vars cn cd hl hu vn vd ln ld un ud j |--
  simplex_enter_slots_memory s row vars cn cd hl hu vn vd ln ld un ud.
Proof.
  intros. unfold simplex_enter_slots_memory, simplex_enter_slots_except.
  pose proof (iter_sepcon_merge_remove_Znth j
    (map (simplex_enter_slot_memory s row vars cn cd hl hu vn vd ln ld un ud) (Zrange 0 24))
    (simplex_enter_slot_memory s row vars cn cd hl hu vn vd ln ld un ud j)) as HM.
  rewrite <- (simplex_enter_slot_map_nth s row vars cn cd hl hu vn vd ln ld un ud j H) in HM.
  rewrite replace_Znth_Znth in HM. rewrite simplex_enter_slot_map_nth in HM by auto.
  apply HM. rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.

Definition simplex_enter_coeff_except (s row vars : Z) (cn cd : list Z) (j : Z) : Assertion :=
  iter_sepcon (remove_Znth row
    (map (simplex_enter_coeff_memory s row vars cn cd j) (Zrange 0 16))).
Definition simplex_enter_output_separation (s output : Z) : Prop :=
  output + sizeof(INT) <= s \/ s + sizeof("SxState") <= output.

Lemma simplex_enter_coeff_split : forall s row vars cn cd j,
  0 <= row < 16 -> 0 <= j < vars ->
  iter_sepcon (map (simplex_enter_coeff_memory s row vars cn cd j) (Zrange 0 16)) |--
  (eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const ((&(s # "SxState" ->ₛ "a") + row * (sizeof("SxRat") * 24)) + j * sizeof("SxRat")) (FET_alias "SxRat")) "num")) # Int |-> Znth j cn 0 **
   eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const ((&(s # "SxState" ->ₛ "a") + row * (sizeof("SxRat") * 24)) + j * sizeof("SxRat")) (FET_alias "SxRat")) "den")) # Int |-> Znth j cd 0) **
   simplex_enter_coeff_except s row vars cn cd j.
Proof.
  intros. unfold simplex_enter_coeff_except.
  pose proof (iter_sepcon_split_remove_Znth row
    (map (simplex_enter_coeff_memory s row vars cn cd j) (Zrange 0 16)) emp) as HS.
  rewrite (Znth_map _ _ _ 0 emp) in HS by (rewrite simplex_scan_range_length; lia).
  rewrite simplex_scan_range_nth in HS by lia.
  unfold simplex_enter_coeff_memory in HS.
  rewrite Z.eqb_refl in HS. assert (Z.ltb j vars = true) by (apply Z.ltb_lt; lia).
  rewrite H1 in HS. cbn [andb] in HS. unfold simplex_enter_coeff_memory. rewrite H1. apply HS.
  rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.

Definition simplex_enter_skipped (basic coeff hl hu vn vd ln ld un ud : list Z)
    (direction k : Z) : Prop :=
  forall j, 0 <= j < k ->
    simplex_enter_observations basic coeff hl hu vn vd ln ld un ud direction j = Some false.


(* Reverse of the current-coefficient cutpoint, with the same exact native
   address shape emitted by C for s->a[row][j].num and .den. *)
Lemma simplex_enter_coeff_merge : forall s row vars cn cd j,
  0 <= row < 16 -> 0 <= j < vars ->
  (eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const ((&(s # "SxState" ->ₛ "a") + row * (sizeof("SxRat") * 24)) + j * sizeof("SxRat")) (FET_alias "SxRat")) "num")) # Int |-> Znth j cn 0 **
   eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const ((&(s # "SxState" ->ₛ "a") + row * (sizeof("SxRat") * 24)) + j * sizeof("SxRat")) (FET_alias "SxRat")) "den")) # Int |-> Znth j cd 0) **
  simplex_enter_coeff_except s row vars cn cd j |--
  iter_sepcon (map (simplex_enter_coeff_memory s row vars cn cd j) (Zrange 0 16)).
Proof.
  intros s row vars cn cd j HR HJ.
  unfold simplex_enter_coeff_except.
  pose proof (iter_sepcon_merge_remove_Znth row
    (map (simplex_enter_coeff_memory s row vars cn cd j) (Zrange 0 16))
    (Znth row (map (simplex_enter_coeff_memory s row vars cn cd j) (Zrange 0 16)) emp)) as HM.
  rewrite replace_Znth_Znth in HM.
  rewrite (Znth_map _ _ _ 0 emp) in HM by (rewrite simplex_scan_range_length; lia).
  rewrite simplex_scan_range_nth in HM by lia.
  assert (EJ : Z.ltb j vars = true) by (apply Z.ltb_lt; lia).
  assert (ES : simplex_enter_coeff_memory s row vars cn cd j row =
    (eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const ((&(s # "SxState" ->ₛ "a") + row * (sizeof("SxRat") * 24)) + j * sizeof("SxRat")) (FET_alias "SxRat")) "num")) # Int |-> Znth j cn 0 **
     eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const ((&(s # "SxState" ->ₛ "a") + row * (sizeof("SxRat") * 24)) + j * sizeof("SxRat")) (FET_alias "SxRat")) "den")) # Int |-> Znth j cd 0)).
  { unfold simplex_enter_coeff_memory. rewrite Z.eqb_refl, EJ. reflexivity. }
  rewrite ES in HM. apply HM. rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.

(* The RHS below is copied verbatim from actual generated coefficient cells
   (only universally bound names are renamed). Thus this bridge checks the
   concrete consumer shape, including the row stride and typed arrow node. *)
Lemma simplex_enter_coeff_generated_shape : forall s row vars cn cd j,
  0 <= j < vars ->
  simplex_enter_coeff_memory s row vars cn cd j row =
  (((&((((&((s)  # "SxState" ->ₛ "a") + (row * (sizeof( "SxRat" ) * 24))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (cn) (0))) **
   ((&((((&((s)  # "SxState" ->ₛ "a") + (row * (sizeof( "SxRat" ) * 24))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (cd) (0)))).
Proof.
  intros. unfold simplex_enter_coeff_memory.
  assert (HJ : Z.ltb j vars = true) by (apply Z.ltb_lt; lia).
  rewrite Z.eqb_refl, HJ. reflexivity.
Qed.

Lemma simplex_enter_current_slot_merge : forall s row vars cn cd hl hu vn vd ln ld un ud j,
  0 <= row < 16 -> 0 <= j < vars -> j < 24 ->
  (((&((((&((s)  # "SxState" ->ₛ "a") + (row * (sizeof( "SxRat" ) * 24))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (cn) (0))) **
   ((&((((&((s)  # "SxState" ->ₛ "a") + (row * (sizeof( "SxRat" ) * 24))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (cd) (0)))) **
  simplex_enter_coeff_except s row vars cn cd j **
  simplex_scan_rat_memory s "value" j true (Znth j vn 0) (Znth j vd 0) **
  simplex_scan_rat_memory s "lower" j (negb (Z.eqb (Znth j hl 0) 0)) (Znth j ln 0) (Znth j ld 0) **
  simplex_scan_rat_memory s "upper" j (negb (Z.eqb (Znth j hu 0) 0)) (Znth j un 0) (Znth j ud 0) **
  simplex_enter_slots_except s row vars cn cd hl hu vn vd ln ld un ud j |--
  simplex_enter_slots_memory s row vars cn cd hl hu vn vd ln ld un ud.
Proof.
  intros.
  sep_apply_r_atomic (simplex_enter_slots_merge s row vars cn cd hl hu vn vd ln ld un ud j ltac:(lia)).
  unfold simplex_enter_slot_memory.
  assert (HJ : Z.ltb j vars = true) by (apply Z.ltb_lt; lia).
  rewrite HJ. cbn [andb].
  sepcon_assoc_change.
  sep_apply_r_atomic (simplex_enter_coeff_merge s row vars cn cd j H H0).
  cancel.
  sepcon_assoc_change. cancel.
Qed.
