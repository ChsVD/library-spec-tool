From Coq Require Import ZArith List Bool Lia Lra QArith Qabs Qring String.
From AUXLib Require Import ListLib.
From SumLib Require Import ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_lib.
From SimpleC.EE.Applications_human.simplex_gmp_minimal
  Require Import integers_fme_model_lib pivot_fme_model_lib sx_check_fme_model_lib.
From SimpleC.EE.Applications_human.simplex_gmp_optimized
  Require Export build_opt_lib.
Import naive_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.
Local Open Scope Z_scope.

(* Sign bits range over a finite prefix of input rows at a fixed column. *)
Definition os_coef (r : build_row_snapshot) (j : Z) : Z :=
  Znth (j+1) (build_row_entries r) 0.

Definition os_pos j rows := existsb (fun r => 0 <? os_coef r j) rows.
Definition os_neg j rows := existsb (fun r => os_coef r j <? 0) rows.
Definition os_mask j rows : Z :=
  (if os_pos j rows then 1 else 0) + (if os_neg j rows then 2 else 0).

(* A common rational direction which strictly reduces every removed row. *)
Definition os_dir rows j : Z :=
  if os_pos j rows then (if os_neg j rows then 0 else -1)
  else (if os_neg j rows then 1 else 0).

Definition os_keep_col rows r j : bool :=
  (Z.eqb (os_dir rows j) 0 || Z.eqb (os_coef r j) 0)%bool.

Definition os_kept n rows :=
  filter (fun r => forallb (os_keep_col rows r) (Zrange 0%Z n)) rows.

Definition os_slope columns rows r : Z :=
  fold_right Z.add 0 (map (fun j => os_coef r j * os_dir rows j) columns).

Definition os_eval n (x : Z -> Q) r : Q :=
  (inject_Z (Znth 0%Z (build_row_entries r) 0%Z) +
    fold_right Qplus 0
      (map (fun j => (inject_Z (os_coef r j) * x j)%Q) (Zrange 0%Z n)))%Q.

Lemma os_mask_range j rows : 0 <= os_mask j rows <= 3.
Proof.
  unfold os_mask. destruct (os_pos j rows), (os_neg j rows); lia.
Qed.

Lemma os_keep_col_bit rows r j :
  os_keep_col rows r j = true <->
  ((os_mask j rows <> 1 /\ os_mask j rows <> 2) \/ os_coef r j = 0).
Proof.
  unfold os_keep_col, os_mask, os_dir.
  destruct (os_pos j rows), (os_neg j rows); simpl;
    try (rewrite Z.eqb_eq); intuition lia.
Qed.

Lemma os_kept_length n rows : 0 <= Zlength (os_kept n rows) <= Zlength rows.
Proof.
  unfold os_kept. rewrite !Zlength_correct. split; [lia|].
  apply Nat2Z.inj_le, filter_length_le.
Qed.

Lemma os_slope_term_nonpos rows r j :
  In r rows -> os_coef r j * os_dir rows j <= 0.
Proof.
  intro Hin. unfold os_dir.
  destruct (os_pos j rows) eqn:Hp, (os_neg j rows) eqn:Hn; try lia.
  - assert (0 <= os_coef r j).
    { destruct (Z_lt_ge_dec (os_coef r j) 0); [|lia].
      assert (os_neg j rows = true) by
        (apply existsb_exists; exists r; split; [assumption|apply Z.ltb_lt; lia]).
      congruence. }
    lia.
  - assert (os_coef r j <= 0).
    { destruct (Z_le_gt_dec (os_coef r j) 0); [assumption|].
      assert (os_pos j rows = true) by
        (apply existsb_exists; exists r; split; [assumption|apply Z.ltb_lt; lia]).
      congruence. }
    lia.
Qed.

Lemma os_slope_nonpos cols rows r :
  In r rows -> os_slope cols rows r <= 0.
Proof.
  intro Hin. unfold os_slope.
  induction cols as [|j cols IH]; [reflexivity|].
  simpl. pose proof (os_slope_term_nonpos rows r j Hin). lia.
Qed.

Lemma os_slope_kept cols rows r :
  forallb (os_keep_col rows r) cols = true -> os_slope cols rows r = 0.
Proof.
  unfold os_slope. induction cols as [|j cols IH]; [reflexivity|].
  simpl. rewrite andb_true_iff. intros [Hj Hcols].
  unfold os_keep_col in Hj. apply orb_true_iff in Hj.
  rewrite IH by exact Hcols.
  destruct Hj as [Hd|Hc]; apply Z.eqb_eq in Hd || apply Z.eqb_eq in Hc; nia.
Qed.

Lemma os_slope_removed cols rows r :
  In r rows -> forallb (os_keep_col rows r) cols = false ->
  os_slope cols rows r < 0.
Proof.
  intro Hin. induction cols as [|j cols IH]; [discriminate|].
  simpl. rewrite andb_false_iff. intros [Hj|Hcols].
  - change (os_coef r j * os_dir rows j + os_slope cols rows r < 0).
    unfold os_keep_col in Hj. apply orb_false_iff in Hj.
    destruct Hj as [Hd Hc]; apply Z.eqb_neq in Hd, Hc.
    pose proof (os_slope_nonpos cols rows r Hin).
    pose proof (os_slope_term_nonpos rows r j Hin).
    nia.
  - change (os_coef r j * os_dir rows j + os_slope cols rows r < 0).
    specialize (IH Hcols). pose proof (os_slope_term_nonpos rows r j Hin). lia.
Qed.

Lemma os_sum_shift cols rows r x t :
  (fold_right Qplus 0
      (map (fun j => inject_Z (os_coef r j) *
              (x j + t * inject_Z (os_dir rows j))) cols)
    == fold_right Qplus 0 (map (fun j => inject_Z (os_coef r j) * x j) cols)
         + t * inject_Z (os_slope cols rows r))%Q.
Proof.
  unfold os_slope. induction cols as [|j cols IH]; simpl.
  - ring.
  - rewrite inject_Z_plus, inject_Z_mult, IH. ring.
Qed.

Lemma os_eval_shift n rows r x t :
  (os_eval n (fun j => x j + t * inject_Z (os_dir rows j)) r
    == os_eval n x r + t * inject_Z (os_slope (Zrange 0%Z n) rows r))%Q.
Proof. unfold os_eval. rewrite os_sum_shift. ring. Qed.

Lemma os_finite_upper (rows : list build_row_snapshot) (value : build_row_snapshot -> Q) :
  exists t, (0 <= t)%Q /\ forall r, In r rows -> (value r <= t)%Q.
Proof.
  induction rows as [|r rows [u [Hu Hupper]]].
  - exists 0%Q; split; [apply Qle_refl|contradiction].
  - exists (Qabs (value r) + u)%Q.
    pose proof (Qabs_nonneg (value r)) as Ha.
    split.
    + change ((0 + 0) <= Qabs (value r) + u)%Q.
      apply Qplus_le_compat; assumption.
    + intros r' [<-|Hr'].
      * setoid_replace (value r) with (value r + 0)%Q at 1 by ring.
        apply Qplus_le_compat; [apply Qle_Qabs|exact Hu].
      * setoid_replace (value r') with (0 + value r')%Q at 1 by ring.
        apply Qplus_le_compat; [exact Ha|apply Hupper; exact Hr'].
Qed.

(* Extend any witness on the retained rows by a sufficiently large single
   shift. All removed row slopes are integers at most -1, so a finite upper
   bound on original row values suffices as the shift distance. *)
Lemma os_extend_witness n rows x :
  (forall r, In r (os_kept n rows) -> (os_eval n x r <= 0)%Q) ->
  exists y : Z -> Q, forall r, In r rows -> (os_eval n y r <= 0)%Q.
Proof.
  intro Hkept.
  destruct (os_finite_upper rows (os_eval n x)) as [t [Ht Hupper]].
  exists (fun j => (x j + t * inject_Z (os_dir rows j))%Q).
  intros r Hr. rewrite os_eval_shift.
  destruct (forallb (os_keep_col rows r) (Zrange 0%Z n)) eqn:Hkeep.
  - rewrite os_slope_kept by exact Hkeep. simpl.
    specialize (Hkept r ltac:(unfold os_kept; apply filter_In; auto)).
    rewrite Qmult_0_r, Qplus_0_r. exact Hkept.
  - pose proof (os_slope_removed _ _ _ Hr Hkeep) as Hslope.
    assert (Hq : (inject_Z (os_slope (Zrange 0%Z n) rows r) <= inject_Z (-1))%Q).
    { rewrite <- Zle_Qle; lia. }
    pose proof (Qmult_le_compat_r _ _ t Hq Ht) as Hscaled.
    specialize (Hupper r Hr). change (inject_Z (-1)) with (-1)%Q in Hscaled.
    rewrite (Qmult_comm t).
    eapply Qle_trans.
    + apply Qplus_le_compat; [exact Hupper|exact Hscaled].
    + setoid_replace (t + -1*t)%Q with 0%Q by ring. apply Qle_refl.
Qed.

Lemma os_eval_as_constraint n x r :
  let c := list_Constraint (build_row_entries r) in
  (os_eval n x r == inject_Z (coef_Znth 0%Z c 0%Z) +
    fold_right Qplus 0
      (map (fun j => inject_Z (coef_Znth (j+1)%Z c 0%Z) * x j)
           (Zrange 0%Z n)))%Q.
Proof.
  destruct r as [p next [|c cs]]; [|reflexivity].
  unfold os_eval, os_coef, coef_Znth, Constraint_list, list_Constraint.
  simpl. apply Qplus_comp; [reflexivity|].
  induction (Zrange 0 n) as [|j js IH]; [reflexivity|].
  simpl; apply Qplus_comp; [|exact IH].
  apply Qmult_comp; [|reflexivity].
  unfold Znth.
  rewrite (nth_overflow [] 0 (n:=Z.to_nat (j+1))) by (simpl; lia).
  destruct (Z.to_nat (j+1)) as [|k]; [reflexivity|].
  destruct k; reflexivity.
Qed.

(* The indexed public feasibility relation and the membership form checked
   along the selected rows express exactly the same rational constraints. *)
Lemma os_feasible_members n rows :
  sx_rationally_feasible n (Zlength rows) (build_matrix rows) <->
  exists x : Z -> Q, forall r, In r rows -> (os_eval n x r <= 0)%Q.
Proof.
  unfold sx_rationally_feasible. split.
  - intros [x Hx]. exists x. intros r Hr.
    apply In_nth_error in Hr. destruct Hr as [k Hk].
    assert (Hrange : 0 <= Z.of_nat k < Zlength rows).
    { rewrite Zlength_correct. split; [lia|].
      apply Nat2Z.inj_lt, nth_error_Some. rewrite Hk. discriminate. }
    specialize (Hx (Z.of_nat k) Hrange).
    assert (Hmatrix : Znth (Z.of_nat k) (build_matrix rows) (list_Constraint nil)
                  = list_Constraint (build_row_entries r)).
    { unfold Znth, build_matrix. rewrite Nat2Z.id.
      apply nth_error_nth. rewrite nth_error_map, Hk. reflexivity. }
    rewrite Hmatrix in Hx. rewrite os_eval_as_constraint. exact Hx.
  - intros [x Hx]. exists x. intros i Hi.
    set (r := Znth i rows default_build_row_snapshot).
    assert (Hnat : (Z.to_nat i < List.length rows)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. lia. }
    assert (Hr : In r rows) by (unfold r, Znth; apply nth_In; exact Hnat).
    specialize (Hx r Hr).
    replace (Znth i (build_matrix rows) (list_Constraint nil))
      with (list_Constraint (build_row_entries r)).
    + rewrite <- (os_eval_as_constraint n x r). exact Hx.
    + unfold r, Znth, build_matrix.
      symmetry.
      exact (map_nth (fun row => list_Constraint (build_row_entries row))
        rows default_build_row_snapshot (Z.to_nat i)).
Qed.

Lemma os_feasible_iff n rows :
  sx_rationally_feasible n (Zlength (os_kept n rows))
    (build_matrix (os_kept n rows)) <->
  sx_rationally_feasible n (Zlength rows) (build_matrix rows).
Proof.
  rewrite !os_feasible_members. split.
  - intros [x Hx]. exact (os_extend_witness n rows x Hx).
  - intros [x Hx]. exists x. intros r Hr.
    apply Hx. unfold os_kept in Hr. apply filter_In in Hr. tauto.
Qed.

(* Temporary packed nodes use the selected Arch32 two-pointer layout. *)
Definition os_node_layout : Prop :=
  sizeof("InequList") = 8 /\
  forall p : Z, &(p # "InequList" ->ₛ "coef") = p /\
                &(p # "InequList" ->ₛ "next") = p + 4.

Definition os_zeros n := repeat 0 (Z.to_nat n).

(* The temporary chain changes only next; original snapshots remain intact. *)
Fixpoint os_shadows (base i : Z) (rows : list build_row_snapshot)
  : list build_row_snapshot :=
  match rows with
  | [] => []
  | r :: rs =>
    {| build_row_coefficients := build_row_coefficients r;
       build_row_entries := build_row_entries r;
       build_row_next := match rs with
                         | [] => 0
                         | _ :: _ => base + (i + 1) * sizeof("InequList")
                         end |} :: os_shadows base (i+1) rs
  end.

Lemma os_shadows_length base i rows :
  Zlength (os_shadows base i rows) = Zlength rows.
Proof.
  revert i. induction rows; intro i; [reflexivity|].
  simpl. rewrite !Zlength_cons, IHrows. reflexivity.
Qed.

Lemma os_shadows_matrix base i rows :
  build_matrix (os_shadows base i rows) = build_matrix rows.
Proof.
  revert i. induction rows; intro i; [reflexivity|].
  change (list_Constraint (build_row_entries a) ::
    build_matrix (os_shadows base (i+1) rows) =
    list_Constraint (build_row_entries a) :: build_matrix rows).
  rewrite IHrows. reflexivity.
Qed.

(* The temporary link array owns fields but never separately owns payloads. *)
Fixpoint os_links (p tail : Z) (rows : list build_row_snapshot) : Assertion :=
  match rows with
  | [] => “ p = tail ” && emp
  | r :: rs =>
    “ p <> 0 ” &&
    (&(p # "InequList" ->ₛ "coef") # Ptr |-> build_row_coefficients r) **
    (&(p # "InequList" ->ₛ "next") # Ptr |-> build_row_next r) **
    os_links (build_row_next r) tail rs
  end.

(* Original node fields remain owned throughout the call. At the call
   boundary only the coefficient resources of kept rows move to build. *)
Fixpoint os_unborrowed (keep : build_row_snapshot -> bool)
    (p count : Z) (rows : list build_row_snapshot) : Assertion :=
  match rows with
  | [] => “ p = 0 ” && emp
  | r :: rs =>
    “ p <> 0 /\ build_row_coefficients r <> 0 ” &&
    (&(p # "InequList" ->ₛ "coef") # Ptr |-> build_row_coefficients r) **
    (&(p # "InequList" ->ₛ "next") # Ptr |-> build_row_next r) **
    (if keep r then emp
     else MpzArray.full (build_row_coefficients r) count (build_row_entries r)) **
    os_unborrowed keep (build_row_next r) count rs
  end.

Definition os_unborrowed_kept n p rows :=
  os_unborrowed (fun r => forallb (os_keep_col rows r) (Zrange 0 n)) p (n+1) rows.

Definition os_size_relation (s z : Z) : Prop := Z.sgn s = Z.sgn z.

(* The size cell is exposed separately for the C read. This assertion
   retains exactly the remaining header fields and storage of store_Z. *)
Definition os_mpz_without_size (x n size : Z) : Assertion :=
  EX (ptr : Z) (cap : Z),
    “ Z.abs size <= cap ” && “ same_sign n size ” &&
    mpd_store_Z_compact UINT_MOD ptr (Z.abs n) (Z.abs size) **
    UIntArray.undef_seg ptr (Z.abs size) cap **
    (&(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap) **
    (&(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr).

Lemma os_mpz_size_sign size n :
  same_sign n size ->
  (0 < size <-> 0 < n) ->
  (size = 0 <-> n = 0) ->
  os_size_relation size n.
Proof.
  unfold same_sign, os_size_relation.
  intros Hsign Hpositive Hzero.
  destruct (Z_lt_ge_dec size 0) as [Hneg|Hnonneg].
  - rewrite !Z.sgn_neg; lia.
  - destruct (Z.eq_dec size 0) as [Heq|Hneq].
    + assert (n = 0) by tauto. subst. reflexivity.
    + rewrite !Z.sgn_pos; lia.
Qed.

Lemma os_mpz_size_open x n :
  store_Z x n |--
  EX size : Z, “ os_size_relation size n ” &&
    (&(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size) **
    os_mpz_without_size x n size.
Proof.
  unfold store_Z.
  Intros ptr size cap.
  prop_apply (pivot_mpz_compact_sign ptr n size ltac:(tauto)).
  Intros_p Hsign.
  Exists size.
  split_pure_spatial.
  - unfold os_mpz_without_size. Exists ptr cap.
    split_pure_spatial; [sepcon_assoc_change; cancel|].
    split_pures; dump_pre_spatial; tauto.
  - dump_pre_spatial. apply os_mpz_size_sign; tauto.
Qed.

Lemma os_mpz_size_close x n size :
  (&(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size) **
  os_mpz_without_size x n size |-- store_Z x n.
Proof.
  unfold os_mpz_without_size, store_Z.
  Intros ptr cap.
  Exists ptr size cap.
  split_pure_spatial; [sepcon_assoc_change; cancel|].
  split_pures; dump_pre_spatial; tauto.
Qed.


(* Natural exact sign information for loops: advanced columns have already
   consumed the current row, and all other columns read the previous prefix. *)
Definition os_masks_at (n i j : Z) (rows : list build_row_snapshot)
    (mask : list Z) : Prop :=
  forall v, 0 <= v < n ->
    Znth v mask 0 = os_mask v (sublist 0 (if v <? j then i+1 else i) rows).

Definition os_checked_prefix (rows : list build_row_snapshot)
    (r : build_row_snapshot) (j : Z) : Prop :=
  forall k, 0 <= k < j -> os_keep_col rows r k = true.

Definition os_kept_prefix n i rows :=
  filter (fun r => forallb (os_keep_col rows r) (Zrange 0 n))
    (sublist 0 i rows).

Definition os_temp_head base kept : Z :=
  if Z.eqb kept 0 then 0 else base.

Lemma os_transfer_frame P Q R S T (H : Q |-- S) :
    (P |-- Q ** R) -> (S ** R |-- T) -> P |-- T.
Proof.
  intros Hpre Hpost.
  sep_apply Hpre.
  sep_apply H.
  exact Hpost.
Qed.

Lemma os_transfer keep base i p q count rows :
  (build_input_segment p 0 count rows **
   os_links q 0 (os_shadows base i (filter keep rows)))
  --||--
  (os_unborrowed keep p count rows **
   build_input_segment q 0 count (os_shadows base i (filter keep rows))).
Proof.
  revert i p q.
  induction rows as [|r rs IH]; intros i p q.
  - reflexivity.
  - cbn [filter]. destruct (keep r) eqn:Hkeep.
    + cbn [os_shadows build_input_segment os_links os_unborrowed].
      rewrite Hkeep.
      set (next := match filter keep rs with
                   | [] => 0
                   | _ :: _ => base + (i + 1) * sizeof("InequList")
                   end).
      cbn [build_row_next build_row_entries build_row_coefficients].
      set (F := (&(p # "InequList" ->ₛ "coef") # Ptr |-> build_row_coefficients r) **
        (&(p # "InequList" ->ₛ "next") # Ptr |-> build_row_next r) **
        (&(q # "InequList" ->ₛ "coef") # Ptr |-> build_row_coefficients r) **
        (&(q # "InequList" ->ₛ "next") # Ptr |-> next) **
        MpzArray.full (build_row_coefficients r) count (build_row_entries r)).
      split.
      * Intros_p Horiginal. Intros_p Hshadow.
        split_pure_spatial.
        -- eapply (os_transfer_frame _ _ F _ _
             (proj1 (IH (i+1) (build_row_next r) next))); unfold F; asrt_simpl; sepcon_assoc_change; cancel.
        -- split_pures; dump_pre_spatial; tauto.
      * Intros_p Horiginal. Intros_p Hshadow.
        split_pure_spatial.
        -- eapply (os_transfer_frame _ _ F _ _
             (proj2 (IH (i+1) (build_row_next r) next))); unfold F; asrt_simpl; sepcon_assoc_change; cancel.
        -- split_pures; dump_pre_spatial; tauto.
    + cbn [build_input_segment os_unborrowed]. rewrite Hkeep.
      set (F := (&(p # "InequList" ->ₛ "coef") # Ptr |-> build_row_coefficients r) **
        (&(p # "InequList" ->ₛ "next") # Ptr |-> build_row_next r) **
        MpzArray.full (build_row_coefficients r) count (build_row_entries r)).
      split.
      * Intros_p Horiginal.
        split_pure_spatial.
        -- eapply (os_transfer_frame _ _ F _ _
             (proj1 (IH i (build_row_next r) q))); unfold F; asrt_simpl; sepcon_assoc_change; cancel.
        -- split_pures; dump_pre_spatial; tauto.
      * Intros_p Horiginal.
        split_pure_spatial.
        -- eapply (os_transfer_frame _ _ F _ _
             (proj2 (IH i (build_row_next r) q))); unfold F; asrt_simpl; sepcon_assoc_change; cancel.
        -- split_pures; dump_pre_spatial; tauto.
Qed.

Lemma os_raw_node p i :
  os_node_layout ->
  0 <= p + i * sizeof("InequList") ->
  (4 | p + i * sizeof("InequList")) ->
  p + i * sizeof("InequList") + 7 <= addr_max_unsigned ->
  UCharArray.undef_seg p (i * sizeof("InequList"))
    ((i + 1) * sizeof("InequList"))
  |-- undef_store_ptr (&(((p + (i * sizeof("InequList")))) # "InequList" ->ₛ "coef")) **
      undef_store_ptr (&(((p + (i * sizeof("InequList")))) # "InequList" ->ₛ "next")).
Proof.
  intros [Hstride Hfields].
  rewrite Hstride. intros Hnonneg Halign Hlast.
  destruct (Hfields (p + i * 8)) as [Hcoef Hnext].
  rewrite Hcoef, Hnext.
  assert (Hvalid : forall off, 0 <= off <= 4 -> (4 | off) ->
    valid_object (p + i * 8 + off) 4 4).
  {
    intros off Hoffset Hdiv.
    unfold valid_object, valid_addr_range, aligned.
    repeat split; try lia.
    apply Z.mod_divide; [lia|].
    apply Z.divide_add_r; assumption.
  }
  replace ((i + 1) * 8) with ((i * 8 + 4) + 4) by lia.
  sep_apply (UCharArray.undef_seg_split_to_undef_seg p (i * 8)
    (i * 8 + 4) (i * 8 + 4 + 4) ltac:(lia)).
  sep_apply (uchar_segment_four_raw__initialization_loop p
    (i * 8) (i * 8 + 4) ltac:(lia)).
  sep_apply (uchar_segment_four_raw__initialization_loop p
    (i * 8 + 4) (i * 8 + 4 + 4) ltac:(lia)).
  replace (p + (i * 8 + 4)) with (p + i * 8 + 4) by lia.
  assert (Hfirst : valid_object (p + i * 8) 4 4).
  {
    replace (p + i * 8) with (p + i * 8 + 0) by lia.
    apply Hvalid; [lia | exists 0; lia].
  }
  assert (Hsecond : valid_object (p + i * 8 + 4) 4 4)
    by (apply Hvalid; [lia | exists 1; lia]).
  sep_apply (raw_four_to_ptr__initialization_loop _ Hfirst).
  sep_apply (raw_four_to_ptr__initialization_loop _ Hsecond).
  cancel.
Qed.


Lemma os_filter_reject__packed_nodes n m rows mask r j sz :
  m = Zlength rows -> os_masks_at n m 0 rows mask -> 0 <= j < n ->
  (Znth j mask 0 = 1 \/ Znth j mask 0 = 2) ->
  os_size_relation sz (os_coef r j) -> sz <> 0 ->
  forallb (os_keep_col rows r) (Zrange 0 n) = false.
Proof.
  intros Hm Hmasks Hj Hmask Hsize Hsz.
  specialize (Hmasks j Hj).
  assert (Hj0 : (j <? 0) = false) by (apply Z.ltb_ge; lia).
  rewrite Hj0, (sublist_self rows m Hm) in Hmasks.
  destruct (forallb (os_keep_col rows r) (Zrange 0 n)) eqn:Hkeep; [|reflexivity].
  apply forallb_forall with (x := j) in Hkeep; [|apply In_Zrange; exact Hj].
  apply os_keep_col_bit in Hkeep.
  assert (Hcoef : os_coef r j <> 0).
  { intro Hz. unfold os_size_relation in Hsize. rewrite Hz in Hsize.
    change (Z.sgn sz = 0) in Hsize. exact (Hsz (proj1 (Z.sgn_null_iff sz) Hsize)). }
  lia.
Qed.
Lemma os_kept_prefix_step__packed_nodes n i rows :
  0 <= i < Zlength rows ->
  os_kept_prefix n (i+1) rows =
    (os_kept_prefix n i rows ++
    filter (fun r => forallb (os_keep_col rows r) (Zrange 0 n)) [build_row_at rows i])%list.
Proof.
  intro Hi. unfold os_kept_prefix.
  rewrite (build_prefix_snoc__build_initial_table rows i Hi), filter_app.
  reflexivity.
Qed.
Lemma os_filter_accept__packed_nodes n rows r :
  os_checked_prefix rows r n ->
  forallb (os_keep_col rows r) (Zrange 0 n) = true.
Proof.
  intro Hchecked. apply forallb_forall.
  intros j Hj. apply Hchecked, In_Zrange, Hj.
Qed.
Lemma os_empty_if_length_zero__packed_nodes (xs : list build_row_snapshot) :
  Zlength xs = 0 -> xs = [].
Proof.
  destruct xs; [reflexivity|].
  rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia.
Qed.
Lemma os_links_append__packed_nodes p middle tail xs ys :
  os_links p middle xs ** os_links middle tail ys |--
  os_links p tail (xs ++ ys)%list.
Proof.
  revert p. induction xs as [|x xs IH]; intro p; cbn [os_links app].
  - Intros_p Heq. subst p. cancel.
  - Intros_p Hnonnull. sep_apply (IH (build_row_next x)).
    split_pure_spatial; [cancel | dump_pre_spatial; exact Hnonnull].
Qed.
Lemma os_shadows_cons__packed_nodes base i x y ys :
  os_shadows base i (x :: y :: ys) =
  {| build_row_coefficients := build_row_coefficients x;
     build_row_entries := build_row_entries x;
     build_row_next := base + (i + 1) * sizeof("InequList") |} ::
    os_shadows base (i + 1) (y :: ys).
Proof. reflexivity. Qed.
Lemma os_shadows_snoc__packed_nodes base i xs r :
  0 < Zlength xs ->
  os_shadows base i (xs ++ [r])%list =
    (sublist 0 (Zlength xs - 1) (os_shadows base i xs) ++
      [{| build_row_coefficients := build_row_coefficients (build_row_at xs (Zlength xs - 1));
          build_row_entries := build_row_entries (build_row_at xs (Zlength xs - 1));
          build_row_next := base + (i + Zlength xs) * sizeof("InequList") |};
       {| build_row_coefficients := build_row_coefficients r;
          build_row_entries := build_row_entries r;
          build_row_next := 0 |}])%list.
Proof.
  revert i. induction xs as [|x xs IH]; intros i Hpositive.
  - rewrite Zlength_nil in Hpositive. lia.
  - destruct xs as [|y ys].
    + rewrite Zlength_cons, Zlength_nil.
      replace (0 + 1 - 1) with 0 by lia.
      replace (i + (0 + 1)) with (i + 1) by lia.
      reflexivity.
    + rewrite Zlength_cons.
      rewrite <- (Z.add_1_r (Zlength (y :: ys))).
      replace (Zlength (y :: ys) + 1 - 1) with (Zlength (y :: ys)) by lia.
      assert (Hpos : 0 < Zlength (y :: ys)).
      { rewrite Zlength_cons. pose proof (Zlength_nonneg ys). lia. }
      unfold build_row_at at 1 2.
      rewrite !Znth_cons by lia.
      change ((x :: y :: ys) ++ [r])%list with (x :: y :: (ys ++ [r]))%list.
      rewrite (os_shadows_cons__packed_nodes base i x y (ys ++ [r])%list),
        (os_shadows_cons__packed_nodes base i x y ys).
      rewrite sublist_cons1 by lia.
      cbn [app].
      change (y :: ys ++ [r])%list with ((y :: ys) ++ [r])%list.
      rewrite (IH (i+1) Hpos).
      replace (i + (Zlength (y :: ys) + 1)) with (i + 1 + Zlength (y :: ys)) by lia.
      reflexivity.
Qed.
Lemma os_links_cons__packed_nodes p tail r rs :
  os_links p tail (r :: rs) =
    “ p <> 0 ” &&
    (&(p # "InequList" ->ₛ "coef") # Ptr |-> build_row_coefficients r) **
    (&(p # "InequList" ->ₛ "next") # Ptr |-> build_row_next r) **
    os_links (build_row_next r) tail rs.
Proof. reflexivity. Qed.
Lemma os_links_last_split__packed_nodes base i xs :
  0 < Zlength xs ->
  os_links (base+i*sizeof("InequList")) 0 (os_shadows base i xs) |--
  os_links (base+i*sizeof("InequList"))
    (base+(i+Zlength xs-1)*sizeof("InequList"))
    (sublist 0 (Zlength xs - 1) (os_shadows base i xs)) **
  (&(((base + ((i + Zlength xs - 1) * sizeof("InequList")))) # "InequList" ->ₛ "coef")
    # Ptr |-> build_row_coefficients (build_row_at xs (Zlength xs-1))) **
  (&(((base + ((i + Zlength xs - 1) * sizeof("InequList")))) # "InequList" ->ₛ "next") # Ptr |-> 0).
Proof.
  revert i. induction xs as [|x xs IH]; intros i Hpositive.
  - rewrite Zlength_nil in Hpositive. lia.
  - destruct xs as [|y ys].
    + rewrite Zlength_cons, Zlength_nil.
      replace (Z.succ 0 - 1) with 0 by reflexivity.
      replace (i + Z.succ 0 - 1) with i by lia.
      unfold build_row_at. rewrite Znth0_cons, Zsublist_nil by lia.
      cbn [os_shadows os_links build_row_coefficients build_row_next].
      cbn [os_links].
      Intros_p Hnonnull. Intros_p Hzero.
      asrt_simpl. split_pure_spatial; [cancel | dump_pre_spatial; reflexivity].
    + rewrite Zlength_cons.
      rewrite <- (Z.add_1_r (Zlength (y :: ys))).
      replace (Zlength (y :: ys) + 1 - 1) with (Zlength (y :: ys)) by lia.
      assert (Hpos : 0 < Zlength (y :: ys)).
      { rewrite Zlength_cons. pose proof (Zlength_nonneg ys). lia. }
      unfold build_row_at at 1. rewrite Znth_cons by lia.
      rewrite (os_shadows_cons__packed_nodes base i x y ys).
      rewrite sublist_cons1 by lia.
      rewrite (os_links_cons__packed_nodes (base+i*sizeof("InequList")) 0).
      rewrite (os_links_cons__packed_nodes (base+i*sizeof("InequList"))
        (base+(i+(Zlength (y :: ys)+1)-1)*sizeof("InequList"))).
      cbn [build_row_next build_row_coefficients].
      Intros_p Hnonnull.
      sep_apply (IH (i+1) Hpos).
      replace (i + (Zlength (y :: ys) + 1) - 1)
        with (i + 1 + Zlength (y :: ys) - 1) by lia.
      cbn [build_row_next build_row_entries build_row_coefficients].
      unfold build_row_at. split_pure_spatial; [asrt_simpl; cancel | dump_pre_spatial; exact Hnonnull].
Qed.
Lemma os_open_packed_slot__packed_nodes p i m :
  os_node_layout ->
  0 <= i < m -> 0 <= p -> (4 | p) ->
  UCharArray.undef_seg p (i * sizeof("InequList")) (m * sizeof("InequList"))
  |-- undef_store_ptr (&(((p + (i * sizeof("InequList")))) # "InequList" ->ₛ "coef")) **
      undef_store_ptr (&(((p + (i * sizeof("InequList")))) # "InequList" ->ₛ "next")) **
      UCharArray.undef_seg p ((i+1) * sizeof("InequList")) (m * sizeof("InequList")).
Proof.
  intros Hlayout Hi Hp Hdiv.
  pose proof (proj1 Hlayout) as Hstride.
  set (stride := sizeof("InequList")).
  assert (Hstride' : stride = 8) by exact Hstride.
  assert (Hsplit : i * stride <= (i+1) * stride <= m * stride) by lia.
  sep_apply (UCharArray.undef_seg_split_to_undef_seg p
    (i*stride) ((i+1)*stride) (m*stride) Hsplit).
  set (last := (i+1)*stride-1).
  assert (Hslot : i * stride <= last < (i+1)*stride) by (unfold last; lia).
  sep_apply (UCharArray.undef_seg_split_to_undef_missing_i p
    (i*stride) last ((i+1)*stride) Hslot).
  pose proof (valid_undef_store_uchar (p + last * sizeof(UCHAR))) as Hbyte.
  change (StoreUCharAsElement.undefstoreA p last |--
    “ valid_object (p + last * sizeof(UCHAR)) (sizeof(CHAR)) 1 ”) in Hbyte.
  prop_apply Hbyte.
  Intros_p Hvalid.
  pose proof (UCharArray.undef_missing_i_merge_to_undef_seg p
    (i*stride) last ((i+1)*stride) Hslot) as Hmerge.
  change (StoreUCharAsElement.undefstoreA p last **
    UCharArray.undef_missing_i p last (i*stride) ((i+1)*stride) |--
    UCharArray.undef_seg p (i*stride) ((i+1)*stride)) in Hmerge.
  sep_apply Hmerge.
  assert (Hlast : p + i * stride + 7 <= addr_max_unsigned).
  { unfold valid_object, valid_addr_range, last in Hvalid.
    rewrite sizeof_uchar, sizeof_char in Hvalid. lia. }
  assert (Halign : (4 | p + i * stride)).
  { apply Z.divide_add_r; [exact Hdiv|].
    rewrite Hstride'. exists (2*i). lia. }
  unfold stride in Halign, Hlast |- *.
  sep_apply (os_raw_node p i Hlayout ltac:(lia) Halign Hlast).
  cancel.
Qed.
Lemma os_ptr_as_uchar__build_transfer p v :
  store_ptr p v |-- UCharArray.undef_seg p 0 4.
Proof.
  sep_apply (store_ptr_undef_store_ptr p v).
  change (undef_store_ptr p) with (undef_store_uint p).
  rewrite (undef_store_uint_undef_store_char p).
  Intros_p Halign.
  rewrite (UCharArray.undef_seg_unfold p 0 4 ltac:(lia)).
  rewrite (UCharArray.undef_seg_unfold p 1 4 ltac:(lia)).
  rewrite (UCharArray.undef_seg_unfold p 2 4 ltac:(lia)).
  rewrite (UCharArray.undef_seg_unfold p 3 4 ltac:(lia)).
  rewrite (UCharArray.undef_seg_empty p 4).
  unfold StoreUCharAsElement.undefstoreA.
  rewrite sizeof_uchar.
  replace (p + 0 * 1) with p by lia.
  replace (p + 1 * 1) with (p + 1) by lia.
  replace (p + 2 * 1) with (p + 2) by lia.
  replace (p + 3 * 1) with (p + 3) by lia.
  change (undef_store_uchar p) with (undef_store_char p).
  change (undef_store_uchar (p + 1)) with (undef_store_char (p + 1)).
  change (undef_store_uchar (p + 2)) with (undef_store_char (p + 2)).
  change (undef_store_uchar (p + 3)) with (undef_store_char (p + 3)).
  asrt_simpl. sepcon_assoc_change. cancel.
Qed.
Lemma os_ptr_as_uchar_at__build_transfer base lo v :
  store_ptr (base + lo) v |-- UCharArray.undef_seg base lo (lo + 4).
Proof.
  rewrite UCharArray.undef_seg_0_shift.
  unfold StoreUCharAsElement.sizeA.
  rewrite sizeof_uchar.
  replace (lo + 4 - lo) with 4 by lia.
  replace (base + lo * 1) with (base + lo) by lia.
  apply os_ptr_as_uchar__build_transfer.
Qed.
Lemma os_links_as_uchar__build_transfer base i xs :
  (0 < Zlength xs -> os_node_layout) ->
  os_links (match xs with nil => 0 | _ :: _ => base + i * sizeof("InequList") end)
    0 (os_shadows base i xs)
  |-- UCharArray.undef_seg base (i * sizeof("InequList"))
    ((i + Zlength xs) * sizeof("InequList")).
Proof.
  revert i.
  induction xs as [|r rs IH]; intros i Hlayout.
  - rewrite Zlength_nil, Z.add_0_r.
    cbn [os_shadows os_links].
    Intros_p Hnull.
    rewrite UCharArray.undef_seg_empty.
    cancel.
  - pose proof (Zlength_nonneg rs) as Hlen.
    pose proof (IH (i + 1) ltac:(intros Hpositive; apply Hlayout; rewrite Zlength_cons; lia))
      as Htail.
    destruct (Hlayout ltac:(rewrite Zlength_cons; lia)) as [Hstride Hfields].
    cbn [os_shadows os_links build_row_coefficients build_row_next].
    rewrite Hstride in Htail |- *.
    destruct (Hfields (base + i * 8)) as [Hcoef Hnext].
    rewrite Hcoef, Hnext.
    Intros_p Hnonnull.
    replace (base + i * 8 + 4) with (base + (i * 8 + 4)) by lia.
    sep_apply (os_ptr_as_uchar_at__build_transfer base (i * 8)
      (build_row_coefficients r)).
    sep_apply (os_ptr_as_uchar_at__build_transfer base (i * 8 + 4)
      (match rs with nil => 0 | _ :: _ => base + (i + 1) * 8 end)).
    sep_apply Htail.
    rewrite Zlength_cons.
    replace ((i + Z.succ (Zlength rs)) * 8) with ((i + 1 + Zlength rs) * 8) by lia.
    replace (i * 8 + 4 + 4) with ((i + 1) * 8) by lia.
    sep_apply (UCharArray.undef_seg_merge_to_undef_seg base (i * 8)
      (i * 8 + 4) ((i + 1) * 8) ltac:(lia)).
    sep_apply (UCharArray.undef_seg_merge_to_undef_seg base (i * 8)
      ((i + 1) * 8) ((i + 1 + Zlength rs) * 8) ltac:(lia)).
    cancel.
Qed.
Lemma os_recover_input__build_transfer n m kept head nodes rows :
  kept = Zlength (os_kept n rows) ->
  kept <= m ->
  (0 < m -> os_node_layout) ->
  os_unborrowed_kept n head rows **
  build_input_segment (os_temp_head nodes kept) 0 (n + 1)
    (os_shadows nodes 0 (os_kept n rows)) **
  UCharArray.undef_seg nodes (kept * sizeof("InequList")) (m * sizeof("InequList"))
  |-- build_input_segment head 0 (n + 1) rows **
      UCharArray.undef_full nodes (m * sizeof("InequList")).
Proof.
  intros Hkept Hbound Hlayout.
  sep_apply (proj2 (os_transfer (fun r => forallb (os_keep_col rows r) (Zrange 0 n))
    nodes 0 head (os_temp_head nodes kept) (n + 1) rows)).
  pose proof (os_links_as_uchar__build_transfer nodes 0 (os_kept n rows)
    ltac:(intros Hpositive; apply Hlayout; lia)) as Hlinks.
  assert (Hhead : (match os_kept n rows with nil => 0
                    | _ :: _ => nodes + 0 * sizeof("InequList") end) =
                  os_temp_head nodes kept).
  {
    unfold os_temp_head.
    destruct (os_kept n rows) as [|r rs].
    - rewrite Zlength_nil in Hkept. rewrite Hkept. reflexivity.
    - rewrite Zlength_cons in Hkept.
      pose proof (Zlength_nonneg rs).
      rewrite (proj2 (Z.eqb_neq kept 0) ltac:(lia)).
      lia.
  }
  rewrite Hhead, <- Hkept, Z.mul_0_l, Z.add_0_l in Hlinks.
  sep_apply Hlinks.
  assert (Hbyte : 0 <= kept * sizeof("InequList") <= m * sizeof("InequList")).
  {
    pose proof (Zlength_nonneg (os_kept n rows)).
    destruct (Z.eq_dec m 0) as [->|Hnonzero].
    - assert (kept = 0) by lia. subst kept. rewrite Z.mul_0_l. lia.
    - destruct (Hlayout ltac:(lia)) as [Hstride _]. rewrite Hstride. lia.
  }
  pose proof (UCharArray.undef_seg_merge_to_undef_full nodes 0
    (kept * sizeof("InequList")) (m * sizeof("InequList")) Hbyte) as Hjoin.
  rewrite Z.mul_0_l, Z.add_0_r, Z.sub_0_r in Hjoin.
  sep_apply Hjoin.
  cancel.
Qed.
Lemma os_masks_step__sign_masks n i j rows masks sz :
  0 <= i < Zlength rows ->
  0 <= j < n ->
  Zlength masks = n ->
  os_masks_at n i j rows masks ->
  os_size_relation sz (os_coef (build_row_at rows i) j) ->
  os_masks_at n i (j + 1) rows
    (if sz <? 0 then
       replace_Znth j (Z.lor (unsigned_last_nbits (Znth j masks 0) 8) 2) masks
     else if 0 <? sz then
       replace_Znth j (Z.lor (unsigned_last_nbits (Znth j masks 0) 8) 1) masks
     else masks).
Proof.
  intros Hi Hj Hlength Hmask Hsign v Hv.
  specialize (Hmask v Hv).
  destruct (Z.eq_dec v j) as [->|Hdistinct].
  - rewrite Z.ltb_irrefl in Hmask.
    assert (Hadvance : (j <? j + 1) = true) by (apply Z.ltb_lt; lia).
    rewrite Hadvance, build_prefix_snoc__build_initial_table by exact Hi.
    assert (Hbits :
      (sz <? 0) = (os_coef (build_row_at rows i) j <? 0) /\
      (0 <? sz) = (0 <? os_coef (build_row_at rows i) j)).
    { unfold os_size_relation in Hsign.
      destruct sz, (os_coef (build_row_at rows i) j); cbn in *;
        split; congruence. }
    destruct Hbits as [Hneg Hpos].
    unfold os_mask, os_pos, os_neg in Hmask |- *.
    rewrite !existsb_app. cbn [existsb].
    rewrite <- Hneg, <- Hpos.
    destruct (sz <? 0) eqn:Hnegative.
    + assert (Hz : (0 <? sz) = false) by
          (apply Z.ltb_ge; apply Z.ltb_lt in Hnegative; lia).
      rewrite Hz, Znth_replace_Znth_Same, Hmask by lia.
      destruct (existsb (fun r => 0 <? os_coef r j) (sublist 0 i rows)),
        (existsb (fun r => os_coef r j <? 0) (sublist 0 i rows));
        reflexivity.
    + destruct (0 <? sz) eqn:Hpositive.
      * rewrite Znth_replace_Znth_Same, Hmask by lia.
        destruct (existsb (fun r => 0 <? os_coef r j) (sublist 0 i rows)),
          (existsb (fun r => os_coef r j <? 0) (sublist 0 i rows));
          reflexivity.
      * rewrite Hmask, !orb_false_r. reflexivity.
  - assert (Hadvance : (v <? j + 1) = (v <? j)).
    { destruct (v <? j) eqn:Hlt.
      - apply Z.ltb_lt in Hlt. apply Z.ltb_lt. lia.
      - apply Z.ltb_ge in Hlt. apply Z.ltb_ge. lia. }
    rewrite Hadvance, <- Hmask.
    destruct (sz <? 0), (0 <? sz);
      try rewrite Znth_replace_Znth_Diff by lia; reflexivity.
Qed.
