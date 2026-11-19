From Coq Require Import ZArith List QArith Lia.
From AUXLib Require Import ListLib.
From SumLib Require Import ZRange.
From SimpleC.SL Require Import IntLib.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_lib.
From SimpleC.EE.Applications_human.simplex_gmp_minimal Require Import
  build_fme_model_input_revision_lib sx_check_fme_model_lib
  violated_fme_model_selection_lib entering_fme_model_selection_lib pivot_fme_model_lib.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import
  build_one_sided_policy_opt_lib pivot_opt_lib.

Local Open Scope Z_scope.

(* All entries for original variables tested in this row are zero. *)
Definition sx_zero_prefix (row : build_row_snapshot) (j : Z) : Prop :=
  forall v, 0 <= v < j -> os_coef row v = 0.

Lemma sx_zero_prefix_start row : sx_zero_prefix row 0.
Proof. unfold sx_zero_prefix; lia. Qed.

Lemma sx_zero_prefix_step row j :
  sx_zero_prefix row j -> os_coef row j = 0 -> sx_zero_prefix row (j+1).
Proof.
  intros Hprefix Hzero v Hv.
  destruct (Z.eq_dec v j) as [->|Hneq]; [exact Hzero|].
  apply Hprefix; lia.
Qed.

(* A positive constant row contradicts every valuation of the original
   system, including the empty valuation when n is zero. *)
Lemma sx_positive_constant_infeasible n rows i :
  0 <= i < Zlength rows ->
  0 < Znth 0 (build_row_entries (build_row_at rows i)) 0 ->
  sx_zero_prefix (build_row_at rows i) n ->
  ~ sx_rationally_feasible n (Zlength rows) (build_matrix rows).
Proof.
  intros Hi Hpositive Hzero.
  rewrite os_feasible_members.
  intros [x Hx].
  specialize (Hx (build_row_at rows i)).
  unfold build_row_at in Hx, Hpositive, Hzero.
  specialize (Hx (Znth_In_Zlength _ _ _ Hi)).
  unfold os_eval in Hx.
  assert (Hsum : forall indices : list Z,
      (forall j, In j indices -> 0 <= j < n) ->
      (fold_right Qplus 0
        (map (fun j => (inject_Z (os_coef (Znth i rows default_build_row_snapshot) j)
          * x j)%Q) indices) == 0)%Q).
  { induction indices as [|v rest IH]; intros Hrange; simpl.
    - reflexivity.
    - rewrite (Hzero v (Hrange v (or_introl eq_refl))), Qmult_0_l, Qplus_0_l.
      apply IH. intros j Hj. apply Hrange. now right. }
  rewrite Hsum, Qplus_0_r in Hx.
  - change (inject_Z (Znth 0%Z (build_row_entries
        (Znth i rows default_build_row_snapshot)) 0%Z) <= inject_Z 0%Z)%Q in Hx.
    rewrite <- Zle_Qle in Hx. lia.
  - intros v Hv. now apply In_Zrange.
Qed.

(* Positive denominators, mutually inverse basis bookkeeping, and zero
   basic columns follow from the actual initialized table. *)
Lemma sx_initial_selection_basis n m k I D C A B R :
  0 <= n ->
  simplex_initial_table n m k I D C A B R ->
  selection_basis m k D A B R.
Proof.
  intros Hn [Hk [Hrows [Hprefix Hcoeff]]].
  split.
  - intros r Hr.
    destruct (Hrows r Hr) as [Hd [_ [Hb Hmap]]].
    rewrite Hb, Hd. split; [lia|]. split; [exact Hmap|lia].
  - split.
    + intros v Hv Hnonbasic.
      assert (Haux : n <= v).
      { destruct (Z_lt_ge_dec v n) as [Horiginal | Haux]; [|lia].
        exfalso. apply Hnonbasic. apply Hprefix. lia. }
      assert (Hr : 0 <= v - n < m) by lia.
      destruct (Hrows (v - n) Hr) as [_ [_ [Hb Hmap]]].
      replace (n + (v - n)) with v in Hb, Hmap by lia.
      rewrite Hmap. split; assumption.
    + intros r q Hr Hq.
      destruct (Hrows q Hq) as [_ [_ [Hb _]]].
      rewrite Hb, Hcoeff by lia.
      assert (Haux : (n + q <? n)%Z = false) by (apply Z.ltb_ge; lia).
      now rewrite Haux.
Qed.

Lemma sx_initial_selection_equations n m k I D C A B :
  simplex_initial_equations n m k I D C A B ->
  selection_equations n m k I D C A B.
Proof.
  intros Hequations x. split; intros Hrows r Hr.
  - apply (proj1 (Hequations r x Hr)), Hrows, Hr.
  - apply (proj2 (Hequations r x Hr)), Hrows, Hr.
Qed.

Lemma sx_pivot_preserves_selection_equations n m k I r e q
    D C A B R NB Df Cf Af Bf Rf NBf :
  selection_equations n m k I D C A B ->
  pivot_optimized_result m k r e q D C A B R NB Df Cf Af Bf Rf NBf ->
  selection_equations n m k I Df Cf Af Bf.
Proof.
  intros Hequations (_ & _ & _ & _ & _ & _ & _ & Hpivot) x.
  transitivity (pivot_table_equations m k D C A B x).
  - symmetry. exact (Hpivot x).
  - exact (Hequations x).
Qed.

(* Each break branch establishes the public result through the same
   stable-subsequence filtering equivalence. *)
Lemma sx_no_violated_filtered n rows m k D C A B R :
  m = Zlength (os_kept n rows) -> 0 <= n -> k = m+n -> k < UINT_MAX ->
  selection_basis m k D A B R ->
  selection_equations n m k (build_matrix (os_kept n rows)) D C A B ->
  first_positive_row n k (sublist n k R) (scan_row_values C) = UINT_MAX ->
  sx_check_result n (Zlength rows) (build_matrix rows) 0.
Proof.
  intros Hm Hn Hk Hmax Hbasis Hequations Hscan.
  pose proof (proj1 (valid_selection_no_positive_aux n k m D C A B R Hn Hbasis)
    Hscan) as Haux.
  pose proof (proj1 (Hequations (selection_basic_value D C R))) as Hinput.
  specialize (Hinput (selection_basic_satisfies_table__feasible_return
    m k UINT_MAX D C A B R (selection_basic_value D C R)
    ltac:(lia) Hmax Hbasis ltac:(reflexivity))).
  assert (Hfeasible : sx_rationally_feasible n (Zlength rows) (build_matrix rows)).
  { apply (proj1 (os_feasible_iff n rows)).
    rewrite <- Hm.
    exists (selection_basic_value D C R).
    intros r Hr. specialize (Hinput r Hr).
    cbv zeta in Hinput |- *. rewrite <- Hinput. apply Haux. lia. }
  unfold sx_check_result.
  split; [now left |].
  split.
  - split; [intros _; exact Hfeasible | intros _; reflexivity].
  - split; [discriminate | intros H; contradiction].
Qed.

Lemma sx_violated_blocked_filtered n rows m k D C A B R ret :
  m = Zlength (os_kept n rows) -> 0 <= n -> k = m+n ->
  selection_basis m k D A B R ->
  selection_equations n m k (build_matrix (os_kept n rows)) D C A B ->
  ret <> UINT_MAX ->
  ret = first_positive_row n k (sublist n k R) (scan_row_values C) ->
  entering_blocked_row n k ret A ->
  sx_check_result n (Zlength rows) (build_matrix rows) 1.
Proof.
  intros Hm Hn Hk Hbasis Hequations Hne Hscan Hblocked.
  destruct (valid_selection_first_aux n k m D C A B R ret Hn Hbasis Hne Hscan)
    as [Hrow [Haux [Hpositive _]]].
  assert (~ sx_rationally_feasible n (Zlength rows) (build_matrix rows)) as Hinfeasible.
  { intros Hfeasible.
    apply (proj2 (os_feasible_iff n rows)) in Hfeasible.
    rewrite <- Hm in Hfeasible.
    destruct (sx_feasible_valuation_extends__infeasible_return n m k
      (build_matrix (os_kept n rows)) Hk Hfeasible) as [y [Hnonpositive Hinput]].
    apply (entering_blocked_row_not_feasible n m k ret D C A B R Hrow Hbasis
      (proj1 Haux) Hpositive Hblocked).
    exists y. split.
    - exact Hnonpositive.
    - exact (proj2 (Hequations y) Hinput). }
  unfold sx_check_result.
  split; [right; reflexivity |].
  split.
  - split; [discriminate |]. intros Hfeasible. contradiction.
  - split; [intros _; exact Hinfeasible | intros _; reflexivity].
Qed.

(* The C pivot searches for this unique entry in the nonbasic array.
   Fixing the logical slot by its value lets the caller specialize the
   frozen ghost-parameterized contract without a call-site directive. *)
Definition sx_entering_slot (nb : list Z) (e : Z) : Z :=
  match find (fun q => Z.eqb (Znth q nb 0) e) (Zrange 0 (Zlength nb)) with
  | Some q => q
  | None => 0
  end.

(* The computed index is inside the owned nonbasic enumeration and its
   column is the actual entering parameter. *)
Definition sx_entering_slot_matches (nb : list Z) (e : Z) : Prop :=
  0 <= sx_entering_slot nb e < Zlength nb /\
  Znth (sx_entering_slot nb e) nb 0 = e.

Lemma sx_entering_slot_valid k B R nb e :
  pivot_nonbasic_columns k B R nb ->
  0 <= e < k -> Znth e R 0 = UINT_MAX ->
  sx_entering_slot_matches nb e.
Proof.
  unfold sx_entering_slot_matches.
  intros Hcolumns He Hnonbasic.
  destruct (pivot_nonbasic_slot k B R nb e Hcolumns He Hnonbasic)
    as (q & Hq & Hcolumn & _).
  unfold sx_entering_slot.
  destruct (find (fun j => Z.eqb (Znth j nb 0) e) (Zrange 0 (Zlength nb)))
    as [j|] eqn:Hfind.
  - apply find_some in Hfind. destruct Hfind as [Hj Hentry].
    split.
    + now apply In_Zrange in Hj.
    + now apply Z.eqb_eq in Hentry.
  - exfalso.
    assert (Hin : In q (Zrange 0 (Zlength nb))) by (apply In_Zrange; exact Hq).
    pose proof (find_none _ _ Hfind q Hin) as Hmiss.
    change (Z.eqb (Znth q nb 0) e = false) in Hmiss.
    rewrite Hcolumn, Z.eqb_refl in Hmiss. discriminate.
Qed.

(* Every ghost slot admitted by the frozen Require is exactly the closed
   argument used in the caller's declaration. Rewriting by this equality
   specializes both its Require and its exact pivot_optimized_result. *)
Lemma sx_entering_slot_unique k B R nb e q :
  pivot_nonbasic_columns k B R nb ->
  0 <= e < k -> Znth e R 0 = UINT_MAX ->
  0 <= q < Zlength nb -> Znth q nb 0 = e ->
  q = sx_entering_slot nb e.
Proof.
  intros Hcolumns He Hnonbasic Hq Hentry.
  destruct (pivot_nonbasic_slot k B R nb e Hcolumns He Hnonbasic)
    as (slot & _ & _ & Hunique).
  destruct (sx_entering_slot_valid k B R nb e Hcolumns He Hnonbasic)
    as [Hbound Hfound].
  transitivity slot.
  - now apply Hunique.
  - symmetry. now apply Hunique.
Qed.
