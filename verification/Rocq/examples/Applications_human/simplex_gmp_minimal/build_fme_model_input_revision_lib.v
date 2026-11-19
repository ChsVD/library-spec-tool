From Coq Require Import ZArith List String Lia QArith.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_lib.
From SimpleC.EE.Applications_human.simplex_gmp_minimal Require Import integers_fme_model_lib.
Import naive_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.

(* The frontend's return slot for the by-value table has seven fresh fields. *)
Definition UndefStructPredtable (p : Z) : Assertion :=
  &(p # "table" ->ₛ "rows") # UInt |->_ **
  &(p # "table" ->ₛ "cols") # UInt |->_ **
  &(p # "table" ->ₛ "d") # Ptr |->_ **
  &(p # "table" ->ₛ "c") # Ptr |->_ **
  &(p # "table" ->ₛ "a") # Ptr |->_ **
  &(p # "table" ->ₛ "basic") # Ptr |->_ **
  &(p # "table" ->ₛ "row") # Ptr |->_.

(* A row snapshot binds the coefficient base, link, and mathematical row.
   The start address and the successive links identify every node. *)
Record build_row_snapshot := {
  build_row_coefficients : Z;
  build_row_next : Z;
  build_row_entries : list Z
}.

Definition default_build_row_snapshot : build_row_snapshot :=
  {| build_row_coefficients := 0; build_row_next := 0; build_row_entries := nil |}.

Fixpoint build_input_segment
    (p tail count : Z) (rows : list build_row_snapshot) : Assertion :=
  match rows with
  | nil => “ p = tail ” && emp
  | entry :: rest =>
    “ p <> 0 /\ build_row_coefficients entry <> 0 ” &&
    &(p # "InequList" ->ₛ "coef") # Ptr |-> build_row_coefficients entry **
    &(p # "InequList" ->ₛ "next") # Ptr |-> build_row_next entry **
    MpzArray.full (build_row_coefficients entry) count (build_row_entries entry) **
    build_input_segment (build_row_next entry) tail count rest
  end.

Definition build_row_at (rows : list build_row_snapshot) (r : Z) : build_row_snapshot :=
  Znth r rows default_build_row_snapshot.

Definition build_matrix (rows : list build_row_snapshot) : list Constraint :=
  map (fun row => list_Constraint (build_row_entries row)) rows.

(* The result is exact at the logical array level. The A block is row-major
   because the accepted release consumes this same one-dimensional block. *)
Definition simplex_initial_table
    (n m k : Z) (matrix : list Constraint) (d c a basic row : list Z) : Prop :=
  k = n + m /\
  (forall r, 0 <= r < m ->
    Znth r d 0 = 1 /\
    Znth r c 0 = coef_Znth 0 (Znth r matrix (list_Constraint nil)) 0 /\
    Znth r basic 0 = n + r /\ Znth (n + r) row 0 = r) /\
  (forall v, 0 <= v < n -> Znth v row 0 = UINT_MAX) /\
  (forall r v, 0 <= r < m -> 0 <= v < k ->
    Znth (r * k + v) a 0 =
      if (v <? n)%Z then coef_Znth (v + 1) (Znth r matrix (list_Constraint nil)) 0 else 0).

(* This is the rational, row-major equality understood by the solver.
   Both finite sums use the standard fold over a list of products. *)
Definition simplex_initial_equations
    (n m k : Z) (matrix : list Constraint) (d c a basic : list Z) : Prop :=
  forall r (y : Z -> Q), 0 <= r < m ->
    let input := Znth r matrix (list_Constraint nil) in
    ((inject_Z (Znth r d 0%Z) * y (Znth r basic 0%Z) ==
      inject_Z (Znth r c 0%Z) +
      fold_right Qplus 0
        (map (fun v => (inject_Z (Znth (r * k + v)%Z a 0%Z) * y v)%Q)
          (SumLib.ZRange.Zrange 0%Z k)))%Q <->
     (y (n + r)%Z == inject_Z (coef_Znth 0%Z input 0%Z) +
      fold_right Qplus 0
        (map (fun v => (inject_Z (coef_Znth (v + 1)%Z input 0%Z) * y v)%Q)
          (SumLib.ZRange.Zrange 0%Z n)))%Q).

(* Prefix state for the row-building loop. d/c include [0,dc), A includes
   the first r rows plus v entries of row r, and basic/row include [0,r). *)
Definition simplex_build_prefix
    (n k r v dc : Z) (matrix : list Constraint) (d c a basic row : list Z) : Prop :=
  (forall i, 0 <= i < Zlength d -> Znth i d 0 = if (i <? dc)%Z then 1 else 0) /\
  (forall i, 0 <= i < Zlength c ->
    Znth i c 0 = if (i <? dc)%Z then
      coef_Znth 0 (Znth i matrix (list_Constraint nil)) 0 else 0) /\
  (forall i j, 0 <= i < Zlength matrix -> 0 <= j < k ->
    Znth (i * k + j) a 0 =
      if ((i <? r)%Z || (Z.eqb i r && (j <? v)%Z))%bool then
        if (j <? n)%Z then coef_Znth (j + 1) (Znth i matrix (list_Constraint nil)) 0 else 0
      else 0) /\
  (forall i, 0 <= i < r -> Znth i basic 0 = n + i) /\
  (forall j, 0 <= j < k ->
    Znth j row 0 = if ((n <=? j)%Z && (j <? n + r)%Z)%bool then j - n else UINT_MAX).

(* Reassemble a borrowed row from the same address and mathematical value
   that the value-level copy contract returns. *)
Lemma build_input_coefficients_restore :
  forall p j count values,
    0 <= j < count ->
    store_Z (p + j * mpz_sizeof) (Znth j values 0) **
    MpzArray.missing_i p j 0 count values |--
    MpzArray.full p count values.
Proof.
  intros p j count values Hj.
  pose proof (MpzArray.missing_i_merge_to_full p j count (Znth j values 0) values Hj) as Hmerge.
  rewrite replace_Znth_Znth in Hmerge.
  exact Hmerge.
Qed.

(* The FME projection forgets the addresses tracked by the borrow contract. *)
Lemma build_input_segment_to_fme :
  forall p count entries,
    0 < count ->
    build_input_segment p 0 count entries |--
    InequList p count (build_matrix entries).
Proof.
  intros p count entries Hcount; revert p.
  induction entries as [|entry rest IH]; intro p.
  - intros st H; exact H.
  - cbn [build_input_segment build_matrix map InequList].
    Intros_p Hnode.
    destruct Hnode as [Hp Hbase].
    Exists (build_row_coefficients entry) (build_row_next entry).
    sep_apply (IH (build_row_next entry)).
    assert (Hcoeff :
      MpzArray.full (build_row_coefficients entry) count (build_row_entries entry)
      |-- mpz_coef_array (build_row_coefficients entry) count
        (list_Constraint (build_row_entries entry))).
    {
      unfold mpz_coef_array.
      destruct (build_row_entries entry) as [|value rest_values].
      - prop_apply MpzArray.full_Zlength. Intros_p Hlength.
        change (0 = count) in Hlength. exfalso; lia.
      - intros st Hstorage. right; split; [exact Hbase | exact Hstorage].
    }
    sep_apply Hcoeff.
    unfold build_matrix.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; assumption.
Qed.

Lemma build_matrix_coefficient :
  forall rows r j,
    0 <= r < Zlength rows ->
    coef_Znth j (Znth r (build_matrix rows) (list_Constraint nil)) 0 =
    Znth j (build_row_entries (build_row_at rows r)) 0.
Proof.
  intros rows r j Hr.
  unfold build_matrix, build_row_at.
  replace (list_Constraint nil)
    with (list_Constraint (build_row_entries default_build_row_snapshot)) by reflexivity.
  rewrite (Znth_map (fun row => list_Constraint (build_row_entries row)) rows r
    default_build_row_snapshot (list_Constraint (build_row_entries default_build_row_snapshot))) by lia.
  destruct (build_row_entries (Znth r rows default_build_row_snapshot)) as [|value rest].
  - unfold coef_Znth, Znth, Constraint_list, list_Constraint; destruct (Z.to_nat j) as [|[|k]]; reflexivity.
  - reflexivity.
Qed.

(* Joining contiguous segments preserves the complete pointer and value snapshot. *)
Lemma build_input_segment_app :
  forall rows1 rows2 head middle tail count,
    build_input_segment head middle count rows1 **
    build_input_segment middle tail count rows2 |--
    build_input_segment head tail count (rows1 ++ rows2).
Proof.
  induction rows1 as [|entry rows1 IH]; intros rows2 head middle tail count;
    cbn [build_input_segment app].
  - Intros_p Hhead. subst head. cancel.
  - Intros_p Hnode.
    sep_apply (IH rows2 (build_row_next entry) middle tail count).
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. exact Hnode.
Qed.

(* Rational sums used below differ only by the appended zero coefficients. *)
Local Lemma rational_sum_ext :
  forall (indices : list Z) (f g : Z -> Q),
    (forall i, In i indices -> (f i == g i)%Q) ->
    (fold_right Qplus 0%Q (map f indices) ==
     fold_right Qplus 0%Q (map g indices))%Q.
Proof.
  induction indices as [|i rest IH]; intros f g Hsame; simpl.
  - reflexivity.
  - apply Qplus_comp.
    + apply Hsame. now left.
    + apply IH. intros j Hj. apply Hsame. now right.
Qed.

Local Lemma rational_sum_erase_zero_suffix :
  forall (prefix suffix : list Z) (f : Z -> Q),
    (forall i, In i suffix -> (f i == 0)%Q) ->
    (fold_right Qplus 0%Q (map f (prefix ++ suffix)) ==
     fold_right Qplus 0%Q (map f prefix))%Q.
Proof.
  induction prefix as [|i rest IH]; intros suffix f Hzero; simpl.
  - transitivity (fold_right Qplus 0%Q (map (fun _ : Z => 0%Q) suffix)).
    + apply rational_sum_ext. exact Hzero.
    + induction suffix as [|j tail IHtail]; simpl.
      * reflexivity.
      * rewrite Qplus_0_l. apply IHtail.
        intros v Hv. apply Hzero. now right.
  - apply Qplus_comp.
    + reflexivity.
    + apply IH. exact Hzero.
Qed.

Lemma simplex_initial_table_implies_rational_equations :
  forall n m k matrix d c a basic row,
    0 <= n -> 0 <= m ->
    simplex_initial_table n m k matrix d c a basic row ->
    simplex_initial_equations n m k matrix d c a basic.
Proof.
  intros n m k matrix d c a basic row Hn Hm Htable.
  destruct Htable as (Hk & Hrows & _ & Ha).
  intros r y Hr.
  destruct (Hrows r Hr) as (Hd & Hc & Hb & _).
  cbn zeta.
  rewrite Hd, Hc, Hb.
  assert (Hsplit : SumLib.ZRange.Zrange 0 k =
    (SumLib.ZRange.Zrange 0 n ++ SumLib.ZRange.Zrange n k)%list).
  {
    unfold SumLib.ZRange.Zrange.
    replace (k - 0) with (n - 0 + (k - n)) by lia.
    rewrite Z2Nat.inj_add by lia.
    rewrite SumLib.ZRange.Zrange_aux_app.
    replace (0 + Z.of_nat (Z.to_nat (n - 0))) with n by lia.
    reflexivity.
  }
  assert (Hsum :
    (fold_right Qplus 0%Q
      (map (fun v => (inject_Z (Znth (r * k + v)%Z a 0%Z) * y v)%Q)
        (SumLib.ZRange.Zrange 0 k)) ==
     fold_right Qplus 0%Q
      (map (fun v => (inject_Z (coef_Znth (v + 1)%Z
        (Znth r matrix (list_Constraint nil)) 0%Z) * y v)%Q)
        (SumLib.ZRange.Zrange 0 n)))%Q).
  {
    rewrite Hsplit.
    etransitivity.
    - apply rational_sum_erase_zero_suffix.
      intros v Hv.
      apply SumLib.ZRange.In_Zrange in Hv.
      rewrite (Ha r v Hr) by lia.
      assert (Hvtest : (v <? n)%Z = false) by (apply Z.ltb_ge; lia).
      rewrite Hvtest.
      change ((0 * y v) == 0)%Q.
      ring.
    - apply rational_sum_ext.
      intros v Hv.
      apply SumLib.ZRange.In_Zrange in Hv.
      rewrite (Ha r v Hr) by lia.
      assert (Hvtest : (v <? n)%Z = true) by (apply Z.ltb_lt; lia).
      now rewrite Hvtest.
  }
  setoid_rewrite Hsum.
  setoid_rewrite Qmult_1_l.
  tauto.
Qed.


Lemma build_suffix_cons__build_initial_table :
  forall rows i m, m = Zlength rows -> 0 <= i < m ->
    sublist i m rows = build_row_at rows i :: sublist (i + 1) m rows.
Proof.
  intros rows i m Hm Hi.
  rewrite (sublist_split i m (i + 1) rows) at 1 by lia.
  unfold build_row_at. rewrite (sublist_single default_build_row_snapshot i rows) by lia.
  reflexivity.
Qed.
Lemma build_prefix_snoc__build_initial_table :
  forall rows i, 0 <= i < Zlength rows ->
    sublist 0 (i + 1) rows = (sublist 0 i rows ++ [build_row_at rows i])%list.
Proof.
  intros rows i Hi.
  rewrite (sublist_split 0 (i + 1) i rows) at 1 by lia.
  unfold build_row_at. rewrite (sublist_single default_build_row_snapshot i rows) by lia.
  reflexivity.
Qed.
Lemma build_tail_nonempty__build_initial_table :
  forall p count rows i m, p <> 0 -> 0 <= i <= m ->
    build_input_segment p 0 count (sublist i m rows) |-- “ i < m ”.
Proof.
  intros p count rows i m Hp Hi.
  destruct (Z.eq_dec i m) as [->|Hlt].
  - rewrite Zsublist_nil by lia. cbn [build_input_segment].
    Intros_p Hnull. dump_pre_spatial. contradiction.
  - dump_pre_spatial. lia.
Qed.
Lemma build_tail_null__build_initial_table :
  forall count rows i m, m = Zlength rows -> 0 <= i <= m ->
    build_input_segment 0 0 count (sublist i m rows) |-- “ i = m ”.
Proof.
  intros count rows i m Hm Hi.
  destruct (Z.eq_dec i m) as [->|Hlt].
  - dump_pre_spatial. reflexivity.
  - rewrite (build_suffix_cons__build_initial_table rows i m Hm ltac:(lia)).
    cbn [build_input_segment]. Intros_p Hnonnull.
    dump_pre_spatial. tauto.
Qed.
Lemma build_single_row__build_initial_table :
  forall row q count,
    q <> 0 -> build_row_coefficients row <> 0 ->
    &(q # "InequList" ->ₛ "coef") # Ptr |-> build_row_coefficients row **
    &(q # "InequList" ->ₛ "next") # Ptr |-> build_row_next row **
    MpzArray.full (build_row_coefficients row) count (build_row_entries row)
    |-- build_input_segment q (build_row_next row) count [row].
Proof.
  intros row q count Hq Hcoef.
  cbn [build_input_segment].
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.
Lemma build_push_row__build_initial_table :
  forall rows i head q count,
    0 <= i < Zlength rows -> q <> 0 ->
    build_row_coefficients (build_row_at rows i) <> 0 ->
    &(q # "InequList" ->ₛ "next") # Ptr |-> build_row_next (build_row_at rows i) **
    (&(q # "InequList" ->ₛ "coef") # Ptr |-> build_row_coefficients (build_row_at rows i) **
     (MpzArray.full (build_row_coefficients (build_row_at rows i)) count (build_row_entries (build_row_at rows i)) **
      build_input_segment head q count (sublist 0 i rows)))
    |-- build_input_segment head (build_row_next (build_row_at rows i)) count (sublist 0 (i + 1) rows).
Proof.
  intros rows i head q count Hi Hq Hcoef.
  rewrite (build_prefix_snoc__build_initial_table rows i Hi).
  sep_apply_r_atomic (build_input_segment_app (sublist 0 i rows) [build_row_at rows i]
    head q (build_row_next (build_row_at rows i)) count).
  sep_apply (build_single_row__build_initial_table (build_row_at rows i) q count Hq Hcoef).
  cancel.
Qed.
Lemma build_count_bound__build_initial_table :
  forall m n, 0 <= m -> 0 <= n -> (0 < m -> simplex_mpz_layout) ->
    m * (m + n) * sizeof("__mpz_struct") <= INT_MAX ->
    m * (m + n) <= INT_MAX.
Proof.
  intros m n Hm Hn Hlayout Hbound.
  destruct (Z.eq_dec m 0) as [->|Hnonzero].
  - change (0 <= 2147483647). lia.
  - destruct (Hlayout ltac:(lia)) as [Hsize _]. rewrite Hsize in Hbound.
    assert (0 <= m * (m + n)) by nia. lia.
Qed.
Lemma build_empty_segment__build_initial_table :
  forall p count, emp |-- build_input_segment p p count nil.
Proof.
  intros p count. cbn [build_input_segment].
  split_pure_spatial; [cancel | dump_pre_spatial; reflexivity].
Qed.
Lemma build_matrix_length__build_initial_table :
  forall rows, Zlength (build_matrix rows) = Zlength rows.
Proof. intros; unfold build_matrix; apply Zlength_map. Qed.
Lemma build_dc_prefix_step__build_initial_table :
  forall n k r rows d c a b row,
    0 <= r < Zlength rows -> Zlength d = Zlength rows -> Zlength c = Zlength rows ->
    simplex_build_prefix n k r 0 r (build_matrix rows) d c a b row ->
    simplex_build_prefix n k r 0 (r + 1) (build_matrix rows)
      (replace_Znth r 1 d)
      (replace_Znth r (Znth 0 (build_row_entries (build_row_at rows r)) 0) c)
      a b row.
Proof.
  intros n k r rows d c a b row Hr Hdl Hcl (Hd & Hc & Ha & Hb & Hrow).
  split; [|split; [|tauto]].
  - intros i Hi. rewrite Zlength_replace_Znth in Hi.
    destruct (Z.eq_dec i r) as [->|Hneq].
    + rewrite Znth_replace_Znth_Same by lia.
      rewrite (proj2 (Z.ltb_lt r (r+1)) ltac:(lia)). reflexivity.
    + rewrite Znth_replace_Znth_Diff by lia. rewrite Hd by lia.
      destruct (Z.ltb_spec i r), (Z.ltb_spec i (r+1)); try lia; reflexivity.
  - intros i Hi. rewrite Zlength_replace_Znth in Hi.
    destruct (Z.eq_dec i r) as [->|Hneq].
    + rewrite Znth_replace_Znth_Same by lia.
      rewrite (proj2 (Z.ltb_lt r (r+1)) ltac:(lia)).
      symmetry. apply build_matrix_coefficient; lia.
    + rewrite Znth_replace_Znth_Diff by lia. rewrite Hc by lia.
      destruct (Z.ltb_spec i r), (Z.ltb_spec i (r+1)); try lia; reflexivity.
Qed.
Lemma build_row_major_index_injective__build_initial_table :
  forall k i j r v,
    0 < k -> 0 <= j < k -> 0 <= v < k ->
    i*k+j = r*k+v -> i = r /\ j = v.
Proof.
  intros k i j r v Hk Hj Hv Heq.
  assert (i = r) by (destruct (Z.lt_trichotomy i r) as [H|[H|H]]; nia).
  split; nia.
Qed.
Lemma build_a_prefix_step__build_initial_table :
  forall n k r v rows d c a b row,
    0 <= r < Zlength rows -> 0 <= v < n -> n <= k ->
    Zlength a = Zlength rows * k ->
    simplex_build_prefix n k r v (r+1) (build_matrix rows) d c a b row ->
    simplex_build_prefix n k r (v+1) (r+1) (build_matrix rows) d c
      (replace_Znth (r*k+v) (Znth (v+1) (build_row_entries (build_row_at rows r)) 0) a) b row.
Proof.
  intros n k r v rows d c a b row Hr Hv Hnk Hlen (Hd & Hc & Ha & Hb & Hrow).
  split; [exact Hd|]. split; [exact Hc|]. split; [|tauto].
  intros i j Hi Hj.
  rewrite build_matrix_length__build_initial_table in Hi.
  assert (Hpos : 0 <= r*k+v < Zlength a) by nia.
  destruct (Z.eq_dec (r*k+v) (i*k+j)) as [Heq|Hneq].
  - symmetry in Heq.
    destruct (build_row_major_index_injective__build_initial_table k i j r v
      ltac:(lia) Hj ltac:(lia) Heq) as [-> ->].
    rewrite Znth_replace_Znth_Same by exact Hpos.
    rewrite Z.eqb_refl, (proj2 (Z.ltb_ge r r) ltac:(lia)),
      (proj2 (Z.ltb_lt v (v+1)) ltac:(lia)), (proj2 (Z.ltb_lt v n) ltac:(lia)).
    symmetry. apply build_matrix_coefficient. exact Hr.
  - rewrite Znth_replace_Znth_Diff by nia.
    rewrite Ha by (try rewrite build_matrix_length__build_initial_table; lia).
    destruct (Z.ltb_spec i r); [reflexivity|].
    destruct (Z.eqb_spec i r); [subst i|reflexivity].
    destruct (Z.ltb_spec j v), (Z.ltb_spec j (v+1)); try reflexivity; lia.
Qed.
Lemma build_missing_length__build_initial_table :
  forall p i count values,
    MpzArray.missing_i p i 0 count values |-- “ Zlength values = count ”.
Proof.
  intros p i count values. unfold MpzArray.missing_i.
  replace count with (count - 0) at 2 by lia.
  apply store_array_missing_i_rec_Zlength.
Qed.
Lemma build_dummy_segment_zero__build_initial_table :
  forall p dummy hi (len : nat) lo, hi = lo + Z.of_nat len ->
    store_undef_array_rec
      (fun base index => store_Z_dummy (base + index * sizeof("__mpz_struct")) dummy)
      p lo hi len |--
    store_array_rec mpz_store p lo hi (repeat 0 len).
Proof.
  intros p dummy hi len. induction len as [|len IH]; intros lo Hlen.
  - cbn [repeat store_undef_array_rec store_array_rec].
    Intros. split_pure_spatial; [cancel | split_pures; dump_pre_spatial; reflexivity || lia].
  - cbn [repeat store_undef_array_rec store_array_rec].
    sep_apply_l_atomic (store_Z_dummy_to_store_Z_0 (p + lo * sizeof("__mpz_struct")) dummy).
    sep_apply_l_atomic (IH (lo + 1) ltac:(lia)).
    unfold mpz_store, mpz_sizeof.
    cancel.
Qed.
Lemma build_dummy_zero_array__build_initial_table :
  forall p count dummy, 0 <= count ->
    simplex_mpz_dummy_seg p 0 count dummy |--
    MpzArray.full p count (repeat 0 (Z.to_nat count)).
Proof.
  intros p count dummy Hcount.
  unfold simplex_mpz_dummy_seg, MpzArray.full, store_array.
  replace (count - 0) with count by lia.
  apply build_dummy_segment_zero__build_initial_table. lia.
Qed.
Lemma build_uchar_to_uint_segment__build_initial_table :
  forall p lo hi (len : nat), hi = lo + Z.of_nat len ->
    0 <= lo ->
    (lo < hi -> 0 <= p /\ (4 | p) /\ p + 4*hi - 1 <= addr_max_unsigned) ->
    UCharArray.undef_seg p (4*lo) (4*hi) |-- UIntArray.undef_seg p lo hi.
Proof.
  intros p lo hi len. revert lo.
  induction len as [|len IH]; intros lo Hlen Hlo Hrange.
  - replace hi with lo by lia.
    rewrite UCharArray.undef_seg_empty, UIntArray.undef_seg_empty.
    reflexivity.
  - assert (Hlt : lo < hi) by lia.
    destruct (Hrange Hlt) as [Hp [Halign Hmax]].
    sep_apply_l_atomic (UCharArray.undef_seg_split_to_undef_seg p (4*lo) (4*(lo+1)) (4*hi) ltac:(lia)).
    sep_apply_l_atomic (uchar_segment_four_raw__initialization_loop p (4*lo) (4*(lo+1)) ltac:(lia)).
    assert (Hvalid : valid_object (p + 4*lo) 4 4).
    { unfold valid_object, Arch.valid_object, Arch.valid_addr_range, aligned, Arch.aligned.
      fold addr_max_unsigned. split; [lia|].
      apply Z.mod_divide; [lia|]. destruct Halign as [a Ha]. exists (a + lo). lia. }
    sep_apply_l_atomic (raw_four_to_int__initialization_loop (p + 4*lo) Hvalid).
    sep_apply_l_atomic (IH (lo+1) ltac:(lia) ltac:(lia) ltac:(tauto)).
    sep_apply_r_atomic (proj2 (UIntArray.undef_seg_unfold p lo hi Hlt)).
    unfold StoreUIntAsElement.undefstoreA.
    rewrite sizeof_uint. replace (lo*4) with (4*lo) by lia.
    cbn [poly_undef_store]. cancel.
    change (undef_store_int (p + 4*lo) |-- undef_store_uint (p + 4*lo)). reflexivity.
Qed.
Lemma build_uchar_to_uint_full__build_initial_table :
  forall p count, 0 <= count ->
    (0 < count -> 0 <= p /\ (4 | p) /\ p + 4*count - 1 <= addr_max_unsigned) ->
    UCharArray.undef_full p (4*count) |-- UIntArray.undef_full p count.
Proof.
  intros p count Hcount Hrange.
  pose proof (build_uchar_to_uint_segment__build_initial_table p 0 count
    (Z.to_nat count) ltac:(lia) ltac:(lia) Hrange) as Hsegment.
  unfold UCharArray.undef_full, UIntArray.undef_full, store_undef_array.
  unfold UCharArray.undef_seg, UIntArray.undef_seg in Hsegment.
  rewrite Z.mul_0_r, !Z.sub_0_r in Hsegment.
  exact Hsegment.
Qed.
Lemma build_prefix_initial__build_initial_table :
  forall n m rows row,
    0 <= n -> 0 <= m ->
    (forall j, 0 <= j < m+n -> Znth j row 0 = UINT_MAX) ->
    simplex_build_prefix n (m+n) 0 0 0 (build_matrix rows)
      (repeat 0 (Z.to_nat m)) (repeat 0 (Z.to_nat m))
      (repeat 0 (Z.to_nat (m*(m+n)))) nil row.
Proof.
  intros n m rows row Hn Hm Hrow. unfold simplex_build_prefix.
  repeat split.
  - intros i Hi. rewrite Znth_repeat, (proj2 (Z.ltb_ge i 0)) by lia. reflexivity.
  - intros i Hi. rewrite Znth_repeat, (proj2 (Z.ltb_ge i 0)) by lia. reflexivity.
  - intros i j Hi Hj. rewrite Znth_repeat, (proj2 (Z.ltb_ge i 0)), (proj2 (Z.ltb_ge j 0)) by lia.
    destruct (Z.eqb i 0); reflexivity.
  - intros i Hi. lia.
  - intros j Hj. rewrite Hrow by lia.
    replace (n + 0) with n by lia.
    destruct (Z.leb_spec n j), (Z.ltb_spec j n); try lia; reflexivity.
Qed.
Lemma build_outer_prefix_step__build_initial_table :
  forall n m r rows d c a b row,
    0 <= n -> 0 <= r < m -> Zlength b = r -> Zlength row = m+n ->
    simplex_build_prefix n (m+n) r n (r+1) (build_matrix rows) d c a b row ->
    simplex_build_prefix n (m+n) (r+1) 0 (r+1) (build_matrix rows) d c a
      (b ++ [n+r])%list (replace_Znth (n+r) r row).
Proof.
  intros n m r rows d c a b row Hn Hr Hbl Hrl (Hd & Hc & Ha & Hb & Hrow).
  split; [exact Hd|]. split; [exact Hc|]. split.
  - intros i j Hi Hj. rewrite Ha by assumption.
    destruct (Z.ltb_spec i r) as [Hir|Hir].
    + rewrite (proj2 (Z.ltb_lt i (r+1))) by lia. reflexivity.
    + destruct (Z.eqb_spec i r) as [->|Hneq].
      * rewrite (proj2 (Z.ltb_lt r (r+1))) by lia.
        destruct (Z.ltb_spec j n); reflexivity.
      * rewrite (proj2 (Z.ltb_ge i (r+1))) by lia.
        rewrite (proj2 (Z.ltb_ge j 0)) by lia.
        destruct (Z.eqb i (r+1)); reflexivity.
  - split.
    + intros i Hi. destruct (Z.eq_dec i r) as [->|Hneq].
      * rewrite app_Znth2 by lia. replace (r - Zlength b) with 0 by lia. reflexivity.
      * rewrite app_Znth1 by lia. apply Hb. lia.
    + intros j Hj. destruct (Z.eq_dec j (n+r)) as [->|Hneq].
      * rewrite Znth_replace_Znth_Same by lia.
        rewrite (proj2 (Z.leb_le n (n+r))), (proj2 (Z.ltb_lt (n+r) (n+(r+1)))) by lia.
        simpl. lia.
      * rewrite Znth_replace_Znth_Diff by lia. rewrite Hrow by lia.
        destruct (Z.leb_spec n j), (Z.ltb_spec j (n+r)), (Z.ltb_spec j (n+(r+1)));
          try reflexivity; lia.
Qed.
Lemma build_prefix_final__build_initial_table :
  forall n m rows d c a b row,
    0 <= n -> 0 <= m -> Zlength rows = m -> Zlength d = m -> Zlength c = m ->
    simplex_build_prefix n (m+n) m 0 m (build_matrix rows) d c a b row ->
    simplex_initial_table n m (m+n) (build_matrix rows) d c a b row.
Proof.
  intros n m rows d c a b row Hn Hm Hml Hdl Hcl (Hd & Hc & Ha & Hb & Hrow).
  unfold simplex_initial_table. split; [lia|]. split.
  - intros i Hi. repeat split.
    + rewrite Hd by lia. rewrite (proj2 (Z.ltb_lt i m)) by lia. reflexivity.
    + rewrite Hc by lia. rewrite (proj2 (Z.ltb_lt i m)) by lia. reflexivity.
    + apply Hb. exact Hi.
    + rewrite Hrow by lia. rewrite (proj2 (Z.leb_le n (n+i))), (proj2 (Z.ltb_lt (n+i) (n+m))) by lia.
      simpl. lia.
  - split.
    + intros j Hj. rewrite Hrow by lia. rewrite (proj2 (Z.leb_gt n j)) by lia. reflexivity.
    + intros i j Hi Hj. rewrite Ha by (try rewrite build_matrix_length__build_initial_table; lia).
      rewrite (proj2 (Z.ltb_lt i m)) by lia. reflexivity.
Qed.
