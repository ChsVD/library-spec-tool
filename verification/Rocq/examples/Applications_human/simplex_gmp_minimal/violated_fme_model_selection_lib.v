From Coq Require Import ZArith List String Lia QArith.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic CommonAssertion ArrayLibCore.
From SumLib Require Import ZRange.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_lib.
From SimpleC.EE.Applications_human.simplex_gmp_minimal Require Import integers_fme_model_lib.

Import naive_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.

(* R is the entry snapshot starting at variable n. H maps row indices to
   their entry signed header sizes, or to their mathematical constants. *)
Definition positive_row_candidate (n : Z) (R : list Z) (H : Z -> Z) (v : Z) : Prop :=
  let j := Znth (v - n) R 0 in
  j <> UINT_MAX /\ 0 < H j.

Definition first_positive_row (n k : Z) (R : list Z) (H : Z -> Z) : Z :=
  match find (fun v => let j := Znth (v - n) R 0 in
                       andb (negb (Z.eqb j UINT_MAX)) (0 <? H j)%Z)
             (Zrange n k) with
  | Some v => Znth (v - n) R 0
  | None => UINT_MAX
  end.

Definition no_positive_row (n v : Z) (R : list Z) (H : Z -> Z) : Prop :=
  forall u, n <= u < v -> ~ positive_row_candidate n R H u.

Lemma no_positive_row_start n R H : no_positive_row n n R H.
Proof. unfold no_positive_row; intros; lia. Qed.

Lemma no_positive_row_step n v R H :
  no_positive_row n v R H ->
  ~ positive_row_candidate n R H v ->
  no_positive_row n (v + 1) R H.
Proof.
  unfold no_positive_row. intros Hprefix Hv u Hu.
  destruct (Z.eq_dec u v) as [->|Hne]; [exact Hv | apply Hprefix; lia].
Qed.

(* Exactly the distinct non-sentinel rows occurring in the suffix. *)
Definition scan_size_fields (p : Z) (J : list Z) (H : Z -> Z) : Assertion :=
  fold_right (fun (j : Z) (rest : Assertion) =>
    let addr := (p + j * mpz_sizeof)%Z in
    (&(addr # "__mpz_struct" ->ₛ "_mp_size") # Int |-> H j) ** rest) emp J.

(* Exact MiniGMP witnesses. Spare capacity retains its original undef
   ownership, as in store_Z. The static zero limb need not be owned. *)
Record scan_mpz_snapshot := {
  scan_limb_ptr : Z;
  scan_mp_size : Z;
  scan_mp_alloc : Z;
  scan_limbs : list Z
}.

Definition scan_mpz_default : scan_mpz_snapshot :=
  {| scan_limb_ptr := 0; scan_mp_size := 0; scan_mp_alloc := 0; scan_limbs := [] |}.

Definition scan_header_sizes (T : list scan_mpz_snapshot) (j : Z) : Z :=
  scan_mp_size (Znth j T scan_mpz_default).

Definition scan_mpz_at (p z : Z) (S : scan_mpz_snapshot) : Assertion :=
  “ Z.abs (scan_mp_size S) <= scan_mp_alloc S ” &&
  “ same_sign z (scan_mp_size S) ” &&
  “ list_to_Z UINT_MOD (scan_limbs S) = Z.abs z /\
    last (scan_limbs S) 1 >= 1 /\ list_within_bound UINT_MOD (scan_limbs S) ” &&
  “ Z.abs (scan_mp_size S) = Zlength (scan_limbs S) ” &&
  mpd_store_list (scan_limb_ptr S) (scan_limbs S) **
  UIntArray.undef_seg (scan_limb_ptr S) (Z.abs (scan_mp_size S)) (scan_mp_alloc S) **
  &(p # "__mpz_struct" ->ₛ "_mp_size") # Int |-> scan_mp_size S **
  &(p # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> scan_mp_alloc S **
  &(p # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> scan_limb_ptr S.

Definition scan_mpz_entry (p j : Z) (e : Z * scan_mpz_snapshot) : Assertion :=
  scan_mpz_at (p + j * mpz_sizeof)%Z (fst e) (snd e).

Definition scan_mpz_array (p count : Z) (V : list Z) (T : list scan_mpz_snapshot) : Assertion :=
  “ Zlength V = Zlength T ” && store_array scan_mpz_entry p count (combine V T).

Definition scan_mpz_array_missing (p j count : Z) (V : list Z)
    (T : list scan_mpz_snapshot) : Assertion :=
  “ Zlength V = Zlength T ” &&
  store_array_missing_i_rec scan_mpz_entry p j 0 count (combine V T).

(* General basis conditions, preserved across a valid pivot. *)
Definition selection_basis (m k : Z) (D A B R : list Z) : Prop :=
  (forall r, 0 <= r < m ->
    0 <= Znth r B 0 < k /\ Znth (Znth r B 0) R 0 = r /\ 0 < Znth r D 0) /\
  (forall v, 0 <= v < k -> Znth v R 0 <> UINT_MAX ->
    0 <= Znth v R 0 < m /\ Znth (Znth v R 0) B 0 = v) /\
  (forall r q, 0 <= r < m -> 0 <= q < m ->
    Znth (r * k + Znth q B 0) A 0 = 0).

(* Whole-system equivalence admits mixing equations during a pivot. *)
Definition selection_equations (n m k : Z) (I : list Constraint) (D C A B : list Z) : Prop :=
  forall x : Z -> Q,
    (forall r, (0 <= r < m)%Z ->
      (inject_Z (Znth r D 0%Z) * x (Znth r B 0%Z) ==
       inject_Z (Znth r C 0%Z) +
       fold_right Qplus 0
         (map (fun v => inject_Z (Znth (r * k + v)%Z A 0%Z) * x v) (Zrange 0%Z k)))%Q) <->
    (forall r, (0 <= r < m)%Z ->
      let input := Znth r I (list_Constraint nil) in
      (x (n + r)%Z == inject_Z (coef_Znth 0%Z input 0%Z) +
       fold_right Qplus 0
         (map (fun v => inject_Z (coef_Znth (v + 1)%Z input 0%Z) * x v) (Zrange 0%Z n)))%Q).

Definition scan_other_rows (j : Z) (J : list Z) : list Z := remove Z.eq_dec j J.

Definition scan_row_domain (n k m : Z) (R J : list Z) : Prop :=
  NoDup J /\
  (forall j, In j J <-> j <> UINT_MAX /\ exists v, n <= v < k /\ Znth (v - n) R 0 = j) /\
  (forall j, In j J -> 0 <= j < m).

Definition scan_row_values (C : list Z) (j : Z) : Z := Znth j C 0.

Lemma scan_row_domain_at n k m R J v :
  scan_row_domain n k m R J -> n <= v < k ->
  Znth (v - n) R 0 <> UINT_MAX ->
  In (Znth (v - n) R 0) J /\ 0 <= Znth (v - n) R 0 < m.
Proof.
  intros [_ [Hset Hbounds]] Hv Hne.
  assert (Hin : In (Znth (v - n) R 0) J).
  { apply Hset. split; [exact Hne | exists v; auto]. }
  auto.
Qed.

Definition scan_size_cell (p j sz : Z) : Assertion :=
  let a := (p + j * mpz_sizeof)%Z in
  &(a # "__mpz_struct" ->ₛ "_mp_size") # Int |-> sz.

Lemma scan_size_fields_focus p J H j :
  NoDup J -> In j J ->
  scan_size_fields p J H --||--
  scan_size_cell p j (H j) ** scan_size_fields p (scan_other_rows j J) H.
Proof.
  intros Hdup Hin. unfold scan_other_rows.
  induction J as [|a J IH]; [contradiction |].
  inversion Hdup as [|? ? Hnot Htail]; subst.
  simpl in Hin. simpl.
  destruct (Z.eq_dec j a) as [->|Hne].
  - rewrite notin_remove by assumption. change (scan_size_cell p a (H a) ** scan_size_fields p J H --||-- scan_size_cell p a (H a) ** scan_size_fields p J H). split; intros st Howned; exact Howned.
  - assert (HinTail : In j J) by (destruct Hin; [congruence | assumption]).
    specialize (IH Htail HinTail). destruct IH as [Hopen Hclose].
    change (scan_size_cell p a (H a) ** scan_size_fields p J H --||--
      scan_size_cell p j (H j) **
      (scan_size_cell p a (H a) ** scan_size_fields p (remove Z.eq_dec j J) H)).
    split.
    + sep_apply Hopen. cancel.
    + sep_apply Hclose. cancel.
Qed.

Lemma positive_row_candidate_bool n R H v :
  andb (negb (Z.eqb (Znth (v - n) R 0) UINT_MAX))
       (0 <? H (Znth (v - n) R 0))%Z = true <->
  positive_row_candidate n R H v.
Proof.
  unfold positive_row_candidate.
  rewrite Bool.andb_true_iff, Bool.negb_true_iff, Z.eqb_neq, Z.ltb_lt.
  reflexivity.
Qed.

Lemma first_positive_row_empty n k R H :
  k <= n -> first_positive_row n k R H = UINT_MAX.
Proof.
  intros Hle. unfold first_positive_row, Zrange.
  assert (Z.to_nat (k - n) = O) as -> by lia. reflexivity.
Qed.

Lemma first_positive_row_none n k R H :
  first_positive_row n k R H = UINT_MAX <-> no_positive_row n k R H.
Proof.
  unfold first_positive_row, no_positive_row.
  set (test := fun v => andb (negb (Z.eqb (Znth (v - n) R 0) UINT_MAX))
                            (0 <? H (Znth (v - n) R 0))%Z).
  destruct (find test (Zrange n k)) as [v|] eqn:Hfind.
  - apply find_some in Hfind as [Hin Htest].
    unfold test in Htest. apply positive_row_candidate_bool in Htest.
    apply <- In_Zrange in Hin.
    split; intro Hnone.
    + unfold positive_row_candidate in Htest. tauto.
    + exfalso. exact (Hnone v Hin Htest).
  - split; [intros _ v Hv Hcand | reflexivity].
    apply In_Zrange in Hv.
    pose proof (find_none _ _ Hfind v Hv) as Htest.
    apply positive_row_candidate_bool in Hcand.
    unfold test in Htest. congruence.
Qed.

Lemma find_Zrange_first (test : Z -> bool) n k v :
  n <= v < k -> test v = true ->
  (forall u, n <= u < v -> test u = false) ->
  find test (Zrange n k) = Some v.
Proof.
  unfold Zrange.
  assert (forall len lo, lo <= v < lo + Z.of_nat len ->
    test v = true -> (forall u, lo <= u < v -> test u = false) ->
    find test (Zrange_aux lo len) = Some v) as Hfirst.
  { induction len as [|len IH]; intros lo Hbounds Hhit Hprefix; [simpl in Hbounds; lia |].
    simpl. destruct (Z.eq_dec lo v) as [->|Hne].
    - now rewrite Hhit.
    - rewrite Hprefix by lia. apply IH; try assumption; [lia | intros; apply Hprefix; lia]. }
  intros; apply Hfirst; auto; lia.
Qed.

Lemma first_positive_row_hit n k R H v :
  n <= v < k -> no_positive_row n v R H -> positive_row_candidate n R H v ->
  first_positive_row n k R H = Znth (v - n) R 0.
Proof.
  intros Hv Hprefix Hhit.
  unfold first_positive_row.
  rewrite (find_Zrange_first _ n k v Hv); [reflexivity | |].
  - apply positive_row_candidate_bool. exact Hhit.
  - intros u Hu. destruct (positive_row_candidate_bool n R H u) as [Htest _].
    destruct (andb (negb (Z.eqb (Znth (u - n) R 0) UINT_MAX))
                   (0 <? H (Znth (u - n) R 0))%Z); [|reflexivity].
    exfalso. exact (Hprefix u Hu (Htest eq_refl)).
Qed.

Lemma find_Zrange_prefix (test : Z -> bool) n k v :
  find test (Zrange n k) = Some v ->
  forall u, n <= u < v -> test u = false.
Proof.
  unfold Zrange.
  assert (forall len lo, find test (Zrange_aux lo len) = Some v ->
    forall u, lo <= u < v -> test u = false) as Hprefix.
  { induction len as [|len IH]; intros lo Hfind u Hu; [discriminate |].
    simpl in Hfind. destruct (test lo) eqn:Hlo.
    - injection Hfind as <-. lia.
    - destruct (Z.eq_dec u lo) as [->|Hne]; [exact Hlo |].
      apply (IH (lo + 1)); [exact Hfind | lia]. }
  apply Hprefix.
Qed.

Lemma first_positive_row_minimal n k R H ret :
  ret <> UINT_MAX ->
  (ret = first_positive_row n k R H <->
   exists v, n <= v < k /\ positive_row_candidate n R H v /\
             no_positive_row n v R H /\ ret = Znth (v - n) R 0).
Proof.
  intros Hne. split.
  - unfold first_positive_row.
    set (test := fun v => andb (negb (Z.eqb (Znth (v - n) R 0) UINT_MAX))
                              (0 <? H (Znth (v - n) R 0))%Z).
    destruct (find test (Zrange n k)) as [v|] eqn:Hfind; [|contradiction].
    intros ->. exists v. pose proof (find_some _ _ Hfind) as [Hin Htest].
    split; [now apply <- In_Zrange |].
    split; [apply positive_row_candidate_bool; exact Htest |].
    split; [|reflexivity].
    intros u Hu Hcand. apply positive_row_candidate_bool in Hcand.
    pose proof (find_Zrange_prefix _ _ _ _ Hfind u Hu) as HtestFalse.
    unfold test in HtestFalse. congruence.
  - intros [v [Hv [Hhit [Hprefix ->]]]].
    symmetry. now apply first_positive_row_hit.
Qed.

Lemma scan_mpz_at_bridge p z :
  store_Z p z --||-- (EX S : scan_mpz_snapshot, scan_mpz_at p z S).
Proof.
  unfold store_Z, mpd_store_Z_compact, scan_mpz_at.
  split.
  - Intros ptr size cap limbs.
    Exists {| scan_limb_ptr := ptr; scan_mp_size := size; scan_mp_alloc := cap;
              scan_limbs := limbs |}.
    simpl. split_pure_spatial.
    + cancel (mpd_store_list ptr limbs). cancel.
    + split_pures; dump_pre_spatial; tauto.
  - Intros S. Exists (scan_limb_ptr S) (scan_mp_size S) (scan_mp_alloc S) (scan_limbs S).
    split_pure_spatial.
    + cancel (mpd_store_list (scan_limb_ptr S) (scan_limbs S)). cancel.
    + split_pures; dump_pre_spatial; tauto.
Qed.

Lemma scan_mpz_segment_bridge p lo hi V :
  store_array_rec mpz_store p lo hi V --||--
  (EX T : list scan_mpz_snapshot,
    “ Zlength V = Zlength T ” && store_array_rec scan_mpz_entry p lo hi (combine V T)).
Proof.
  revert lo. induction V as [|z V IH]; intro lo.
  - split.
    + Exists (@nil scan_mpz_snapshot). simpl store_array_rec. Intros.
      split_pure_spatial; [cancel | split_pures; dump_pre_spatial; rewrite ?Zlength_nil; auto].
    + Intros T. simpl store_array_rec. Intros.
      split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto].
  - split.
    + change (mpz_store p lo z ** store_array_rec mpz_store p (lo + 1) hi V |--
        EX T : list scan_mpz_snapshot,
          “ Zlength (z :: V) = Zlength T ” && store_array_rec scan_mpz_entry p lo hi (combine (z :: V) T)).
      unfold mpz_store at 1.
      sep_apply (proj1 (scan_mpz_at_bridge (p + lo * mpz_sizeof)%Z z)).
      rewrite (IH (lo + 1)).
      Intros S T. Exists (S :: T). simpl store_array_rec.
      rewrite !Zlength_cons.
      split_pure_spatial.
      * change (store_array_rec scan_mpz_entry p (lo + 1) hi (combine V T) ** scan_mpz_entry p lo (z, S)
          |-- scan_mpz_entry p lo (z, S) ** store_array_rec scan_mpz_entry p (lo + 1) hi (combine V T)).
        cancel.
      * split_pures; dump_pre_spatial; lia.
    + Intros T. destruct T as [|S T].
      * rewrite Zlength_cons, Zlength_nil in *. pose proof (Zlength_nonneg V). lia.
      * rewrite !Zlength_cons in *.
        change (scan_mpz_entry p lo (z, S) ** store_array_rec scan_mpz_entry p (lo + 1) hi (combine V T)
          |-- mpz_store p lo z ** store_array_rec mpz_store p (lo + 1) hi V).
        assert (Zlength V = Zlength T) by lia.
        assert (scan_mpz_entry p lo (z, S) |-- mpz_store p lo z) as Hhead.
        { unfold scan_mpz_entry, mpz_store. simpl fst. simpl snd.
          rewrite (scan_mpz_at_bridge (p + lo * mpz_sizeof)%Z z).
          Exists S. cancel. }
        assert (store_array_rec scan_mpz_entry p (lo + 1) hi (combine V T) |--
          store_array_rec mpz_store p (lo + 1) hi V) as Htail.
        { rewrite (IH (lo + 1)).
          Exists T. split_pure_spatial; [cancel | dump_pre_spatial; assumption]. }
        sep_apply Hhead. sep_apply Htail. cancel.
Qed.

Lemma scan_mpz_array_bridge p count V :
  MpzArray.full p count V --||-- (EX T : list scan_mpz_snapshot, scan_mpz_array p count V T).
Proof.
  unfold scan_mpz_array, MpzArray.full, store_array.
  apply scan_mpz_segment_bridge.
Qed.

Lemma scan_mpz_array_lengths p count V T :
  scan_mpz_array p count V T |-- “ Zlength V = count /\ Zlength T = count ”.
Proof.
  unfold scan_mpz_array.
  Intros.
  prop_apply (store_array_Zlength _ scan_mpz_entry p count (combine V T)).
  rewrite Zlength_combine. Intros. normalize; try cancel; try dump_pre_spatial; try lia; try tauto.
Qed.

Lemma scan_mpz_at_sign p z S :
  scan_mpz_at p z S |--
    “ (0 < scan_mp_size S <-> 0 < z) /\ (scan_mp_size S = 0 <-> z = 0) ”.
Proof.
  unfold scan_mpz_at.
  Intros.
  assert (mpd_store_list (scan_limb_ptr S) (scan_limbs S) |--
    mpd_store_Z_compact UINT_MOD (scan_limb_ptr S) (Z.abs z) (Z.abs (scan_mp_size S))) as Hcompact.
  { unfold mpd_store_Z_compact. Exists (scan_limbs S).
    split_pure_spatial; [cancel | split_pures; dump_pre_spatial; tauto]. }
  sep_apply Hcompact.
  destruct (Z.eq_dec (scan_mp_size S) 0) as [Hz|Hnz].
  - rewrite Hz in *. simpl Z.abs in *.
    prop_apply (mpd_store_Z_compact_zero UINT_MOD (scan_limb_ptr S) (Z.abs z)).
    Intros. normalize; try cancel; try dump_pre_spatial; try lia; try tauto.
  - prop_apply (mpd_store_Z_compact_pos UINT_MOD ltac:(change (0 < 4294967296); lia)
      (scan_limb_ptr S) (Z.abs z) (Z.abs (scan_mp_size S)) ltac:(lia)).
    Intros. unfold same_sign in *. normalize; try cancel; try dump_pre_spatial; try lia; try tauto.
Qed.

Lemma scan_mpz_array_sign p count V T :
  scan_mpz_array p count V T |--
    “ forall j, 0 <= j < count -> (0 < scan_header_sizes T j <-> 0 < scan_row_values V j) ”.
Proof.
  unfold scan_mpz_array. Intros.
  prop_apply (store_array_Zlength _ scan_mpz_entry p count (combine V T)).
  rewrite Zlength_combine. Intros.
  assert (Zlength V = count /\ Zlength T = count) as [HV HT] by lia.
  intros st Hown. intros j Hj.
  pose proof (store_array_split_to_missing_i _ scan_mpz_entry p j count
    (combine V T) (0, scan_mpz_default) Hj) as Hsplit.
  rewrite Znth_combine in Hsplit by lia.
  assert (store_array scan_mpz_entry p count (combine V T) |--
    “ 0 < scan_header_sizes T j <-> 0 < scan_row_values V j ”) as Hsign.
  { sep_apply Hsplit.
    unfold scan_mpz_entry. simpl fst. simpl snd.
    prop_apply scan_mpz_at_sign.
    unfold scan_header_sizes, scan_row_values. Intros.
    normalize; try cancel; try dump_pre_spatial; try lia; try tauto. }
  exact (Hsign st Hown).
Qed.

Lemma scan_row_domain_nodup n k m R J :
  scan_row_domain n k m R J -> NoDup J.
Proof. intros [H _]. exact H. Qed.

Lemma no_positive_row_step_sentinel n v R H :
  no_positive_row n v R H -> Znth (v - n) R 0 = UINT_MAX ->
  no_positive_row n (v + 1) R H.
Proof.
  intros Hprefix Hj. apply no_positive_row_step; [exact Hprefix |].
  unfold positive_row_candidate. tauto.
Qed.

Lemma no_positive_row_step_nonpositive n v R H :
  no_positive_row n v R H -> H (Znth (v - n) R 0) <= 0 ->
  no_positive_row n (v + 1) R H.
Proof.
  intros Hprefix Hsize. apply no_positive_row_step; [exact Hprefix |].
  unfold positive_row_candidate. lia.
Qed.

Lemma first_positive_row_hit_fields n k R H v :
  n <= v < k -> no_positive_row n v R H ->
  Znth (v - n) R 0 <> UINT_MAX -> 0 < H (Znth (v - n) R 0) ->
  first_positive_row n k R H = Znth (v - n) R 0.
Proof. intros. apply first_positive_row_hit; auto. split; assumption. Qed.

Lemma first_positive_row_ext n k R H1 H2 :
  (forall v, n <= v < k -> Znth (v - n) R 0 <> UINT_MAX ->
    (0 < H1 (Znth (v - n) R 0) <-> 0 < H2 (Znth (v - n) R 0))) ->
  first_positive_row n k R H1 = first_positive_row n k R H2.
Proof.
  intros Hagree.
  assert (forall v, n <= v < k ->
    (positive_row_candidate n R H1 v <-> positive_row_candidate n R H2 v)) as Hpoint.
  { intros v Hv. unfold positive_row_candidate. specialize (Hagree v Hv). tauto. }
  destruct (Z.eq_dec (first_positive_row n k R H1) UINT_MAX) as [Heq|Hne].
  - rewrite Heq. symmetry. apply first_positive_row_none.
    apply first_positive_row_none in Heq.
    intros v Hv Hcand. apply (Heq v Hv). now apply Hpoint.
  - pose proof (proj1 (first_positive_row_minimal n k R H1 _ Hne) eq_refl) as Hmin.
    destruct Hmin as [v [Hv [Hhit [Hprefix Hrow]]]].
    rewrite Hrow. symmetry. apply first_positive_row_hit; auto.
    + intros u Hu Hcand. apply (Hprefix u Hu).
      apply Hpoint; [lia | exact Hcand].
    + now apply Hpoint.
Qed.

Lemma selection_row_at n k R v :
  0 <= n -> n <= v < k ->
  Znth (v - n) (sublist n k R) 0 = Znth v R 0.
Proof.
  intros Hn Hv. rewrite Znth_sublist by lia.
  replace (v - n + n) with v by lia. reflexivity.
Qed.

(* The set of borrowed fields is finite and contains one cell per row,
   including when several variables refer to the same row. *)
Definition scan_rows (n k : Z) (R : list Z) : list Z :=
  nodup Z.eq_dec
    (filter (fun j => negb (Z.eqb j UINT_MAX))
      (map (fun v => Znth (v - n) R 0) (Zrange n k))).

Lemma scan_rows_member n k R j :
  In j (scan_rows n k R) <->
  j <> UINT_MAX /\ exists v, n <= v < k /\ Znth (v - n) R 0 = j.
Proof.
  unfold scan_rows. rewrite nodup_In, filter_In, in_map_iff, Bool.negb_true_iff, Z.eqb_neq.
  split.
  - intros [[v [Hvalue Hrange]] Hne]. split; [exact Hne |].
    exists v. split; [now apply <- In_Zrange | exact Hvalue].
  - intros [Hne [v [Hrange Hvalue]]]. split; [|exact Hne].
    exists v. split; [exact Hvalue | now apply In_Zrange].
Qed.

Lemma selection_scan_row_domain n k m D A B R :
  0 <= n -> selection_basis m k D A B R ->
  scan_row_domain n k m (sublist n k R) (scan_rows n k (sublist n k R)).
Proof.
  intros Hn [_ [Hlookup _]]. split.
  - apply NoDup_nodup.
  - split; [apply scan_rows_member |].
    intros j Hj. apply scan_rows_member in Hj as [Hne [v [Hv Hvalue]]].
    rewrite selection_row_at in Hvalue by assumption. subst j.
    apply Hlookup; lia || assumption.
Qed.

Lemma selection_header_scan_equals_values n k m D C A B R T :
  0 <= n ->
  selection_basis m k D A B R ->
  (forall j, 0 <= j < m -> (0 < scan_header_sizes T j <-> 0 < scan_row_values C j)) ->
  first_positive_row n k (sublist n k R) (scan_header_sizes T) =
  first_positive_row n k (sublist n k R) (scan_row_values C).
Proof.
  intros Hn [_ [Hlookup _]] Hsign.
  apply first_positive_row_ext. intros v Hv Hne.
  rewrite selection_row_at in * by assumption.
  apply Hsign. apply Hlookup; lia || assumption.
Qed.

Definition selection_basic_value (D C R : list Z) (v : Z) : Q :=
  let j := Znth v R 0 in
  if Z.eqb j UINT_MAX then 0%Q
  else (inject_Z (Znth j C 0%Z) / inject_Z (Znth j D 0%Z))%Q.

Lemma selection_positive_quotient c d :
  0 < d -> ((0 < inject_Z c / inject_Z d)%Q <-> 0 < c).
Proof.
  intro Hd.
  assert (0 < inject_Z d)%Q as HdQ.
  { change (inject_Z 0 < inject_Z d)%Q. rewrite <- Zlt_Qlt. exact Hd. }
  unfold Qdiv.
  assert (0 < / inject_Z d)%Q as Hinv by (now apply Qinv_lt_0_compat).
  rewrite (Qmult_comm (inject_Z c) (/ inject_Z d)).
  rewrite <- (Qmult_0_r (/ inject_Z d)) at 1.
  rewrite Qmult_lt_l by exact Hinv.
  change ((inject_Z 0 < inject_Z c)%Q <-> 0 < c).
  now rewrite <- Zlt_Qlt.
Qed.

Lemma selection_value_positive m k D C A B R v :
  selection_basis m k D A B R -> 0 <= v < k ->
  ((0 < selection_basic_value D C R v)%Q <->
   Znth v R 0 <> UINT_MAX /\ 0 < Znth (Znth v R 0) C 0).
Proof.
  intros [Hbasic [Hrow _]] Hv.
  unfold selection_basic_value.
  destruct (Z.eqb_spec (Znth v R 0) UINT_MAX) as [Heq|Hne].
  - split; [intros H; exfalso; exact (Qlt_irrefl _ H) | tauto].
  - destruct (Hrow _ Hv Hne) as [Hj _].
    destruct (Hbasic _ Hj) as [_ [_ Hd]].
    rewrite selection_positive_quotient by exact Hd. tauto.
Qed.

Lemma valid_selection_no_positive_aux n k m D C A B R :
  0 <= n -> selection_basis m k D A B R ->
  (first_positive_row n k (sublist n k R) (scan_row_values C) = UINT_MAX <->
   forall v, n <= v < k -> (selection_basic_value D C R v <= 0)%Q).
Proof.
  intros Hn Hbasis. rewrite first_positive_row_none.
  unfold no_positive_row. split.
  - intros Hnone v Hv. apply Qnot_lt_le. intro Hpos.
    apply (Hnone v Hv). unfold positive_row_candidate, scan_row_values.
    rewrite selection_row_at by assumption.
    apply (selection_value_positive m k D C A B R v Hbasis); [lia | exact Hpos].
  - intros Hnone v Hv Hcand.
    apply (Qle_not_lt _ _ (Hnone v Hv)).
    apply (selection_value_positive m k D C A B R v Hbasis); [lia |].
    unfold positive_row_candidate, scan_row_values in Hcand.
    rewrite selection_row_at in Hcand by assumption. exact Hcand.
Qed.

Lemma valid_selection_first_aux n k m D C A B R ret :
  0 <= n -> selection_basis m k D A B R -> ret <> UINT_MAX ->
  ret = first_positive_row n k (sublist n k R) (scan_row_values C) ->
  0 <= ret < m /\ n <= Znth ret B 0 < k /\ 0 < Znth ret C 0 /\
  (0 < selection_basic_value D C R (Znth ret B 0%Z))%Q /\
  (forall v, n <= v < Znth ret B 0%Z -> (selection_basic_value D C R v <= 0)%Q).
Proof.
  intros Hn Hbasis Hne Hret.
  apply (first_positive_row_minimal _ _ _ _ _ Hne) in Hret.
  destruct Hret as [v [Hv [Hhit [Hprefix Hret]]]].
  unfold positive_row_candidate, scan_row_values in Hhit.
  rewrite selection_row_at in Hret, Hhit by assumption.
  destruct Hbasis as [Hbasic [Hlookup Hz]].
  assert (0 <= ret < m /\ Znth ret B 0 = v) as [Hbound Hb].
  { rewrite Hret. apply Hlookup; [lia | exact (proj1 Hhit)]. }
  rewrite Hb.
  split; [exact Hbound |]. split; [exact Hv |].
  split; [now rewrite Hret |]. split.
  - apply (selection_value_positive m k D C A B R v); [exact (conj Hbasic (conj Hlookup Hz)) | lia | exact Hhit].
  - intros u Hu. apply Qnot_lt_le. intros Hpos.
    apply (Hprefix u Hu). unfold positive_row_candidate, scan_row_values.
    rewrite selection_row_at by lia.
    apply (selection_value_positive m k D C A B R u); [exact (conj Hbasic (conj Hlookup Hz)) | lia | exact Hpos].
Qed.



Lemma scan_mpz_segment_sizes_frame__complete_table
    p hi H (P : Z -> bool) :
  let rem := fun p j (e : Z * scan_mpz_snapshot) =>
    if P j then
      let S := snd e in
      let a := (p + j * mpz_sizeof)%Z in
      “ Z.abs (scan_mp_size S) <= scan_mp_alloc S ” &&
      “ same_sign (fst e) (scan_mp_size S) ” &&
      “ list_to_Z UINT_MOD (scan_limbs S) = Z.abs (fst e) /\
        last (scan_limbs S) 1 >= 1 /\ list_within_bound UINT_MOD (scan_limbs S) ” &&
      “ Z.abs (scan_mp_size S) = Zlength (scan_limbs S) ” &&
      mpd_store_list (scan_limb_ptr S) (scan_limbs S) **
      UIntArray.undef_seg (scan_limb_ptr S) (Z.abs (scan_mp_size S)) (scan_mp_alloc S) **
      &(a # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> scan_mp_alloc S **
      &(a # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> scan_limb_ptr S
    else scan_mpz_entry p j e in
  forall L lo J,
    Zlength L = hi - lo ->
    NoDup J ->
    (forall j, In j J -> lo <= j < hi) ->
    (forall j, lo <= j < hi -> (P j = true <-> In j J)) ->
    (forall j, lo <= j < hi ->
      H j = scan_mp_size (snd (Znth (j - lo) L (0, scan_mpz_default)))) ->
    store_array_rec scan_mpz_entry p lo hi L --||--
      scan_size_fields p J H ** store_array_rec rem p lo hi L.
Proof.
  intros rem L. induction L as [|e L IH]; intros lo J Hlen Hdup Hbounds Hmask Hsize.
  - rewrite Zlength_nil in Hlen.
    destruct J as [|j J].
    + replace lo with hi by lia.
      cbn [scan_size_fields store_array_rec fold_right].
      split; Intros; split_pure_spatial;
        [cancel | split_pures; dump_pre_spatial; reflexivity
        |cancel | split_pures; dump_pre_spatial; reflexivity].
    + specialize (Hbounds j (or_introl eq_refl)). lia.
  - rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg L).
    assert (Hlo : lo <= lo < hi) by lia.
    assert (Htail_size : forall j, lo + 1 <= j < hi ->
      H j = scan_mp_size (snd (Znth (j - (lo + 1)) L (0, scan_mpz_default)))).
    { intros j Hj. rewrite (Hsize j ltac:(lia)).
      rewrite Znth_cons by lia.
      replace (j - lo - 1) with (j - (lo + 1)) by lia.
      reflexivity. }
    cbn [store_array_rec].
    destruct (P lo) eqn:Hselected.
    + assert (Hmember : In lo J) by (apply (Hmask lo Hlo); assumption).
      assert (Hlo_size : H lo = scan_mp_size (snd e)).
      { specialize (Hsize lo Hlo). rewrite Z.sub_diag, Znth0_cons in Hsize.
        exact Hsize. }
      assert (Hhead : scan_mpz_entry p lo e --||-- scan_size_cell p lo (H lo) ** rem p lo e).
      { unfold rem, scan_mpz_entry, scan_mpz_at, scan_size_cell.
        rewrite Hselected, Hlo_size. split; Intros;
          split_pure_spatial; [cancel | split_pures; dump_pre_spatial; tauto
                              |cancel | split_pures; dump_pre_spatial; tauto]. }
      assert (Htail_member : forall j, lo + 1 <= j < hi ->
        (P j = true <-> In j (scan_other_rows lo J))).
      { intros j Hj. rewrite (Hmask j ltac:(lia)). unfold scan_other_rows.
        split; intro Hin.
        - apply in_in_remove; [lia | exact Hin].
        - apply in_remove in Hin. tauto. }
      assert (Htail_bounds : forall j, In j (scan_other_rows lo J) -> lo + 1 <= j < hi).
      { intros j Hj. unfold scan_other_rows in Hj. apply in_remove in Hj as [Hin Hne].
        specialize (Hbounds j Hin). lia. }
      assert (Htail_dup : NoDup (scan_other_rows lo J)).
      { unfold scan_other_rows. clear - Hdup.
        induction Hdup as [|j J Hnot Hdup IHdup].
        - constructor.
        - cbn [remove]. destruct (Z.eq_dec lo j); [exact IHdup |].
          constructor; [intro Hin; apply Hnot; apply in_remove in Hin; tauto | exact IHdup]. }
      pose proof (IH (lo + 1) (scan_other_rows lo J) ltac:(lia)
        Htail_dup Htail_bounds Htail_member Htail_size) as Htail.
      pose proof (scan_size_fields_focus p J H lo Hdup Hmember) as Hfields.
      rewrite Hhead, Htail, Hfields. split; sepcon_right_assoc; cancel.
    + assert (Htail_bounds : forall j, In j J -> lo + 1 <= j < hi).
      { intros j Hj. specialize (Hbounds j Hj).
        assert (j <> lo).
        { intro Heq. subst j. apply (Hmask lo Hlo) in Hj. congruence. }
        lia. }
      assert (Hhead : rem p lo e = scan_mpz_entry p lo e)
        by (unfold rem; rewrite Hselected; reflexivity).
      pose proof (IH (lo + 1) J ltac:(lia) Hdup Htail_bounds
        ltac:(intros; apply Hmask; lia) Htail_size) as Htail.
      rewrite Hhead, Htail. split; sepcon_right_assoc; cancel.
Qed.
Lemma scan_mpz_array_sizes_frame__complete_table p count V T J :
  NoDup J -> (forall j, In j J -> 0 <= j < count) ->
  Zlength V = count -> Zlength T = count ->
  scan_mpz_array p count V T |--
  scan_size_fields p J (scan_header_sizes T) **
  (scan_size_fields p J (scan_header_sizes T) -* scan_mpz_array p count V T).
Proof.
  intros Hdup Hbounds HV HT.
  set (P := fun j => if in_dec Z.eq_dec j J then true else false).
  assert (Hlen : Zlength (combine V T) = count)
    by (rewrite Zlength_combine, HV, HT, Z.min_id; reflexivity).
  assert (Hmask : forall j, 0 <= j < count -> (P j = true <-> In j J)).
  { intros j _. unfold P. destruct (in_dec Z.eq_dec j J); intuition congruence. }
  assert (Hsize : forall j, 0 <= j < count ->
    scan_header_sizes T j =
      scan_mp_size (snd (Znth (j - 0) (combine V T) (0, scan_mpz_default)))).
  { intros j Hj. unfold scan_header_sizes. rewrite Z.sub_0_r, Znth_combine by lia.
    reflexivity. }
  pose proof (scan_mpz_segment_sizes_frame__complete_table p count (scan_header_sizes T) P
    (combine V T) 0 J ltac:(lia) Hdup Hbounds Hmask Hsize) as Hsplit.
  cbn zeta in Hsplit. destruct Hsplit as [Hopen Hclose].
  change ((“ Zlength V = Zlength T ” &&
    store_array_rec scan_mpz_entry p 0 count (combine V T)) |--
    scan_size_fields p J (scan_header_sizes T) **
    (scan_size_fields p J (scan_header_sizes T) -* scan_mpz_array p count V T)).
  Intros.
  sep_apply_l_atomic Hopen.
  cancel (scan_size_fields p J (scan_header_sizes T)).
  apply_sepcon_adjoint.
  sep_apply_l_atomic Hclose.
  unfold scan_mpz_array, store_array.
  split_pure_spatial; [cancel | dump_pre_spatial; lia].
Qed.
