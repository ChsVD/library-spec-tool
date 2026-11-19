From Coq Require Import ZArith List String Lia QArith Lra.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic CommonAssertion ArrayLibCore.
From SumLib Require Import ZRange.
From SimpleC.EE.Applications_human.simplex_gmp_minimal Require Import
  integers_fme_model_lib violated_fme_model_selection_lib.

Import naive_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac.

(* H indexes coefficients or headers in the flattened matrix. *)
Definition entering_row (r k : Z) (H : Z -> Z) (v : Z) : Z :=
  H (r * k + v).

(* R is the complete row map; H indexes only the selected row by column. *)
Definition entering_candidate (n : Z) (R : list Z) (H : Z -> Z) (v : Z) : Prop :=
  Znth v R 0 = UINT_MAX /\
  (if v <? n then H v <> 0 else 0 < H v).

Definition entering_candidateb (n : Z) (R : list Z) (H : Z -> Z) (v : Z) : bool :=
  (Znth v R 0 =? UINT_MAX) &&
  (if v <? n then negb (H v =? 0) else 0 <? H v).

(* The first candidate column in increasing order, or the 32-bit sentinel. *)
Definition first_entering (n k : Z) (R : list Z) (H : Z -> Z) : Z :=
  match find (entering_candidateb n R H) (Zrange 0 k) with
  | Some v => v
  | None => UINT_MAX
  end.

Definition no_entering (n end_column : Z) (R : list Z) (H : Z -> Z) : Prop :=
  forall v, 0 <= v < end_column -> ~ entering_candidate n R H v.

Lemma entering_candidateb_true n R H v :
  entering_candidateb n R H v = true <-> entering_candidate n R H v.
Proof.
  unfold entering_candidateb, entering_candidate.
  rewrite Bool.andb_true_iff, Z.eqb_eq.
  destruct (v <? n); [rewrite Bool.negb_true_iff, Z.eqb_neq | rewrite Z.ltb_lt];
    reflexivity.
Qed.

Lemma no_entering_start n R H : no_entering n 0 R H.
Proof. unfold no_entering; intros; lia. Qed.

Lemma no_entering_step n v R H :
  no_entering n v R H -> ~ entering_candidate n R H v -> no_entering n (v + 1) R H.
Proof.
  unfold no_entering. intros Hprefix Hv u Hu.
  destruct (Z.eq_dec u v) as [->|Hne]; [exact Hv | apply Hprefix; lia].
Qed.

Lemma no_entering_step_basic n v R H :
  no_entering n v R H -> Znth v R 0 <> UINT_MAX -> no_entering n (v + 1) R H.
Proof. intros. apply no_entering_step; [assumption | unfold entering_candidate; tauto]. Qed.

Lemma no_entering_step_original n v R H :
  no_entering n v R H -> v < n -> H v = 0 -> no_entering n (v + 1) R H.
Proof.
  intros Hprefix Hv Hz. apply no_entering_step; [assumption |].
  unfold entering_candidate. apply Z.ltb_lt in Hv. rewrite Hv. tauto.
Qed.

Lemma no_entering_step_auxiliary n v R H :
  no_entering n v R H -> n <= v -> H v <= 0 -> no_entering n (v + 1) R H.
Proof.
  intros Hprefix Hv Hz. apply no_entering_step; [assumption |].
  unfold entering_candidate. apply Z.ltb_ge in Hv. rewrite Hv. intros [_ Hlt]. lia.
Qed.

Lemma first_entering_none n k R H :
  k <= UINT_MAX -> (first_entering n k R H = UINT_MAX <-> no_entering n k R H).
Proof.
  intros Hmax. unfold first_entering, no_entering.
  destruct (find (entering_candidateb n R H) (Zrange 0 k)) as [v|] eqn:Hfind.
  - apply find_some in Hfind as [Hin Htest].
    apply <- In_Zrange in Hin. apply entering_candidateb_true in Htest.
    split.
    + intro Hbad. lia.
    + intro Hbad. exact (False_rect _ (Hbad v Hin Htest)).
  - split; [intros _ v Hv Hcand | reflexivity].
    apply In_Zrange in Hv. apply entering_candidateb_true in Hcand.
    pose proof (find_none _ _ Hfind v Hv). congruence.
Qed.

Lemma first_entering_empty n R H : first_entering n 0 R H = UINT_MAX.
Proof. reflexivity. Qed.

Lemma first_entering_hit n k R H v :
  0 <= v < k -> no_entering n v R H -> entering_candidate n R H v ->
  first_entering n k R H = v.
Proof.
  intros Hv Hprefix Hhit.
  unfold first_entering.
  rewrite (find_Zrange_first _ 0 k v Hv); [reflexivity | |].
  - now apply entering_candidateb_true.
  - intros u Hu. destruct (entering_candidateb n R H u) eqn:Htest; [|reflexivity].
    exfalso. apply entering_candidateb_true in Htest. exact (Hprefix _ Hu Htest).
Qed.

Lemma first_entering_hit_original n k R H v :
  0 <= v < k -> no_entering n v R H -> Znth v R 0 = UINT_MAX ->
  v < n -> H v <> 0 -> first_entering n k R H = v.
Proof.
  intros Hv Hprefix Hr Hn Hsize.
  apply first_entering_hit; try assumption.
  unfold entering_candidate. apply Z.ltb_lt in Hn. rewrite Hn. auto.
Qed.

Lemma first_entering_hit_auxiliary n k R H v :
  0 <= v < k -> no_entering n v R H -> Znth v R 0 = UINT_MAX ->
  n <= v -> 0 < H v -> first_entering n k R H = v.
Proof.
  intros Hv Hprefix Hr Hn Hsize.
  apply first_entering_hit; try assumption.
  unfold entering_candidate. apply Z.ltb_ge in Hn. rewrite Hn. auto.
Qed.

Lemma first_entering_minimal n k R H ret :
  ret <> UINT_MAX ->
  (ret = first_entering n k R H <->
   0 <= ret < k /\ entering_candidate n R H ret /\ no_entering n ret R H).
Proof.
  intros Hne. split.
  - unfold first_entering.
    destruct (find (entering_candidateb n R H) (Zrange 0 k)) as [v|] eqn:Hfind;
      [|contradiction].
    intros ->. pose proof (find_some _ _ Hfind) as [Hin Htest].
    split; [now apply <- In_Zrange |].
    split; [now apply entering_candidateb_true |].
    intros u Hu Hcand. apply entering_candidateb_true in Hcand.
    pose proof (find_Zrange_prefix _ _ _ _ Hfind u Hu). congruence.
  - intros [Hv [Hhit Hprefix]]. symmetry. now apply first_entering_hit.
Qed.

Lemma entering_candidate_nonzero n R H v :
  entering_candidate n R H v -> H v <> 0.
Proof. unfold entering_candidate. destruct (v <? n); intros [_ Hsign]; lia. Qed.

Lemma first_entering_same_signs n k R H1 H2 :
  (forall v, 0 <= v < k -> (H1 v = 0 <-> H2 v = 0) /\ (0 < H1 v <-> 0 < H2 v)) ->
  first_entering n k R H1 = first_entering n k R H2.
Proof.
  intros Hsign. unfold first_entering.
  assert (Htest: forall v, In v (Zrange 0 k) ->
      entering_candidateb n R H1 v = entering_candidateb n R H2 v).
  { intros v Hv. apply <- In_Zrange in Hv.
    specialize (Hsign v Hv).
    assert (entering_candidate n R H1 v <-> entering_candidate n R H2 v) as Hcand.
    { unfold entering_candidate. destruct (v <? n); tauto. }
    rewrite <- !entering_candidateb_true in Hcand.
    destruct (entering_candidateb n R H1 v), (entering_candidateb n R H2 v);
      intuition discriminate. }
  assert (forall l, (forall v, In v l ->
      entering_candidateb n R H1 v = entering_candidateb n R H2 v) ->
      find (entering_candidateb n R H1) l = find (entering_candidateb n R H2) l) as Hfind.
  { induction l as [|a l IH]; intros Hext; [reflexivity |].
    simpl. rewrite (Hext a (or_introl eq_refl)).
    destruct (entering_candidateb n R H2 a); [reflexivity |].
    apply IH. intros v Hv. apply Hext. right. exact Hv. }
  now rewrite (Hfind _ Htest).
Qed.

(* The selected row cannot move a positive basic auxiliary toward zero
   when the free original terms vanish and all auxiliary coefficients are nonpositive. *)
Definition entering_blocked_row (n k r : Z) (A : list Z) : Prop :=
  forall v, 0 <= v < k ->
    let a := Znth (r * k + v) A 0 in
    if v <? n then a = 0 else a <= 0.

Lemma first_entering_blocked_row n m k r D A B R :
  0 <= r < m -> k <= UINT_MAX -> selection_basis m k D A B R ->
  first_entering n k R (entering_row r k (scan_row_values A)) = UINT_MAX ->
  entering_blocked_row n k r A.
Proof.
  intros Hr Hmax [_ [Hrow Hbasic]] Hnone.
  apply (first_entering_none n k R _ Hmax) in Hnone.
  intros v Hv. cbn zeta.
  destruct (Z.eq_dec (Znth v R 0) UINT_MAX) as [Hs|Hb].
  - specialize (Hnone _ Hv).
    unfold entering_candidate, entering_row, scan_row_values in Hnone.
    rewrite Hs in Hnone.
    destruct (v <? n); lia.
  - destruct (Hrow v Hv Hb) as [Hindex Hcolumn].
    specialize (Hbasic _ _ Hr Hindex).
    rewrite Hcolumn in Hbasic. rewrite Hbasic.
    destruct (v <? n); lia.
Qed.

(* This row obstruction is independent of the uninspected rows.  The
   summand is zero in every free original column, and nonnegative in each
   auxiliary column of a putative solution. *)
Lemma entering_blocked_row_not_feasible n m k r D C A B R :
  0 <= r < m -> selection_basis m k D A B R ->
  n <= Znth r B 0 -> 0 < Znth r C 0 -> entering_blocked_row n k r A ->
  ~ exists x : Z -> Q,
    (forall v, n <= v < k -> (x v <= 0)%Q) /\
    (forall j, 0 <= j < m ->
      (inject_Z (Znth j D 0%Z) * x (Znth j B 0%Z) ==
       inject_Z (Znth j C 0%Z) +
       fold_right Qplus 0
         (map (fun v => inject_Z (Znth (j * k + v)%Z A 0%Z) * x v) (Zrange 0%Z k)))%Q).
Proof.
  intros Hr [Hbasic _] Haux Hpositive Hblocked [x [Hauxbound Heq]].
  destruct (Hbasic r Hr) as [Hbr [_ HD]].
  specialize (Heq r Hr).
  assert ((x (Znth r B 0%Z) <= 0)%Q) as Hx by (apply Hauxbound; lia).
  assert ((0 < inject_Z (Znth r D 0%Z))%Q) as HDq by (change ((inject_Z 0 < inject_Z (Znth r D 0%Z))%Q); rewrite <- Zlt_Qlt; exact HD).
  assert ((0 < inject_Z (Znth r C 0%Z))%Q) as HCq.
  { change ((inject_Z 0 < inject_Z (Znth r C 0%Z))%Q). rewrite <- Zlt_Qlt. exact Hpositive. }
  assert (forall v, In v (Zrange 0 k) ->
    (0 <= inject_Z (Znth (r * k + v) A 0%Z) * x v)%Q) as Hterm.
  { intros v Hv. apply <- In_Zrange in Hv.
    specialize (Hblocked _ Hv). cbn zeta in Hblocked.
    destruct (v <? n) eqn:Hn.
    - rewrite Hblocked. change (0 <= 0 * x v)%Q. rewrite Qmult_0_l. apply Qle_refl.
    - apply Z.ltb_ge in Hn.
      assert ((inject_Z (Znth (r * k + v) A 0%Z) <= 0)%Q) as HAq.
      { change ((inject_Z (Znth (r * k + v) A 0%Z) <= inject_Z 0)%Q). rewrite <- Zle_Qle. exact Hblocked. }
      specialize (Hauxbound v ltac:(lia)).
      set (a := inject_Z (Znth (r * k + v) A 0%Z)) in *.
      assert (0 <= -a)%Q as Ha by (change (-0 <= -a)%Q; now apply Qopp_le_compat).
      assert (0 <= -(x v))%Q as Hxv by (change (-0 <= -(x v))%Q; now apply Qopp_le_compat).
      pose proof (Qmult_le_0_compat _ _ Ha Hxv) as Hproduct.
      setoid_replace ((-a) * (-(x v)))%Q with (a * x v)%Q in Hproduct by ring.
      exact Hproduct. }
  assert (forall cols, (forall v, In v cols ->
    (0 <= inject_Z (Znth (r * k + v) A 0%Z) * x v)%Q) ->
    (0 <= fold_right Qplus 0
      (map (fun v => inject_Z (Znth (r * k + v) A 0%Z) * x v) cols))%Q) as Hsum.
  { induction cols as [|v cols IH]; intros Hall; simpl; [apply Qle_refl |].
    pose proof (Hall v (or_introl eq_refl)).
    specialize (IH ltac:(intros; apply Hall; right; assumption)).
    rewrite <- (Qplus_0_r 0) at 1. now apply Qplus_le_compat. }
  specialize (Hsum _ Hterm).
  apply (Qmult_le_l _ _ _ HDq) in Hx. rewrite Qmult_0_r in Hx.
  rewrite Heq in Hx.
  apply (Qle_not_lt _ _ Hx).
  rewrite <- (Qplus_0_r 0) at 1.
  now apply Qplus_lt_le_compat.
Qed.

(* The full snapshot exposes zero and strict-positive equivalence to
   mathematical coefficients for every initialized head in the array. *)
Lemma entering_array_signs p count V T :
  scan_mpz_array p count V T |--
  “ forall j, 0 <= j < count ->
    (scan_header_sizes T j = 0 <-> scan_row_values V j = 0) /\
    (0 < scan_header_sizes T j <-> 0 < scan_row_values V j) ”.
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
    “ (scan_header_sizes T j = 0 <-> scan_row_values V j = 0) /\
      (0 < scan_header_sizes T j <-> 0 < scan_row_values V j) ”) as Hsign.
  { sep_apply Hsplit.
    unfold scan_mpz_entry. simpl fst. simpl snd.
    prop_apply scan_mpz_at_sign.
    unfold scan_header_sizes, scan_row_values. Intros.
    normalize; try cancel; try dump_pre_spatial; try lia; try tauto. }
  exact (Hsign st Hown).
Qed.

Lemma entering_array_row_frame p m k r V T :
  0 <= r < m -> 0 < k ->
  Zlength V = m * k -> Zlength T = m * k ->
  scan_mpz_array p (m * k) V T |--
  scan_size_fields p (Zrange (r * k) (r * k + k)) (scan_header_sizes T) **
  (scan_size_fields p (Zrange (r * k) (r * k + k)) (scan_header_sizes T) -*
   scan_mpz_array p (m * k) V T).
Proof.
  intros Hr Hk HV HT.
  apply scan_mpz_array_sizes_frame__complete_table;
    try assumption; [apply NoDup_Zrange |].
  intros j Hj. apply <- In_Zrange in Hj. nia.
Qed.

Lemma entering_row_cell_focus p r k H v :
  0 <= v < k ->
  scan_size_fields p (Zrange (r * k) (r * k + k)) H --||--
  scan_size_cell p (r * k + v) (H (r * k + v)) **
  scan_size_fields p (scan_other_rows (r * k + v) (Zrange (r * k) (r * k + k))) H.
Proof.
  intros Hv. apply scan_size_fields_focus; [apply NoDup_Zrange |].
  apply In_Zrange. lia.
Qed.

(* The object span bounds imply that both stages of the unsigned
   row-major index fit the GMP-FME size_t model. *)
Lemma entering_index_bounds r k v :
  simplex_mpz_layout -> 0 <= r -> 0 <= v < k ->
  (r * k + k) * sizeof("__mpz_struct") <= INT_MAX ->
  0 <= r * k /\ r * k + v <= UINT_MAX.
Proof.
  intros [Hsize _] Hr Hv Hbytes.
  rewrite Hsize in Hbytes.
  change ((r * k + k) * 12 <= 2147483647) in Hbytes.
  change (0 <= r * k /\ r * k + v <= 4294967295).
  nia.
Qed.

Lemma entering_prefix_bounds m k r :
  simplex_mpz_layout -> 0 <= r < m -> 0 < k ->
  m * k * sizeof("__mpz_struct") <= INT_MAX ->
  r <= UINT_MAX /\ (r * k + k) * sizeof("__mpz_struct") <= INT_MAX.
Proof.
  intros [Hsize _] Hr Hk Hbytes.
  rewrite Hsize in *.
  change (m * k * 12 <= 2147483647) in Hbytes.
  change (r <= 4294967295 /\ (r * k + k) * 12 <= 2147483647).
  split.
  - assert (m <= m * k) by nia. lia.
  - assert (r * k + k <= m * k) by nia. lia.
Qed.

(* A field-level miss gives sign restrictions for every nonbasic column. *)
Lemma first_entering_no_match_signs n k R H :
  k <= UINT_MAX -> first_entering n k R H = UINT_MAX ->
  forall v, 0 <= v < k -> Znth v R 0 = UINT_MAX ->
  if v <? n then H v = 0 else H v <= 0.
Proof.
  intros Hmax Hnone v Hv Hsentinel.
  apply (first_entering_none n k R H Hmax) in Hnone.
  specialize (Hnone v Hv). unfold entering_candidate in Hnone.
  rewrite Hsentinel in Hnone. destruct (v <? n); lia.
Qed.
