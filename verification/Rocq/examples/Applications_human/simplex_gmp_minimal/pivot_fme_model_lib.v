From Coq Require Import ZArith List String Lia QArith.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic CommonAssertion ArrayLibCore.
From SumLib Require Import ZRange.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_lib.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_lib.
From SimpleC.EE.Applications_human.simplex_gmp_minimal Require Import
  integers_fme_model_lib violated_fme_model_selection_lib.

Import naive_C_Rules ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope sac.

(* Entry coefficients are a flattened row-major list. *)
Definition pivot_coef (A : list Z) (k i v : Z) : Z := Znth (i * k + v) A 0.

Definition pivot_orientation (h : Z) : Z := if 0 <? h then 1 else -1.

Definition pivot_row_constant (h c : Z) : Z := - pivot_orientation h * c.

Definition pivot_row_coef (e b h d v value : Z) : Z :=
  if v =? e then 0 else
  if v =? b then pivot_orientation h * d else
  - pivot_orientation h * value.

(* Row multipliers are exact quotients for a nonzero row coefficient and
   a nonzero pivot. The second multiplier retains the row coefficient sign. *)
Definition pivot_row_scale (h x : Z) : Z := Z.quot (Z.abs h) (Z.gcd (Z.abs h) x).
Definition pivot_row_add (h x : Z) : Z := Z.quot x (Z.gcd (Z.abs h) x).

Definition pivot_denominators (m k r e : Z) (D A : list Z) : list Z :=
  let h := pivot_coef A k r e in
  map (fun i =>
    let x := pivot_coef A k i e in
    if i =? r then Z.abs h else if x =? 0 then Znth i D 0
    else pivot_row_scale h x * Znth i D 0) (Zrange 0 m).

Definition pivot_constants (m k r e : Z) (C A : list Z) : list Z :=
  let h := pivot_coef A k r e in
  let c := pivot_row_constant h (Znth r C 0) in
  map (fun i =>
    let x := pivot_coef A k i e in
    if i =? r then c else if x =? 0 then Znth i C 0
    else pivot_row_scale h x * Znth i C 0 + pivot_row_add h x * c) (Zrange 0 m).

Definition pivot_coefficient_at (k r e : Z) (D A B : list Z) (i v : Z) : Z :=
  let h := pivot_coef A k r e in
  let x := pivot_coef A k i e in
  let entry := pivot_coef A k i v in
  let b := Znth r B 0 in
  let pr := pivot_row_coef e b h (Znth r D 0) v (pivot_coef A k r v) in
  if i =? r then pr else if x =? 0 then entry else if v =? e then 0
  else pivot_row_scale h x * entry + pivot_row_add h x * pr.

Definition pivot_coefficients (m k r e : Z) (D A B : list Z) : list Z :=
  map (fun j => pivot_coefficient_at k r e D A B (j / k) (j mod k))
    (Zrange 0 (m * k)).

Definition pivot_basic (r e : Z) (B : list Z) : list Z := replace_Znth r e B.

Definition pivot_row_map (r e : Z) (B R : list Z) : list Z :=
  replace_Znth (Znth r B 0) UINT_MAX (replace_Znth e r R).

Definition integer_pivot_compute (m k r e : Z) (D C A B R : list Z)
    : list Z * list Z * list Z * list Z * list Z :=
  (pivot_denominators m k r e D A, pivot_constants m k r e C A,
   pivot_coefficients m k r e D A B, pivot_basic r e B, pivot_row_map r e B R).

(* Exactly the rational table equation used by selection_equations. *)
Definition pivot_table_equations (m k : Z) (D C A B : list Z) (x : Z -> Q) : Prop :=
  forall i, 0 <= i < m ->
    (inject_Z (Znth i D 0%Z) * x (Znth i B 0%Z) ==
     inject_Z (Znth i C 0%Z) +
     fold_right Qplus 0
       (map (fun v => inject_Z (pivot_coef A k i v) * x v) (Zrange 0 k)))%Q.

Definition pivot_equations_equivalent (m k : Z) (D C A B Dnext Cnext Anext Bnext : list Z) : Prop :=
  forall x : Z -> Q,
    pivot_table_equations m k D C A B x <->
    pivot_table_equations m k Dnext Cnext Anext Bnext x.

(* [AN] differs from the entry matrix only on the already negated columns. *)
Definition pivot_negated_prefix (m k r v : Z) (A AN : list Z) : Prop :=
  forall j, 0 <= j < m * k ->
    Znth j AN 0 = if andb (r * k <=? j) (j <? r * k + v)
      then - Znth j A 0 else Znth j A 0.

(* Finished elimination rows, plus the pivot row, have their final values. *)
Definition pivot_rows_done (m k r e i : Z) (D C A B DL CL AL : list Z) : Prop :=
  (forall j, 0 <= j < m ->
    let done := orb (j =? r) (j <? i) in
    Znth j DL 0 = (if done then Znth j (pivot_denominators m k r e D A) 0
                            else Znth j D 0) /\
    Znth j CL 0 = (if done then Znth j (pivot_constants m k r e C A) 0
                            else Znth j C 0)) /\
  (forall j v, 0 <= j < m -> 0 <= v < k ->
    pivot_coef AL k j v = if orb (j =? r) (j <? i)
      then pivot_coefficient_at k r e D A B j v else pivot_coef A k j v).

(* During elimination the active row's entering coefficient is still its old
   value. All other already visited columns are final. *)
Definition pivot_combined_prefix (m k r e i next : Z)
    (D A B AL AN : list Z) : Prop :=
  forall j v, 0 <= j < m -> 0 <= v < k ->
    pivot_coef AN k j v = if andb (andb (j =? i) (v <? next)) (negb (v =? e))
      then pivot_coefficient_at k r e D A B i v else pivot_coef AL k j v.

(* Same base and absolute indices as MpzArray.full. Each remaining range is
   contiguous; using min and max handles i<r and r<i uniformly. *)
Definition pivot_two_missing (p count a b : Z) (values : list Z) : Assertion :=
  let lo := Z.min a b in
  let hi := Z.max a b in
  store_array_rec fme_gmp_lib.mpz_store p 0 lo (sublist 0 lo values) **
  store_array_rec fme_gmp_lib.mpz_store p (lo + 1) hi (sublist (lo + 1) hi values) **
  store_array_rec fme_gmp_lib.mpz_store p (hi + 1) count (sublist (hi + 1) count values).

(* Keep the original divexact precondition while preventing its equality
   from being substituted recursively by the C contract matcher. *)
Definition pivot_divides_exactly (num den : Z) : Prop :=
  num = Z.quot num den * den.

(* This is precisely the pure equality emitted by the original annotation's
   slash, which QCP maps to Z.quot. It changes neither nonnull premise nor
   the three store_Z resources. *)
Lemma pivot_divexact_require_equiv q num den old zn zd :
  (“ q <> 0 ” && “ zd <> 0 ” && “ pivot_divides_exactly zn zd ” &&
    store_Z q old ** store_Z num zn ** store_Z den zd) =
  (“ q <> 0 ” && “ zd <> 0 ” && “ zn = Z.quot zn zd * zd ” &&
    store_Z q old ** store_Z num zn ** store_Z den zd).
Proof. reflexivity. Qed.

(* GCD exactness works for either sign of the second numerator. *)
Lemma pivot_gcd_exact a b :
  0 < a ->
  let g := Z.gcd a b in
  0 < g /\ pivot_divides_exactly a g /\ pivot_divides_exactly b g.
Proof.
  intro Ha. fold (Z.gcd a b). cbn zeta.
  assert (Hg : 0 < Z.gcd a b).
  { pose proof (Z.gcd_nonneg a b).
    assert (Z.gcd a b <> 0).
    { intro Hz. apply Z.gcd_eq_0_l in Hz. lia. }
    lia. }
  split; [exact Hg |].
  assert (Hex : forall t d, d <> 0 -> (d | t) -> pivot_divides_exactly t d).
  { intros t d Hd [u Hu]. unfold pivot_divides_exactly.
    rewrite Hu, Z.quot_mul by exact Hd. reflexivity. }
  split; apply Hex; try lia; [apply Z.gcd_divide_l | apply Z.gcd_divide_r].
Qed.

Lemma pivot_row_multipliers h x :
  h <> 0 ->
  let p := Z.abs h in
  let g := Z.gcd p x in
  0 < g /\
  0 < pivot_row_scale h x /\
  p = pivot_row_scale h x * g /\ x = pivot_row_add h x * g.
Proof.
  intro Hh. cbn zeta.
  assert (Hp : 0 < Z.abs h) by (apply Z.abs_pos; lia).
  destruct (pivot_gcd_exact (Z.abs h) x Hp) as [Hg [HexP HexX]].
  unfold pivot_divides_exactly in *. unfold pivot_row_scale, pivot_row_add.
  repeat split; try assumption. nia.
Qed.

Lemma pivot_range_aux_length start count :
  Zlength (Zrange_aux start count) = Z.of_nat count.
Proof.
  revert start. induction count as [|count IH]; intro start.
  - reflexivity.
  - cbn [Zrange_aux]. rewrite Zlength_cons, IH. lia.
Qed.

Lemma pivot_range_length bound : 0 <= bound -> Zlength (Zrange 0 bound) = bound.
Proof.
  intro Hbound. unfold Zrange. rewrite pivot_range_aux_length. lia.
Qed.

Lemma pivot_range_aux_at start count j :
  0 <= j < Z.of_nat count -> Znth j (Zrange_aux start count) 0 = start + j.
Proof.
  revert start j. induction count as [|count IH]; intros start j Hj; [lia |].
  cbn [Zrange_aux].
  destruct (Z.eq_dec j 0) as [-> | Hnz].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia. rewrite IH by lia. lia.
Qed.

Lemma pivot_map_range_at f bound j :
  0 <= j < bound -> Znth j (map f (Zrange 0 bound)) 0 = f j.
Proof.
  intro Hj. rewrite (Znth_map f _ _ 0) by (rewrite pivot_range_length; lia).
  unfold Zrange. rewrite pivot_range_aux_at by lia. now replace (0 + j) with j by lia.
Qed.

Lemma pivot_denominator_index m k r e D A i :
  0 <= i < m ->
  let h := pivot_coef A k r e in
  let x := pivot_coef A k i e in
  Znth i (pivot_denominators m k r e D A) 0 =
    if i =? r then Z.abs h else if x =? 0 then Znth i D 0
    else pivot_row_scale h x * Znth i D 0.
Proof. intro Hi. unfold pivot_denominators. now rewrite pivot_map_range_at. Qed.

Lemma pivot_constant_index m k r e C A i :
  0 <= i < m ->
  let h := pivot_coef A k r e in
  let x := pivot_coef A k i e in
  let c := pivot_row_constant h (Znth r C 0) in
  Znth i (pivot_constants m k r e C A) 0 =
    if i =? r then c else if x =? 0 then Znth i C 0
    else pivot_row_scale h x * Znth i C 0 + pivot_row_add h x * c.
Proof. intro Hi. unfold pivot_constants. now rewrite pivot_map_range_at. Qed.

Lemma pivot_coefficients_index m k r e D A B i v :
  0 <= i < m -> 0 <= v < k ->
  pivot_coef (pivot_coefficients m k r e D A B) k i v =
    pivot_coefficient_at k r e D A B i v.
Proof.
  intros Hi Hv. unfold pivot_coef at 1. unfold pivot_coefficients.
  rewrite pivot_map_range_at by nia.
  replace (i * k + v) with (v + i * k) by ring.
  rewrite Z.div_add by lia. rewrite Z.mod_add by lia.
  rewrite Z.div_small by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma pivot_output_lengths m k r e D C A B R :
  0 <= m -> 0 <= k ->
  Zlength (pivot_denominators m k r e D A) = m /\
  Zlength (pivot_constants m k r e C A) = m /\
  Zlength (pivot_coefficients m k r e D A B) = m * k /\
  Zlength (pivot_basic r e B) = Zlength B /\
  Zlength (pivot_row_map r e B R) = Zlength R.
Proof.
  intros Hm Hk. unfold pivot_denominators, pivot_constants, pivot_coefficients,
    pivot_basic, pivot_row_map.
  repeat rewrite Zlength_map. repeat rewrite pivot_range_length by nia.
  repeat rewrite Zlength_replace_Znth. tauto.
Qed.

Lemma pivot_list_ext (xs ys : list Z) n :
  Zlength xs = n -> Zlength ys = n ->
  (forall j, 0 <= j < n -> Znth j xs 0 = Znth j ys 0) ->
  xs = ys.
Proof.
  intros Hx Hy H. apply nth_ext with (d := 0) (d' := 0).
  - rewrite Zlength_correct in Hx, Hy. lia.
  - intros idx Hidx. specialize (H (Z.of_nat idx)).
    rewrite Zlength_correct in Hx.
    unfold Znth in H. rewrite Nat2Z.id in H.
    apply H. lia.
Qed.

Lemma pivot_matrix_ext m k (xs ys : list Z) :
  0 <= m -> 0 < k ->
  Zlength xs = m * k -> Zlength ys = m * k ->
  (forall i j, 0 <= i < m -> 0 <= j < k -> pivot_coef xs k i j = pivot_coef ys k i j) ->
  xs = ys.
Proof.
  intros Hm Hk Hxs Hys Hcells.
  eapply pivot_list_ext; [exact Hxs | exact Hys |].
  intros t Ht. pose proof (Z.div_mod t k ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound t k Hk) as Hmod.
  assert (0 <= t / k < m) as Hrow by nia.
  specialize (Hcells (t / k) (t mod k) Hrow Hmod).
  unfold pivot_coef in Hcells.
  replace (t / k * k + t mod k) with t in Hcells by nia.
  exact Hcells.
Qed.

Lemma pivot_rows_done_complete m k r e D C A B DL CL AL :
  0 <= m -> 0 < k ->
  Zlength DL = m -> Zlength CL = m -> Zlength AL = m * k ->
  pivot_rows_done m k r e m D C A B DL CL AL ->
  DL = pivot_denominators m k r e D A /\
  CL = pivot_constants m k r e C A /\
  AL = pivot_coefficients m k r e D A B.
Proof.
  intros Hm Hk Hd Hc Ha [Hrows Hcoef].
  destruct (pivot_output_lengths m k r e D C A B [] Hm ltac:(lia)) as
    [Hdl [Hcl [Hal _]]].
  assert (forall j, 0 <= j < m ->
    Znth j DL 0 = Znth j (pivot_denominators m k r e D A) 0 /\
    Znth j CL 0 = Znth j (pivot_constants m k r e C A) 0) as Hdone.
  { intros j Hj. specialize (Hrows j Hj). cbn zeta in Hrows.
    pose proof (proj2 (Z.ltb_lt j m) ltac:(lia)) as Hlt.
    rewrite Hlt, Bool.orb_true_r in Hrows. exact Hrows. }
  split; [eapply pivot_list_ext; eauto; intros; now apply Hdone |].
  split; [eapply pivot_list_ext; eauto; intros; now apply Hdone |].
  eapply pivot_matrix_ext; eauto.
  intros i j Hi Hj. specialize (Hcoef i j Hi Hj).
  pose proof (proj2 (Z.ltb_lt i m) ltac:(lia)) as Hlt.
  rewrite Hlt, Bool.orb_true_r in Hcoef.
  rewrite pivot_coefficients_index by assumption. exact Hcoef.
Qed.

(* GMP's field-read strategy exposes [same_sign] and compact limbs. Since
   [same_sign] puts zero with the nonnegative sign, normalization provides
   the additional information needed to decide positive and zero. *)
Lemma pivot_mpz_compact_sign ptr value size :
  same_sign value size ->
  mpd_store_Z_compact UINT_MOD ptr (Z.abs value) (Z.abs size) |--
    “ (0 < size <-> 0 < value) /\ (size = 0 <-> value = 0) ”.
Proof.
  intros Hsign.
  destruct (Z.eq_dec size 0) as [Hz|Hnz].
  - subst size. change (Z.abs 0) with 0.
    prop_apply (mpd_store_Z_compact_zero UINT_MOD ptr (Z.abs value)).
    Intros. normalize. split_pures; dump_pre_spatial; lia.
  - prop_apply (mpd_store_Z_compact_pos UINT_MOD ltac:(change (0 < 4294967296); lia)
      ptr (Z.abs value) (Z.abs size) ltac:(lia)).
    Intros. unfold same_sign in Hsign.
    normalize. split_pures; dump_pre_spatial; lia.
Qed.

(* The QCP-generated resource for an uninitialized scalar MiniGMP head.
   These are precisely the three field permissions consumed by mpz_init. *)
Definition UndefStructPred__mpz_struct (p : addr) : Assertion :=
  &(p # "__mpz_struct" ->ₛ "_mp_alloc") # Int |->_ **
  &(p # "__mpz_struct" ->ₛ "_mp_size") # Int |->_ **
  &(p # "__mpz_struct" ->ₛ "_mp_d") # Ptr |->_ .


Lemma pivot_basis_distinct__pivot_result m k r e D A B R :
  0 <= r < m -> m <= k -> k < UINT_MAX ->
  selection_basis m k D A B R -> Znth e R 0 = UINT_MAX ->
  0 <= Znth r B 0 < k /\
  (forall j, 0 <= j < m -> Znth j B 0 <> e) /\
  (forall j, 0 <= j < m -> j <> r -> Znth j B 0 <> Znth r B 0).
Proof.
  intros Hr Hmk Hk [Hrow _] He.
  destruct (Hrow r Hr) as [Hb [Hrb _]].
  split; [exact Hb |]. split.
  - intros j Hj Heq. destruct (Hrow j Hj) as [_ [Hjmap _]].
    rewrite Heq, He in Hjmap. lia.
  - intros j Hj Hjr Heq. destruct (Hrow j Hj) as [_ [Hjmap _]].
    rewrite Heq, Hrb in Hjmap. congruence.
Qed.
Lemma pivot_basis_preserved__pivot_result m k r e D A B R :
  0 <= r < m -> 0 <= e < k -> m <= k -> k < UINT_MAX ->
  Zlength B = m -> Zlength R = k ->
  selection_basis m k D A B R -> Znth e R 0 = UINT_MAX ->
  pivot_coef A k r e <> 0 ->
  selection_basis m k (pivot_denominators m k r e D A)
    (pivot_coefficients m k r e D A B) (pivot_basic r e B)
    (pivot_row_map r e B R).
Proof.
  intros Hr He Hmk Hk Hbl Hrl Hbasis Henter Hh.
  destruct (pivot_basis_distinct__pivot_result m k r e D A B R
    Hr Hmk Hk Hbasis Henter) as [Hb [Hnoenter Hdistinct]].
  destruct Hbasis as [Hrow [Hcol Hz]].
  set (b := Znth r B 0).
  assert (Hbe : b <> e) by (apply Hnoenter; exact Hr).
  set (Bn := pivot_basic r e B).
  set (Rn := pivot_row_map r e B R).
  assert (HBr : Znth r Bn 0 = e).
  { unfold Bn, pivot_basic. rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (HBother : forall j, 0 <= j < m -> j <> r -> Znth j Bn 0 = Znth j B 0).
  { intros j Hj Hjr. unfold Bn, pivot_basic. rewrite Znth_replace_Znth_Diff by lia.
    reflexivity. }
  assert (HRe : Znth e Rn 0 = r).
  { unfold Rn, pivot_row_map. fold b.
    rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (HRb : Znth b Rn 0 = UINT_MAX).
  { unfold Rn, pivot_row_map. fold b.
    rewrite Znth_replace_Znth_Same by (try rewrite Zlength_replace_Znth; lia).
    reflexivity. }
  assert (HRother : forall v, 0 <= v < k -> v <> e -> v <> b ->
      Znth v Rn 0 = Znth v R 0).
  { intros v Hv Hve Hvb. unfold Rn, pivot_row_map. fold b.
    rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
  change (selection_basis m k (pivot_denominators m k r e D A)
    (pivot_coefficients m k r e D A B) Bn Rn).
  split.
  - intros j Hj.
    assert (Hpos : 0 < Znth j (pivot_denominators m k r e D A) 0).
    { rewrite pivot_denominator_index by exact Hj. cbn zeta.
      destruct (Z.eqb j r).
      - apply Z.abs_pos. lia.
      - destruct (Hrow j Hj) as [_ [_ Hd]].
        destruct (Z.eqb (pivot_coef A k j e) 0); [exact Hd |].
        destruct (pivot_row_multipliers (pivot_coef A k r e) (pivot_coef A k j e) Hh)
          as [_ [Hscale _]]. nia. }
    destruct (Z.eq_dec j r) as [-> | Hjr].
    + rewrite HBr, HRe. auto.
    + destruct (Hrow j Hj) as [HB [HM _]].
      rewrite HBother, HRother; auto.
  - split.
    + intros v Hv Hactive.
      destruct (Z.eq_dec v e) as [-> | Hve].
      * rewrite HRe, HBr. auto.
      * assert (Hvb : v <> b).
        { intro Heq; subst v. rewrite HRb in Hactive. contradiction. }
        rewrite HRother in * by assumption.
        destruct (Hcol v Hv Hactive) as [Hindex Hlookup].
        assert (Hnotr : Znth v R 0 <> r).
        { intro Heq. rewrite Heq in Hlookup. unfold b in Hvb. congruence. }
        rewrite HBother by assumption. auto.
    + intros i j Hi Hj.
      change (pivot_coef (pivot_coefficients m k r e D A B) k i (Znth j Bn 0) = 0).
      destruct (Z.eq_dec j r) as [-> | Hjr].
      * rewrite HBr, pivot_coefficients_index by assumption.
        unfold pivot_coefficient_at, pivot_row_coef.
        destruct (Z.eqb i r); rewrite ?Z.eqb_refl; try reflexivity.
        destruct (Z.eqb_spec (pivot_coef A k i e) 0); auto.
      * destruct (Hrow j Hj) as [Hbj _].
        rewrite HBother by assumption. rewrite pivot_coefficients_index by assumption.
        pose proof (Hnoenter j Hj) as Hje. pose proof (Hdistinct j Hj Hjr) as Hjb.
        pose proof (Hz i j Hi Hj) as Hzi.
        pose proof (Hz r j Hr Hj) as Hzr.
        change (pivot_coef A k i (Znth j B 0) = 0) in Hzi.
        change (pivot_coef A k r (Znth j B 0) = 0) in Hzr.
        unfold pivot_coefficient_at, pivot_row_coef.
        rewrite (proj2 (Z.eqb_neq _ _) Hje), (proj2 (Z.eqb_neq _ _) Hjb), Hzi, Hzr.
        destruct (Z.eqb i r); try ring.
        destruct (Z.eqb (pivot_coef A k i e) 0); ring.
Qed.
Lemma pivot_dot_ext__pivot_result (cols : list Z) (f g : Z -> Q) :
  (forall v, In v cols -> (f v == g v)%Q) ->
  (fold_right Qplus 0 (map f cols) == fold_right Qplus 0 (map g cols))%Q.
Proof.
  intro H. induction cols as [|v cols IH]; simpl; [reflexivity |].
  rewrite (H v (or_introl eq_refl)).
  rewrite IH; [reflexivity | intros w Hw; apply H; now right].
Qed.
Lemma pivot_dot_linear__pivot_result (cols : list Z) (f g : Z -> Q) (u w : Q) :
  (fold_right Qplus 0 (map (fun v => u * f v + w * g v)%Q cols) ==
    u * fold_right Qplus 0 (map f cols) +
    w * fold_right Qplus 0 (map g cols))%Q.
Proof.
  induction cols as [|v cols IH]; simpl; [ring |].
  rewrite IH. ring.
Qed.
Lemma pivot_dot_delta__pivot_result (cols : list Z) (p : Z) (x : Q) :
  NoDup cols ->
  (fold_right Qplus 0 (map (fun v => if v =? p then x else 0%Q) cols) ==
   if in_dec Z.eq_dec p cols then x else 0)%Q.
Proof.
  intro Huniq.
  induction Huniq as [|v cols Hnotin Huniq IH].
  - reflexivity.
  - simpl map. simpl fold_right. rewrite IH.
    destruct (Z.eqb_spec v p) as [-> | Hvp].
    + destruct (in_dec Z.eq_dec p cols); [contradiction |].
      destruct (in_dec Z.eq_dec p (p :: cols)) as [Hself | Hself];
        [ring | exfalso; apply Hself; simpl; auto].
    + destruct (in_dec Z.eq_dec p cols) as [Hin | Hout];
        destruct (in_dec Z.eq_dec p (v :: cols)) as [Hall | Hnone]; try ring.
      * exfalso. apply Hnone. now right.
      * exfalso. destruct Hall as [Heq | Hin]; contradiction.
Qed.
Lemma pivot_rational_sum__pivot_result (cols : list Z) (f left right : Z -> Q)
    (u w c d : Q) (e b : Z) :
  NoDup cols -> In e cols -> In b cols ->
  (forall v, In v cols -> (f v ==
    (u * left v + w * right v) +
    ((if v =? e then c else 0) + (if v =? b then d else 0)))%Q) ->
  (fold_right Qplus 0 (map f cols) ==
    u * fold_right Qplus 0 (map left cols) +
    w * fold_right Qplus 0 (map right cols) + (c + d))%Q.
Proof.
  intros Hdup He Hb Hf.
  transitivity (fold_right Qplus 0%Q
    (map (fun v => (1 * (u * left v + w * right v) +
      1 * (1 * (if v =? e then c else 0) + 1 * (if v =? b then d else 0)))%Q) cols)).
  { apply pivot_dot_ext__pivot_result. intros v Hv. rewrite Hf by exact Hv. ring. }
  rewrite pivot_dot_linear__pivot_result.
  rewrite (pivot_dot_linear__pivot_result cols left right u w).
  rewrite (pivot_dot_linear__pivot_result cols
    (fun v => if v =? e then c else 0%Q)
    (fun v => if v =? b then d else 0%Q) 1%Q 1%Q).
  rewrite (pivot_dot_delta__pivot_result cols e c Hdup),
    (pivot_dot_delta__pivot_result cols b d Hdup).
  destruct (in_dec Z.eq_dec e cols), (in_dec Z.eq_dec b cols);
    try contradiction; ring.
Qed.
Lemma pivot_equation_residual__pivot_result (a b c : Q) :
  (a == b + c)%Q <-> (a - b - c == 0)%Q.
Proof.
  split; intro H.
  - rewrite H. ring.
  - transitivity ((a - b - c) + (b + c))%Q; [ring | rewrite H; ring].
Qed.
Lemma pivot_preserves_equations__pivot_result m k r e D C A B R :
  0 <= r < m -> 0 <= e < k -> m <= k -> k < UINT_MAX ->
  Zlength B = m ->
  selection_basis m k D A B R -> Znth e R 0 = UINT_MAX ->
  pivot_coef A k r e <> 0 ->
  pivot_equations_equivalent m k D C A B
    (pivot_denominators m k r e D A) (pivot_constants m k r e C A)
    (pivot_coefficients m k r e D A B) (pivot_basic r e B).
Proof.
  intros Hr He Hmk Hk Hbl Hbasis Henter Hh.
  destruct (pivot_basis_distinct__pivot_result m k r e D A B R
    Hr Hmk Hk Hbasis Henter) as [Hb [Hnoenter _]].
  pose proof (proj2 (proj2 Hbasis) r r Hr Hr) as Hz.
  set (b := Znth r B 0).
  set (h := pivot_coef A k r e).
  set (s := pivot_orientation h).
  assert (Hbe : b <> e) by (apply Hnoenter; exact Hr).
  change (pivot_coef A k r b = 0) in Hz.
  assert (Habs : Z.abs h = s * h).
  { unfold s, pivot_orientation.
    destruct (Z.ltb_spec 0 h).
    - rewrite Z.abs_eq by lia. ring.
    - rewrite Z.abs_neq by lia. ring. }
  assert (Hs : s <> 0).
  { unfold s, pivot_orientation. destruct (0 <? h); lia. }
  unfold pivot_equations_equivalent. intro x.
  set (Dn := pivot_denominators m k r e D A).
  set (Cn := pivot_constants m k r e C A).
  set (An := pivot_coefficients m k r e D A B).
  set (Bn := pivot_basic r e B).
  set (cols := Zrange 0 k).
  set (dot := fun (values : list Z) i =>
    fold_right Qplus 0%Q
      (map (fun v => (inject_Z (pivot_coef values k i v) * x v)%Q) cols)).
  set (residual := fun Ds Cs As Bs i =>
    (inject_Z (Znth i Ds 0%Z) * x (Znth i Bs 0%Z) -
      inject_Z (Znth i Cs 0%Z) - dot As i)%Q).
  assert (Hsum : forall Ds Cs As Bs,
    pivot_table_equations m k Ds Cs As Bs x <->
    forall i, 0 <= i < m -> (residual Ds Cs As Bs i == 0)%Q).
  { intros Ds Cs As Bs. unfold pivot_table_equations, residual, dot, cols.
    split; intros H i Hi.
    - apply pivot_equation_residual__pivot_result. now apply H.
    - apply pivot_equation_residual__pivot_result. now apply H. }
  rewrite !Hsum.
  assert (Hcol_e : In e cols) by (unfold cols; apply In_Zrange; exact He).
  assert (Hcol_b : In b cols) by (unfold cols; apply In_Zrange; exact Hb).
  assert (Hnodup : NoDup cols) by (unfold cols; apply NoDup_Zrange).
  assert (HAn_e : pivot_coef An k r e = 0).
  { unfold An. rewrite pivot_coefficients_index by assumption.
    unfold pivot_coefficient_at, pivot_row_coef. now rewrite !Z.eqb_refl. }
  assert (HDn_r : Znth r Dn 0 = Z.abs h).
  { unfold Dn. rewrite pivot_denominator_index by exact Hr.
    cbn zeta. now rewrite Z.eqb_refl. }
  assert (HCn_r : Znth r Cn 0 = -s * Znth r C 0).
  { unfold Cn. rewrite pivot_constant_index by exact Hr. cbn zeta.
    rewrite Z.eqb_refl. reflexivity. }
  assert (HBn_r : Znth r Bn 0 = e).
  { unfold Bn, pivot_basic. rewrite Znth_replace_Znth_Same by lia. reflexivity. }
  assert (HDot_r : (dot An r == - inject_Z s * dot A r +
    inject_Z s * inject_Z h * x e + inject_Z s * inject_Z (Znth r D 0%Z) * x b)%Q).
  { transitivity ((-inject_Z s) * dot A r +
      0 * fold_right Qplus 0 (map (fun _ : Z => 0%Q) cols) +
      (inject_Z s * inject_Z h * x e +
       inject_Z s * inject_Z (Znth r D 0%Z) * x b))%Q.
    2: ring.
    unfold dot. apply (pivot_rational_sum__pivot_result cols _ _ _ _ _ _ _ e b); [exact Hnodup | exact Hcol_e | exact Hcol_b |].
    intros v Hv. apply (proj2 (In_Zrange 0 k v)) in Hv.
    unfold An. rewrite pivot_coefficients_index by assumption.
    unfold pivot_coefficient_at, pivot_row_coef. rewrite Z.eqb_refl.
    fold h b s.
    destruct (Z.eqb_spec v e) as [-> | Hve].
    - rewrite (proj2 (Z.eqb_neq e b) ltac:(congruence)).
      fold h. ring.
    - destruct (Z.eqb_spec v b) as [-> | Hvb].
      + rewrite Hz, inject_Z_mult. ring.
      + rewrite inject_Z_mult, inject_Z_opp. ring. }
  assert (Hpivot : (residual Dn Cn An Bn r ==
    - inject_Z s * residual D C A B r)%Q).
  { unfold residual. rewrite HDn_r, HCn_r, HBn_r, Habs, HDot_r.
    fold b. rewrite !inject_Z_mult, inject_Z_opp. ring. }
  assert (Hrow : forall i, 0 <= i < m -> i <> r ->
    let z := pivot_coef A k i e in
    if z =? 0 then (residual Dn Cn An Bn i == residual D C A B i)%Q
    else (residual Dn Cn An Bn i ==
      inject_Z (pivot_row_scale h z) * residual D C A B i +
      inject_Z (pivot_row_add h z) * residual Dn Cn An Bn r)%Q).
  { intros i Hi Hir. cbn zeta.
    set (z := pivot_coef A k i e).
    assert (Hirb : (i =? r) = false) by (apply Z.eqb_neq; exact Hir).
    assert (HBi : Znth i Bn 0 = Znth i B 0).
    { unfold Bn, pivot_basic. rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
    assert (HDi : Znth i Dn 0 =
      if z =? 0 then Znth i D 0 else pivot_row_scale h z * Znth i D 0).
    { unfold Dn. rewrite pivot_denominator_index by exact Hi.
      cbn zeta. rewrite Hirb. reflexivity. }
    assert (HCi : Znth i Cn 0 =
      if z =? 0 then Znth i C 0
      else pivot_row_scale h z * Znth i C 0 + pivot_row_add h z * Znth r Cn 0).
    { unfold Cn at 1. rewrite pivot_constant_index by exact Hi.
      cbn zeta. rewrite Hirb, HCn_r. reflexivity. }
    destruct (z =? 0) eqn:Hzero.
    - assert (Hdot : (dot An i == dot A i)%Q).
      { unfold dot. apply pivot_dot_ext__pivot_result. intros v Hv.
        apply (proj2 (In_Zrange 0 k v)) in Hv.
        unfold An. rewrite pivot_coefficients_index by assumption.
        unfold pivot_coefficient_at. fold z. now rewrite Hirb, Hzero. }
      unfold residual. now rewrite HBi, HDi, HCi, Hdot.
    - set (mu := pivot_row_scale h z). set (nu := pivot_row_add h z).
      destruct (pivot_row_multipliers h z Hh) as [_ [Hmu [HP HZ]]].
      assert (Hcross : mu * z = nu * Z.abs h).
      { fold mu in HP. fold nu in HZ. nia. }
      pose proof (f_equal inject_Z Hcross) as HcrossQ.
      rewrite !inject_Z_mult in HcrossQ.
      assert (Hdot : (dot An i == inject_Z mu * dot A i +
        inject_Z nu * dot An r - inject_Z mu * inject_Z z * x e)%Q).
      { transitivity (inject_Z mu * dot A i + inject_Z nu * dot An r +
          ((-inject_Z mu) * inject_Z z * x e + 0))%Q.
        2: ring.
        unfold dot. apply (pivot_rational_sum__pivot_result cols _ _ _ _ _ _ _ e b);
          [exact Hnodup | exact Hcol_e | exact Hcol_b |].
        intros v Hv. apply (proj2 (In_Zrange 0 k v)) in Hv.
        assert (Hcoef : pivot_coef An k i v = pivot_coefficient_at k r e D A B i v).
        { unfold An. now apply pivot_coefficients_index. }
        rewrite Hcoef.
        unfold pivot_coefficient_at at 1.
        fold h z mu nu. rewrite Hirb, Hzero.
        destruct (Z.eqb_spec v e) as [-> | Hve].
        - rewrite (proj2 (Z.eqb_neq e b) ltac:(congruence)), HAn_e.
          fold z. ring.
        - assert (Hpivot_coef : pivot_coef An k r v =
            pivot_row_coef e (Znth r B 0) h (Znth r D 0) v (pivot_coef A k r v)).
          { unfold An. rewrite pivot_coefficients_index by assumption.
            unfold pivot_coefficient_at. now rewrite Z.eqb_refl. }
          rewrite <- Hpivot_coef. rewrite inject_Z_plus, !inject_Z_mult.
          destruct (v =? b); ring. }
      unfold residual. rewrite HBi, HDi, HCi, Hdot, HBn_r, HDn_r.
      fold mu nu. rewrite inject_Z_plus, !inject_Z_mult, HcrossQ. ring. }
  assert (Hscalar : ~ (inject_Z s == 0)%Q).
  { intro H. apply Hs. now apply inject_Z_injective. }
  split; intros H i Hi.
  - assert (Hp0 : (residual Dn Cn An Bn r == 0)%Q).
    { rewrite Hpivot, (H r Hr). ring. }
    destruct (Z.eq_dec i r) as [-> | Hir]; [exact Hp0 |].
    pose proof (Hrow i Hi Hir) as Hcase. cbn zeta in Hcase.
    destruct (pivot_coef A k i e =? 0);
      rewrite Hcase, (H i Hi); [reflexivity | rewrite Hp0; ring].
  - assert (Hp0 : (residual D C A B r == 0)%Q).
    { apply (Qmult_integral_l (- inject_Z s)).
      - intro Hneg. apply Hscalar. rewrite <- Qopp_involutive, Hneg. reflexivity.
      - rewrite <- Hpivot. now apply H. }
    destruct (Z.eq_dec i r) as [-> | Hir]; [exact Hp0 |].
    pose proof (Hrow i Hi Hir) as Hcase. cbn zeta in Hcase.
    destruct (pivot_coef A k i e =? 0).
    + rewrite <- Hcase. now apply H.
    + destruct (pivot_row_multipliers h (pivot_coef A k i e) Hh) as [_ [Hmu _]].
      apply (Qmult_integral_l (inject_Z (pivot_row_scale h (pivot_coef A k i e)))).
      * intro Hzero.
        pose proof (proj1 (inject_Z_injective _ 0) Hzero) as Hcontra.
        lia.
      * transitivity (inject_Z (pivot_row_scale h (pivot_coef A k i e)) *
          residual D C A B i +
          inject_Z (pivot_row_add h (pivot_coef A k i e)) * residual Dn Cn An Bn r)%Q.
        -- rewrite (H r Hr). ring.
        -- rewrite <- Hcase. now apply H.
Qed.
Lemma pivot_negation_slot_length__negate_pivot_row p j count values :
  MpzArray.missing_i p j 0 count values |-- “ Zlength values = count ”.
Proof.
  unfold MpzArray.missing_i.
  replace count with (count - 0) at 2 by lia.
  apply store_array_missing_i_rec_Zlength.
Qed.
Lemma pivot_negation_step__negate_pivot_row m k r v A AN :
  Zlength AN = m * k ->
  0 <= r * k + v < m * k ->
  0 <= v ->
  pivot_negated_prefix m k r v A AN ->
  pivot_negated_prefix m k r (v + 1) A
    (replace_Znth (r * k + v) (- Znth (r * k + v) AN 0) AN).
Proof.
  intros Hlength Hslot Hv Hprefix j Hj.
  destruct (Z.eq_dec j (r * k + v)) as [-> | Hother].
  - rewrite Znth_replace_Znth_Same by lia.
    rewrite (Hprefix _ Hslot).
    rewrite Z.ltb_irrefl, Bool.andb_false_r.
    assert (Hl : (r * k <=? r * k + v) = true) by (apply Z.leb_le; lia).
    assert (Hr : (r * k + v <? r * k + (v + 1)) = true) by (apply Z.ltb_lt; lia).
    rewrite Hl, Hr.
    reflexivity.
  - rewrite Znth_replace_Znth_Diff by lia.
    rewrite (Hprefix j Hj).
    destruct (r * k <=? j); simpl.
    + destruct (j <? r * k + v) eqn:Hprevious.
      * apply Z.ltb_lt in Hprevious.
        assert (Hnext : (j <? r * k + (v + 1)) = true) by (apply Z.ltb_lt; lia).
        now rewrite Hnext.
      * apply Z.ltb_ge in Hprevious.
        assert (Hnext : (j <? r * k + (v + 1)) = false) by (apply Z.ltb_ge; lia).
        now rewrite Hnext.
    + reflexivity.
Qed.
Lemma pivot_row_ready__pivot_row_transition m k r e b D C A B AN :
  0 <= r < m -> 0 <= e < k -> 0 <= b < k -> b <> e ->
  b = Znth r B 0 ->
  Zlength D = m -> Zlength C = m -> Zlength AN = m * k ->
  (if 0 <? pivot_coef A k r e then pivot_negated_prefix m k r k A AN else AN = A) ->
  pivot_rows_done m k r e 0 D C A B
    (replace_Znth r (Z.abs (pivot_coef A k r e)) D)
    (if 0 <? pivot_coef A k r e then replace_Znth r (- Znth r C 0) C else C)
    (replace_Znth (r * k + e) 0
      (replace_Znth (r * k + b) (pivot_orientation (pivot_coef A k r e) * Znth r D 0) AN)).
Proof.
  intros Hr He Hb Hbe Hbval HD HC HAN Hprefix.
  set (h := pivot_coef A k r e) in *.
  assert (Hcell : forall j v, 0 <= j < m -> 0 <= v < k -> 0 <= j * k + v < m * k).
  { intros j v Hj Hv.
    assert (Htop : (j + 1) * k <= m * k).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    nia. }
  assert (Hdiffer : forall j v, 0 <= j < m -> 0 <= v < k -> j <> r ->
    or (j * k + v < r * k) ((r + 1) * k <= j * k + v)).
  { intros j v Hj Hv Hjr.
    destruct (Z_lt_ge_dec j r) as [Hlt | Hge].
    - left. assert (Hmul : (j + 1) * k <= r * k)
        by (apply Z.mul_le_mono_nonneg_r; lia).
      nia.
    - right. assert (Hmul : (r + 1) * k <= j * k)
        by (apply Z.mul_le_mono_nonneg_r; lia).
      nia. }
  assert (HANval : forall j v, 0 <= j < m -> 0 <= v < k ->
    pivot_coef AN k j v =
    if j =? r then -pivot_orientation h * pivot_coef A k j v else pivot_coef A k j v).
  { intros j v Hj Hv.
    destruct (0 <? h) eqn:Hs.
    - unfold pivot_orientation. rewrite Hs.
      unfold pivot_negated_prefix in Hprefix.
      unfold pivot_coef.
      rewrite Hprefix by (apply Hcell; assumption).
      destruct (j =? r) eqn:Hjr.
      + apply Z.eqb_eq in Hjr. subst j.
        assert (Hlo : (r * k <=? r * k + v) = true) by (apply Z.leb_le; lia).
        assert (Hhi : (r * k + v <? r * k + k) = true) by (apply Z.ltb_lt; lia).
        rewrite Hlo, Hhi. change (- Znth (r * k + v) A 0 = -1 * Znth (r * k + v) A 0). ring.
      + apply Z.eqb_neq in Hjr.
        destruct (Hdiffer j v Hj Hv Hjr) as [Hlo | Hhi].
        * assert (Htest : (r * k <=? j * k + v) = false) by (apply Z.leb_gt; lia).
          now rewrite Htest.
        * assert (Htest : (j * k + v <? r * k + k) = false) by (apply Z.ltb_ge; nia).
          rewrite Htest. now rewrite andb_false_r.
    - unfold pivot_orientation. rewrite Hs. subst AN.
      destruct (j =? r); [ring | reflexivity]. }
  unfold pivot_rows_done. split.
  - intros j Hj.
    assert (Hlt : (j <? 0) = false) by (apply Z.ltb_ge; lia).
    rewrite Hlt, orb_false_r.
    destruct (j =? r) eqn:Hjr.
    + apply Z.eqb_eq in Hjr. subst j. split.
      * rewrite Znth_replace_Znth_Same by lia.
        rewrite pivot_denominator_index by lia. rewrite Z.eqb_refl. reflexivity.
      * rewrite pivot_constant_index by lia. rewrite Z.eqb_refl.
        unfold pivot_row_constant, pivot_orientation. fold h.
        destruct (0 <? h).
        -- rewrite Znth_replace_Znth_Same by lia. ring.
        -- ring.
    + apply Z.eqb_neq in Hjr. split.
      * rewrite Znth_replace_Znth_Diff by lia. reflexivity.
      * destruct (0 <? h).
        -- rewrite Znth_replace_Znth_Diff by lia. reflexivity.
        -- reflexivity.
  - intros j v Hj Hv.
    assert (Hlt : (j <? 0) = false) by (apply Z.ltb_ge; lia).
    rewrite Hlt, orb_false_r.
    assert (Hrb := Hcell r b Hr Hb).
    assert (Hre := Hcell r e Hr He).
    assert (Hjv := Hcell j v Hj Hv).
    destruct (j =? r) eqn:Hjr.
    + apply Z.eqb_eq in Hjr. subst j.
      unfold pivot_coefficient_at. rewrite Z.eqb_refl.
      unfold pivot_row_coef. fold h. rewrite <- Hbval.
      unfold pivot_coef at 1.
      destruct (v =? e) eqn:Hve.
      * apply Z.eqb_eq in Hve. subst v.
        rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia).
        reflexivity.
      * apply Z.eqb_neq in Hve.
        rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
        destruct (v =? b) eqn:Hvb.
        -- apply Z.eqb_eq in Hvb. subst v.
           rewrite Znth_replace_Znth_Same by lia. reflexivity.
        -- apply Z.eqb_neq in Hvb. rewrite Znth_replace_Znth_Diff by lia.
           change (pivot_coef AN k r v = - pivot_orientation h * pivot_coef A k r v).
           rewrite HANval by assumption. now rewrite Z.eqb_refl.
    + apply Z.eqb_neq in Hjr.
      destruct (Hdiffer j v Hj Hv Hjr) as [Hlo | Hhi];
        unfold pivot_coef at 1;
        rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia || nia);
        rewrite Znth_replace_Znth_Diff by (lia || nia);
        change (pivot_coef AN k j v = pivot_coef A k j v);
        rewrite HANval by assumption;
        now rewrite (proj2 (Z.eqb_neq j r) Hjr).
Qed.
Lemma pivot_exact_original_pre__classify_and_divide q num den old p h z :
  q <> 0 -> 0 < p -> (z = p \/ z = h) ->
  store_Z q old ** store_Z num z ** store_Z den (Z.gcd p h) |--
  (“ q <> 0 ” && “ Z.gcd p h <> 0 ” &&
   “ z = Z.quot z (Z.gcd p h) * Z.gcd p h ” &&
   store_Z q old ** store_Z num z ** store_Z den (Z.gcd p h)).
Proof.
  intros Hq Hp Hz.
  destruct (pivot_gcd_exact p h Hp) as [Hg [HexactP HexactH]].
  assert (Hexact : pivot_divides_exactly z (Z.gcd p h)) by (destruct Hz as [-> | ->]; assumption).
  rewrite <- (pivot_divexact_require_equiv q num den old z (Z.gcd p h)).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.
Lemma pivot_exact_stack_calls__classify_and_divide ai entering oldm oldn p h :
  0 < p ->
  (store_Z (&("m")) oldm ** store_Z (&("p")) p ** store_Z (&("g")) (Z.gcd p h) |--
   (“ (&("m")) <> 0 ” && “ Z.gcd p h <> 0 ” &&
    “ p = Z.quot p (Z.gcd p h) * Z.gcd p h ” &&
    store_Z (&("m")) oldm ** store_Z (&("p")) p ** store_Z (&("g")) (Z.gcd p h))) /\
  (store_Z (&("n")) oldn ** store_Z (ai + entering * sizeof("__mpz_struct")) h ** store_Z (&("g")) (Z.gcd p h) |--
   (“ (&("n")) <> 0 ” && “ Z.gcd p h <> 0 ” &&
    “ h = Z.quot h (Z.gcd p h) * Z.gcd p h ” &&
    store_Z (&("n")) oldn ** store_Z (ai + entering * sizeof("__mpz_struct")) h ** store_Z (&("g")) (Z.gcd p h))).
Proof.
  intro Hp.
  split.
  - apply pivot_exact_original_pre__classify_and_divide with (p := p) (h := h);
      auto using addr_of_LE_var_not_zero.
  - apply pivot_exact_original_pre__classify_and_divide with (p := p) (h := h);
      auto using addr_of_LE_var_not_zero.
Qed.
Lemma pivot_array_rec_app__eliminate_two_cells p lo mid hi (prefix suffix : list Z) :
  Zlength prefix = mid - lo ->
  store_array_rec mpz_store p lo hi (prefix ++ suffix) --||--
  store_array_rec mpz_store p lo mid prefix **
    store_array_rec mpz_store p mid hi suffix.
Proof.
  revert lo.
  induction prefix as [|x prefix IH]; intros lo Hlength.
  - rewrite Zlength_nil in Hlength.
    assert (lo = mid) as -> by lia.
    cbn [app store_array_rec].
    split.
    + split_pure_spatial; [cancel | split_pures; dump_pre_spatial; reflexivity].
    + normalize. Intros. cancel.
  - rewrite Zlength_cons in Hlength.
    specialize (IH (lo + 1) ltac:(lia)).
    cbn [app store_array_rec].
    split.
    + sep_apply (proj1 IH). cancel.
    + sep_apply (proj2 IH). cancel.
Qed.
Lemma pivot_two_cells_rec__eliminate_two_cells p count lo hi
    (first middle last : list Z) (x y : Z) :
  Zlength first = lo ->
  Zlength middle = hi - (lo + 1) ->
  store_array_rec mpz_store p 0 count (first ++ x :: middle ++ y :: last) --||--
  mpz_store p lo x ** mpz_store p hi y **
  store_array_rec mpz_store p 0 lo first **
  store_array_rec mpz_store p (lo + 1) hi middle **
  store_array_rec mpz_store p (hi + 1) count last.
Proof.
  intros Hfirst Hmiddle.
  pose proof (pivot_array_rec_app__eliminate_two_cells p 0 lo count
    first (x :: middle ++ y :: last) ltac:(lia)) as Hfirst_split.
  pose proof (pivot_array_rec_app__eliminate_two_cells p (lo + 1) hi count
    middle (y :: last) Hmiddle) as Hmiddle_split.
  split.
  - sep_apply_l_atomic (proj1 Hfirst_split).
    cbn [store_array_rec].
    sep_apply_l_atomic (proj1 Hmiddle_split).
    cbn [store_array_rec].
    cancel; cancel.
  - sep_apply_r_atomic (proj2 Hfirst_split).
    cbn [store_array_rec].
    sep_apply_r_atomic (proj2 Hmiddle_split).
    cbn [store_array_rec].
    sepcon_assoc_change. cancel.
Qed.
Lemma pivot_open_two_ordered__eliminate_two_cells p count lo hi (values : list Z) :
  0 <= lo < hi -> hi < count -> Zlength values = count ->
  MpzArray.full p count values |--
  mpz_store p lo (Znth lo values 0) ** mpz_store p hi (Znth hi values 0) **
  store_array_rec mpz_store p 0 lo (sublist 0 lo values) **
  store_array_rec mpz_store p (lo + 1) hi (sublist (lo + 1) hi values) **
  store_array_rec mpz_store p (hi + 1) count (sublist (hi + 1) count values).
Proof.
  intros Hlo Hhi Hlength.
  unfold MpzArray.full, store_array.
  assert (Hparts :
    values = (sublist 0 lo values ++ Znth lo values 0 ::
             sublist (lo + 1) hi values ++ Znth hi values 0 ::
             sublist (hi + 1) count values)%list).
  {
    rewrite <- (sublist_self values count ltac:(lia)) at 1.
    rewrite (sublist_split 0 count lo values) by lia.
    rewrite (sublist_split lo count (lo + 1) values) by lia.
    rewrite (sublist_split (lo + 1) count hi values) by lia.
    rewrite (sublist_split hi count (hi + 1) values) by lia.
    rewrite (sublist_single 0 lo values), (sublist_single 0 hi values) by lia.
    reflexivity.
  }
  rewrite Hparts at 1.
  apply (proj1 (pivot_two_cells_rec__eliminate_two_cells p count lo hi
    (sublist 0 lo values) (sublist (lo + 1) hi values) (sublist (hi + 1) count values)
    (Znth lo values 0) (Znth hi values 0)
    ltac:(rewrite Zlength_sublist by lia; lia)
    ltac:(rewrite Zlength_sublist by lia; lia))).
Qed.
Lemma pivot_open_two__eliminate_two_cells p count a b values :
  0 <= a < count -> 0 <= b < count -> a <> b -> Zlength values = count ->
  MpzArray.full p count values |--
  mpz_store p a (Znth a values 0) ** mpz_store p b (Znth b values 0) **
  pivot_two_missing p count a b values.
Proof.
  intros Ha Hb Hdistinct Hlength.
  unfold pivot_two_missing.
  destruct (Z_lt_ge_dec a b) as [Hab | Hba].
  - rewrite Z.min_l, Z.max_r by lia.
    sep_apply_l_atomic (pivot_open_two_ordered__eliminate_two_cells p count a b values
      ltac:(lia) ltac:(lia) Hlength).
    cancel.
  - rewrite Z.min_r, Z.max_l by lia.
    sep_apply_l_atomic (pivot_open_two_ordered__eliminate_two_cells p count b a values
      ltac:(lia) ltac:(lia) Hlength).
    cancel.
Qed.


(* All indices other than the two explicit slots read their retained slice. *)
Lemma pivot_two_cells_ordered_value__eliminate_two_cells count lo hi
    (values : list Z) (x y j : Z) :
  0 <= lo < hi -> hi < count -> 0 <= j < count ->
  Zlength (sublist 0 lo values) = lo ->
  Zlength (sublist (lo + 1) hi values) = hi - (lo + 1) ->
  Znth j (sublist 0 lo values ++ x :: sublist (lo + 1) hi values ++
          y :: sublist (hi + 1) count values) 0 =
    if j =? lo then x else if j =? hi then y else Znth j values 0.
Proof.
  intros Hlo Hhi Hj Hfirst Hmiddle.
  destruct (Z_lt_ge_dec j lo) as [Hbefore | Hpast].
  - rewrite app_Znth1 by lia.
    rewrite Znth_sublist0 by lia.
    rewrite (proj2 (Z.eqb_neq j lo) ltac:(lia)),
            (proj2 (Z.eqb_neq j hi) ltac:(lia)).
    reflexivity.
  - rewrite app_Znth2 by lia.
    rewrite Hfirst.
    destruct (Z.eq_dec j lo) as [-> | Hneq].
    + rewrite Z.sub_diag, Znth0_cons, Z.eqb_refl. reflexivity.
    + rewrite (proj2 (Z.eqb_neq j lo) Hneq).
      rewrite Znth_cons by lia.
      destruct (Z_lt_ge_dec j hi) as [Hbetween | Hafter].
      * rewrite app_Znth1 by lia.
        rewrite Znth_sublist by lia.
        replace (j - lo - 1 + (lo + 1)) with j by lia.
        rewrite (proj2 (Z.eqb_neq j hi) ltac:(lia)). reflexivity.
      * rewrite app_Znth2 by lia.
        rewrite Hmiddle.
        replace (j - lo - 1 - (hi - (lo + 1))) with (j - hi) by lia.
        destruct (Z.eq_dec j hi) as [-> | Hneq'].
        -- rewrite Z.sub_diag, Znth0_cons, Z.eqb_refl. reflexivity.
        -- rewrite Znth_cons, Znth_sublist by lia.
           replace (j - hi - 1 + (hi + 1)) with j by lia.
           rewrite (proj2 (Z.eqb_neq j hi) Hneq'). reflexivity.
Qed.
Lemma pivot_two_cells_value__eliminate_two_cells count a b values x y j :
  0 <= a < count -> 0 <= b < count -> a <> b -> 0 <= j < count ->
  let lo := Z.min a b in
  let hi := Z.max a b in
  Zlength (sublist 0 lo values) = lo ->
  Zlength (sublist (lo + 1) hi values) = hi - (lo + 1) ->
  Znth j (sublist 0 lo values ++ (if a <? b then x else y) ::
          sublist (lo + 1) hi values ++ (if a <? b then y else x) ::
          sublist (hi + 1) count values) 0 =
    if j =? a then x else if j =? b then y else Znth j values 0.
Proof.
  intros Ha Hb Hneq Hj; cbn zeta.
  destruct (Z_lt_ge_dec a b) as [Hab | Hba].
  - rewrite Z.min_l, Z.max_r, (proj2 (Z.ltb_lt a b) Hab) by lia.
    eapply pivot_two_cells_ordered_value__eliminate_two_cells; lia.
  - rewrite Z.min_r, Z.max_l, (proj2 (Z.ltb_ge a b) ltac:(lia)) by lia.
    intros Hfirst Hmiddle.
    rewrite pivot_two_cells_ordered_value__eliminate_two_cells by lia.
    destruct (j =? a) eqn:Ha', (j =? b) eqn:Hb'; try reflexivity.
    apply Z.eqb_eq in Ha', Hb'. lia.
Qed.
Lemma pivot_two_cells_lengths__eliminate_two_cells p count a b values :
  pivot_two_missing p count a b values |--
  “ Zlength (sublist 0 (Z.min a b) values) = Z.min a b /\
    Zlength (sublist (Z.min a b + 1) (Z.max a b) values) = Z.max a b - (Z.min a b + 1) /\
    Zlength (sublist (Z.max a b + 1) count values) = count - (Z.max a b + 1) ”.
Proof.
  cbn zeta.
  unfold pivot_two_missing.
  prop_apply store_array_rec_Zlength. Intros.
  prop_apply (store_array_rec_Zlength _ mpz_store p (Z.min a b + 1) (Z.max a b) (sublist (Z.min a b + 1) (Z.max a b) values)).
  Intros.
  prop_apply (store_array_rec_Zlength _ mpz_store p (Z.max a b + 1) count (sublist (Z.max a b + 1) count values)).
  Intros.
  split_pures; dump_pre_spatial; intuition lia.
Qed.
Lemma pivot_merge_two_update__eliminate_two_cells p count a b values x y :
  0 <= a < count -> 0 <= b < count -> a <> b ->
  let lo := Z.min a b in
  let hi := Z.max a b in
  Zlength (sublist 0 lo values) = lo ->
  Zlength (sublist (lo + 1) hi values) = hi - (lo + 1) ->
  mpz_store p a x ** mpz_store p b y ** pivot_two_missing p count a b values |--
  MpzArray.full p count
    (sublist 0 lo values ++ (if a <? b then x else y) ::
     sublist (lo + 1) hi values ++ (if a <? b then y else x) ::
     sublist (hi + 1) count values).
Proof.
  intros Ha Hb Hneq; cbn zeta.
  unfold pivot_two_missing, MpzArray.full, store_array.
  destruct (Z_lt_ge_dec a b) as [Hab | Hba].
  - rewrite Z.min_l, Z.max_r, (proj2 (Z.ltb_lt a b) Hab) by lia.
    intros Hfirst Hmiddle.
    sep_apply_r_atomic (proj2 (pivot_two_cells_rec__eliminate_two_cells p count a b
      (sublist 0 a values) (sublist (a + 1) b values) (sublist (b + 1) count values) x y Hfirst Hmiddle)).
    sepcon_assoc_change. cancel.
  - rewrite Z.min_r, Z.max_l, (proj2 (Z.ltb_ge a b) ltac:(lia)) by lia.
    intros Hfirst Hmiddle.
    sep_apply_r_atomic (proj2 (pivot_two_cells_rec__eliminate_two_cells p count b a
      (sublist 0 b values) (sublist (b + 1) a values) (sublist (a + 1) count values) y x Hfirst Hmiddle)).
    sepcon_assoc_change. cancel.
Qed.
Lemma pivot_unvisited_values__eliminate_two_cells m k r e i v D C A B DL CL AL AN :
  0 <= r < m -> 0 <= i < m -> i <> r -> 0 <= v < k ->
  pivot_rows_done m k r e i D C A B DL CL AL ->
  pivot_combined_prefix m k r e i v D A B AL AN ->
  pivot_coef AN k i v = pivot_coef A k i v /\
  pivot_coef AN k r v = pivot_coef AL k r v.
Proof.
  intros Hr Hi Hneq Hv [_ Hrows] Hprefix.
  split.
  - unfold pivot_combined_prefix in Hprefix.
    rewrite (Hprefix i v Hi Hv), Z.ltb_irrefl, Z.eqb_refl.
    rewrite (Hrows i v Hi Hv), (proj2 (Z.eqb_neq i r) Hneq), Z.ltb_irrefl.
    reflexivity.
  - unfold pivot_combined_prefix in Hprefix.
    rewrite (Hprefix r v Hr Hv), (proj2 (Z.eqb_neq r i) ltac:(lia)).
    reflexivity.
Qed.
Lemma pivot_combined_step__eliminate_two_cells m k r e i v D A B AL AN new :
  0 <= v < k -> v <> e ->
  pivot_combined_prefix m k r e i v D A B AL AN ->
  (forall j u, 0 <= j < m -> 0 <= u < k ->
     pivot_coef new k j u =
     if andb (j =? i) (u =? v) then pivot_coefficient_at k r e D A B i v
     else pivot_coef AN k j u) ->
  pivot_combined_prefix m k r e i (v + 1) D A B AL new.
Proof.
  intros Hv Hve Hprefix Hupdate j u Hj Hu.
  rewrite (Hupdate j u Hj Hu).
  destruct (Z.eq_dec j i) as [->|Hji].
  - rewrite Z.eqb_refl; cbn [andb].
    destruct (Z.eq_dec u v) as [->|Huv].
    + rewrite Z.eqb_refl,
        (proj2 (Z.ltb_lt v (v + 1)) ltac:(lia)),
        (proj2 (Z.eqb_neq v e) Hve).
      reflexivity.
    + rewrite (proj2 (Z.eqb_neq u v) Huv).
      rewrite (Hprefix i u Hj Hu), Z.eqb_refl.
      destruct (u <? v) eqn:Hbefore.
      * apply Z.ltb_lt in Hbefore.
        rewrite (proj2 (Z.ltb_lt u (v + 1)) ltac:(lia)). reflexivity.
      * apply Z.ltb_ge in Hbefore.
        rewrite (proj2 (Z.ltb_ge u (v + 1)) ltac:(lia)). reflexivity.
  - rewrite (proj2 (Z.eqb_neq j i) Hji); cbn [andb].
    rewrite (Hprefix j u Hj Hu), (proj2 (Z.eqb_neq j i) Hji).
    reflexivity.
Qed.
Lemma pivot_two_cells_replace__eliminate_two_cells count a b (values : list Z) x :
  0 <= a < count -> 0 <= b < count -> a <> b ->
  let lo := Z.min a b in
  let hi := Z.max a b in
  Zlength (sublist 0 lo values) = lo ->
  Zlength (sublist (lo + 1) hi values) = hi - (lo + 1) ->
  Zlength (sublist (hi + 1) count values) = count - (hi + 1) ->
  let build := fun x y =>
    (sublist 0 lo values ++ (if a <? b then x else y) ::
     sublist (lo + 1) hi values ++ (if a <? b then y else x) ::
     sublist (hi + 1) count values)%list in
  let base := build (Znth a values 0) (Znth b values 0) in
  (forall j, 0 <= j < count -> Znth j base 0 = Znth j values 0) /\
  build x (Znth b values 0) = replace_Znth a x base.
Proof.
  intros Ha Hb Hneq; cbn zeta.
  intros Hfirst Hmiddle Hlast.
  set (build := fun x y : Z =>
    (sublist 0 (Z.min a b) values ++ (if a <? b then x else y) ::
     sublist (Z.min a b + 1) (Z.max a b) values ++ (if a <? b then y else x) ::
     sublist (Z.max a b + 1) count values)%list).
  set (base := build (Znth a values 0) (Znth b values 0)).
  assert (Hlength : forall x y, Zlength (build x y) = count).
  {
    intros x' y'. unfold build.
    repeat rewrite Zlength_app || rewrite Zlength_cons.
    lia.
  }
  assert (Hvalue : forall x y j, 0 <= j < count ->
    Znth j (build x y) 0 = if j =? a then x else if j =? b then y else Znth j values 0).
  {
    intros x' y' j Hj. unfold build.
    eapply pivot_two_cells_value__eliminate_two_cells; eauto.
  }
  assert (Hbase : forall j, 0 <= j < count -> Znth j base 0 = Znth j values 0).
  {
    intros j Hj. unfold base.
    rewrite Hvalue by lia.
    destruct (j =? a) eqn:Ha', (j =? b) eqn:Hb';
      try apply Z.eqb_eq in Ha'; try apply Z.eqb_eq in Hb';
      subst; reflexivity.
  }
  split; [exact Hbase|].
  apply (pivot_list_ext _ _ count).
  - apply Hlength.
  - rewrite Zlength_replace_Znth; apply Hlength.
  - intros j Hj.
    rewrite Hvalue by lia.
    destruct (Z.eq_dec j a) as [-> | Hja].
    + rewrite Z.eqb_refl, Znth_replace_Znth_Same by (unfold base; rewrite Hlength; lia).
      reflexivity.
    + rewrite (proj2 (Z.eqb_neq j a) Hja), Znth_replace_Znth_Diff
        by (unfold base; try rewrite Hlength; lia).
      rewrite Hbase by lia.
      destruct (j =? b) eqn:Hjb; [apply Z.eqb_eq in Hjb; subst |]; reflexivity.
Qed.
Lemma pivot_rows_done_constant_agreement__eliminate_two_cells
    m k r e i D C A B DL CL AL CL' :
  pivot_rows_done m k r e i D C A B DL CL AL ->
  (forall j, 0 <= j < m -> Znth j CL' 0 = Znth j CL 0) ->
  pivot_rows_done m k r e i D C A B DL CL' AL.
Proof.
  intros [Hdc Ha] Hpointwise.
  split; [|exact Ha].
  intros j Hj. rewrite (Hpointwise j Hj). apply Hdc, Hj.
Qed.
Lemma pivot_flat_same_cell__eliminate_two_cells k i j v u :
  0 < k -> 0 <= v < k -> 0 <= u < k ->
  i * k + v = j * k + u ->
  i = j /\ v = u.
Proof.
  intros Hk Hv Hu Hflat.
  assert (Horder : forall a b x y,
    a < b -> 0 <= x < k -> 0 <= y < k -> a * k + x < b * k + y).
  {
    intros a b x y Hab Hx Hy.
    assert ((a + 1) * k <= b * k) by (apply Z.mul_le_mono_nonneg_r; lia).
    nia.
  }
  assert (i = j) by
    (destruct (Z.lt_trichotomy i j) as [Hij | [Heq | Hji]];
     [pose proof (Horder i j v u Hij Hv Hu); lia | exact Heq |
      pose proof (Horder j i u v Hji Hu Hv); lia]).
  subst j; split; lia.
Qed.
Lemma pivot_active_coefficient__eliminate_two_cells k r e D A B i v :
  i <> r -> v <> e -> pivot_coef A k i e <> 0 ->
  pivot_coefficient_at k r e D A B i v =
    pivot_row_scale (pivot_coef A k r e) (pivot_coef A k i e) * pivot_coef A k i v +
    pivot_row_add (pivot_coef A k r e) (pivot_coef A k i e) *
    pivot_coefficient_at k r e D A B r v.
Proof.
  intros Hir Hve Hx.
  unfold pivot_coefficient_at.
  rewrite (proj2 (Z.eqb_neq i r) Hir),
          (proj2 (Z.eqb_neq (pivot_coef A k i e) 0) Hx),
          (proj2 (Z.eqb_neq v e) Hve),
          Z.eqb_refl.
  reflexivity.
Qed.
Lemma pivot_row_slot_bounds__finish_elimination m k i v :
  0 <= i < m -> 0 <= v < k -> 0 <= i * k + v < m * k.
Proof.
  intros Hi Hv.
  pose proof (Z.mul_nonneg_nonneg i k ltac:(lia) ltac:(lia)).
  pose proof (Z.mul_le_mono_nonneg_r (i + 1) m k ltac:(lia) ltac:(lia)).
  rewrite Z.mul_add_distr_r in H0. lia.
Qed.
Lemma pivot_row_slot_distinct__finish_elimination k i j v w :
  0 <= v < k -> 0 <= w < k -> i <> j \/ v <> w ->
  i * k + v <> j * k + w.
Proof.
  intros Hv Hw Hdiff Heq.
  assert (Hij : i = j).
  { destruct (Z.lt_trichotomy i j) as [Hlt | [He | Hgt]]; [ | exact He | ].
    - pose proof (Z.mul_le_mono_nonneg_r (i + 1) j k ltac:(lia) ltac:(lia)) as Hstride.
      rewrite Z.mul_add_distr_r in Hstride. lia.
    - pose proof (Z.mul_le_mono_nonneg_r (j + 1) i k ltac:(lia) ltac:(lia)) as Hstride.
      rewrite Z.mul_add_distr_r in Hstride. lia. }
  subst j. destruct Hdiff; lia.
Qed.
Lemma pivot_skip_entering_column__finish_elimination m k r e i D A B AL AN :
  pivot_combined_prefix m k r e i e D A B AL AN ->
  pivot_combined_prefix m k r e i (e + 1) D A B AL AN.
Proof.
  intros Hprefix j v Hj Hv. specialize (Hprefix j v Hj Hv).
  destruct (Z.eq_dec v e) as [-> | Hneq].
  - rewrite Z.eqb_refl in *. simpl in *. 
    repeat rewrite Bool.andb_false_r in *. exact Hprefix.
  - assert (Hsame : (v <? e + 1) = (v <? e)).
    { destruct (v <? e) eqn:Hlt; 
        [apply Z.ltb_lt in Hlt; apply Z.ltb_lt | apply Z.ltb_ge in Hlt; apply Z.ltb_ge]; lia. }
    now rewrite Hsame.
Qed.
Lemma pivot_skip_pivot_row__finish_elimination m k r e D C A B DL CL AL :
  pivot_rows_done m k r e r D C A B DL CL AL ->
  pivot_rows_done m k r e (r + 1) D C A B DL CL AL.
Proof.
  intros [Hvalues Hcoef].
  assert (Hsame : forall j, ((j =? r) || (j <? r + 1))%bool =
                            ((j =? r) || (j <? r))%bool).
  { intro j. destruct (j =? r) eqn:Heq; [reflexivity|].
    apply Z.eqb_neq in Heq. simpl.
    destruct (j <? r) eqn:Hlt;
        [apply Z.ltb_lt in Hlt; apply Z.ltb_lt | apply Z.ltb_ge in Hlt; apply Z.ltb_ge]; lia. }
  split.
  - intros j Hj. cbn zeta. rewrite Hsame. exact (Hvalues j Hj).
  - intros j v Hj Hv. rewrite Hsame. exact (Hcoef j v Hj Hv).
Qed.
Lemma pivot_skip_zero_row__finish_elimination m k r e i D C A B DL CL AL :
  0 <= i < m -> i <> r -> pivot_coef A k i e = 0 ->
  pivot_rows_done m k r e i D C A B DL CL AL ->
  pivot_rows_done m k r e (i + 1) D C A B DL CL AL.
Proof.
  intros Hi Hir Hz [Hvalues Hcoef].
  assert (Hsame : forall j, j <> i ->
     ((j =? r) || (j <? i + 1))%bool = ((j =? r) || (j <? i))%bool).
  { intros j Hji. assert (Hlt : (j <? i + 1) = (j <? i)).
    { destruct (j <? i) eqn:Hj;
        [apply Z.ltb_lt in Hj; apply Z.ltb_lt | apply Z.ltb_ge in Hj; apply Z.ltb_ge]; lia. }
    now rewrite Hlt. }
  apply Z.eqb_neq in Hir.
  assert (Hlt : (i <? i + 1) = true) by (apply Z.ltb_lt; lia).
  split.
  - intros j Hj. cbn zeta.
    destruct (Z.eq_dec j i) as [-> | Hneq].
    + specialize (Hvalues i Hi). cbn zeta in Hvalues.
      rewrite Hir, Z.ltb_irrefl in Hvalues. rewrite Hir, Hlt.
      rewrite pivot_denominator_index, pivot_constant_index by exact Hi.
      now rewrite Hir, Hz.
    + rewrite Hsame by exact Hneq. exact (Hvalues j Hj).
  - intros j v Hj Hv.
    destruct (Z.eq_dec j i) as [-> | Hneq].
    + specialize (Hcoef i v Hi Hv).
      rewrite Hir, Z.ltb_irrefl in Hcoef. rewrite Hir, Hlt.
      unfold pivot_coefficient_at. now rewrite Hir, Hz.
    + rewrite Hsame by exact Hneq. exact (Hcoef j v Hj Hv).
Qed.
Lemma pivot_complete_elimination_row__finish_elimination m k r e i D C A B DL CL AL AN :
  0 <= r < m -> 0 <= i < m -> 0 <= e < k ->
  i <> r -> pivot_coef A k i e <> 0 ->
  Zlength DL = m -> Zlength CL = m -> Zlength AN = m * k ->
  pivot_rows_done m k r e i D C A B DL CL AL ->
  pivot_combined_prefix m k r e i k D A B AL AN ->
  let h := pivot_coef A k r e in
  let x := pivot_coef A k i e in
  pivot_rows_done m k r e (i + 1) D C A B
    (replace_Znth i (pivot_row_scale h x * Znth i D 0) DL)
    (replace_Znth i (pivot_row_scale h x * Znth i C 0 +
                    pivot_row_add h x * Znth r CL 0) CL)
    (replace_Znth (i * k + e) 0 AN).
Proof.
  intros Hr Hi He Hir Hnz HD HC HA [Hvalues Hcoef] Hprefix.
  cbn zeta.
  assert (Hie : (i =? r) = false) by (apply Z.eqb_neq; exact Hir).
  assert (Hne : (pivot_coef A k i e =? 0) = false) by (apply Z.eqb_neq; exact Hnz).
  assert (Hlt : (i <? i + 1) = true) by (apply Z.ltb_lt; lia).
  assert (Hsame : forall j, j <> i ->
     ((j =? r) || (j <? i + 1))%bool = ((j =? r) || (j <? i))%bool).
  { intros j Hji. assert (Hlt' : (j <? i + 1) = (j <? i)).
    { destruct (j <? i) eqn:Hj;
        [apply Z.ltb_lt in Hj; apply Z.ltb_lt | apply Z.ltb_ge in Hj; apply Z.ltb_ge]; lia. }
    now rewrite Hlt'. }
  assert (Hconstant : Znth r CL 0 = pivot_row_constant (pivot_coef A k r e) (Znth r C 0)).
  { pose proof (Hvalues r Hr) as [_ Hc]. cbn zeta in Hc.
    rewrite Z.eqb_refl in Hc. simpl in Hc.
    rewrite Hc, pivot_constant_index by exact Hr. now rewrite Z.eqb_refl. }
  split.
  - intros j Hj. cbn zeta.
    destruct (Z.eq_dec j i) as [-> | Hneq].
    + repeat rewrite Znth_replace_Znth_Same by lia.
      rewrite Hie, Hlt. rewrite pivot_denominator_index, pivot_constant_index by exact Hi.
      rewrite Hie, Hne, Hconstant. split; reflexivity.
    + repeat rewrite Znth_replace_Znth_Diff by lia.
      rewrite Hsame by exact Hneq. exact (Hvalues j Hj).
  - intros j v Hj Hv.
    assert (Hidx : 0 <= i * k + e < Zlength AN).
    { rewrite HA. now apply pivot_row_slot_bounds__finish_elimination. }
    assert (Htarget : 0 <= j * k + v < Zlength AN).
    { rewrite HA. now apply pivot_row_slot_bounds__finish_elimination. }
    destruct (Z.eq_dec j i) as [-> | Hneq].
    + rewrite Hie, Hlt. simpl.
      destruct (Z.eq_dec v e) as [-> | Hve].
      * unfold pivot_coef at 1. rewrite Znth_replace_Znth_Same by exact Hidx.
        unfold pivot_coefficient_at. now rewrite Hie, Hne, Z.eqb_refl.
      * assert (Hslots : i * k + e <> i * k + v) by lia.
        unfold pivot_coef at 1. rewrite Znth_replace_Znth_Diff by assumption.
        change (pivot_coef AN k i v = pivot_coefficient_at k r e D A B i v).
        specialize (Hprefix i v Hi Hv). rewrite Z.eqb_refl in Hprefix.
        assert (Hvk : (v <? k) = true) by (apply Z.ltb_lt; lia). rewrite Hvk in Hprefix.
        assert (Hveb : (v =? e) = false) by (apply Z.eqb_neq; exact Hve).
        now rewrite Hveb in Hprefix.
    + assert (Hslots : i * k + e <> j * k + v).
      { apply pivot_row_slot_distinct__finish_elimination; [exact He | exact Hv | left; lia]. }
      rewrite Hsame by exact Hneq.
      unfold pivot_coef at 1. rewrite Znth_replace_Znth_Diff by assumption.
      change (pivot_coef AN k j v = if orb (j =? r) (j <? i) then pivot_coefficient_at k r e D A B j v else pivot_coef A k j v).
      specialize (Hprefix j v Hj Hv).
      assert (Hjib : (j =? i) = false) by (apply Z.eqb_neq; exact Hneq).
      rewrite Hjib in Hprefix. simpl in Hprefix.
      rewrite Hprefix. exact (Hcoef j v Hj Hv).
Qed.
Lemma pivot_missing_slot_length__finish_elimination p j count values :
  MpzArray.missing_i p j 0 count values |-- “ Zlength values = count ”.
Proof.
  unfold MpzArray.missing_i.
  replace count with (count - 0) at 2 by lia.
  apply store_array_missing_i_rec_Zlength.
Qed.
