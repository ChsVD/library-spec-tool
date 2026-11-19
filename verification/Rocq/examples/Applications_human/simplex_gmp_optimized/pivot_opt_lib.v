From Coq Require Import ZArith List Lia.
From Coq Require Import QArith Qring.
From AUXLib Require Import ListLib.
From ListLib.General Require Import Length.
From SumLib Require Import ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.simplex_gmp_minimal Require Import
  pivot_fme_model_lib violated_fme_model_selection_lib.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import
  build_opt_lib normalize_opt_lib.
Import ListNotations.
Local Open Scope Z_scope.

(* N is the ordered enumeration of nonbasic columns, with no repeated slots.
   The row map continues to encode nonbasic columns by UINT_MAX. *)
Definition pivot_nonbasic_columns (k : Z) (B R N : list Z) : Prop :=
  normalize_columns k B R N /\
  (forall v, 0 <= v < k -> (In v N <-> Znth v R 0 = UINT_MAX)).

(* Each row consists of denominator, constant, and coefficients in column
   order, independently of its array address and the other rows. *)
Definition pivot_row_snapshot (k i : Z) (D C A : list Z) : Z * Z * list Z :=
  (Znth i D 0, Znth i C 0, sublist (i*k) ((i+1)*k) A).

(* The primitive form divides the denominator, constant, and exactly the
   nonbasic coefficients by their common positive divisor. *)
Definition pivot_primitive_row (N : list Z)
    (d c : Z) (a : list Z) (k : Z) : Z * Z * list Z :=
  let g := fold_left Z.gcd (map (fun v => Znth v a 0) N ++ [c]) d in
  (Z.quot d g, Z.quot c g,
   map (fun v => if in_dec Z.eq_dec v N then Z.quot (Znth v a 0) g else Znth v a 0)
       (Zrange 0 k)).

(* Solve the original pivot equation for the entering column and reduce it
   under the new basis. The original equation is independent of slot order. *)
Definition pivot_normalized_row (k r e : Z) (D C A B N : list Z)
    : Z * Z * list Z :=
  let h := pivot_coef A k r e in
  let b := Znth r B 0 in
  pivot_primitive_row N (Z.abs h) (pivot_row_constant h (Znth r C 0))
    (map (fun v => pivot_row_coef e b h (Znth r D 0) v (pivot_coef A k r v))
       (Zrange 0 k)) k.

(* The other affected rows use the primitive pivot row's denominator and
   signed gcd quotients. The zero-coefficient case preserves the entry row. *)
Definition pivot_final_row (k r e i : Z) (D C A B N : list Z)
    : Z * Z * list Z :=
  let '(P, T, U) := pivot_normalized_row k r e D C A B N in
  if i =? r then (P,T,U) else
  let x := pivot_coef A k i e in
  if x =? 0 then pivot_row_snapshot k i D C A else
  let g := Z.gcd P x in
  let mu := Z.quot P g in
  let nu := Z.quot x g in
  pivot_primitive_row N (mu * Znth i D 0) (mu * Znth i C 0 + nu * T)
    (map (fun v => if v =? e then 0
                   else mu * pivot_coef A k i v + nu * Znth v U 0) (Zrange 0 k)) k.

(* Completed rows and the pivot row have their exact final values.
   Unvisited rows still represent their original equations. *)
Definition pivot_normalized_prefix (m k r e i : Z)
    (D C A B N d c a : list Z) : Prop :=
  forall j, 0 <= j < m ->
    pivot_row_snapshot k j d c a =
      if orb (j =? r) (j <? i) then pivot_final_row k r e j D C A B N
      else pivot_row_snapshot k j D C A.

(* Coefficients written while assembling the pivot row are selected by the
   visited nonbasic prefix. Every other matrix entry keeps its input value. *)
Definition pivot_negated_slots (m k r s : Z) (A N cur : list Z) : Prop :=
  forall j v, 0 <= j < m -> 0 <= v < k ->
    pivot_coef cur k j v =
      if j =? r then
        if in_dec Z.eq_dec v (sublist 0 s N) then - pivot_coef A k j v
        else pivot_coef A k j v
      else pivot_coef A k j v.

(* Before the active elimination row is normalized, only its visited
   non-entering nonbasic coefficients have the new linear combination. *)
Definition pivot_elimination_slots (m k r e i s mu nu : Z)
    (A N before cur : list Z) : Prop :=
  forall j v, 0 <= j < m -> 0 <= v < k ->
    pivot_coef cur k j v =
      if andb (j =? i) (negb (v =? e)) then
        if in_dec Z.eq_dec v (sublist 0 s N) then
          mu * pivot_coef A k j v + nu * pivot_coef before k r v
        else pivot_coef before k j v
      else pivot_coef before k j v.

(* Only the raw pivot row is modified at the first normalization call. *)
Definition pivot_raw_table (m k r e : Z) (D C A B d c a : list Z) : Prop :=
  let h := pivot_coef A k r e in
  let b := Znth r B 0 in
  d = replace_Znth r (Z.abs h) D /\
  c = replace_Znth r (pivot_row_constant h (Znth r C 0)) C /\
  (forall j v, 0 <= j < m -> 0 <= v < k ->
    pivot_coef a k j v =
      if j =? r then pivot_row_coef e b h (Znth r D 0) v (pivot_coef A k r v)
      else pivot_coef A k j v).

(* The array resources are specified by the caller. This relationship
   describes their exact values and the rational equations they represent. *)
Definition pivot_optimized_result (m k r e q : Z)
    (D C A B R N d c a b rows nb : list Z) : Prop :=
  b = pivot_basic r e B /\ rows = pivot_row_map r e B R /\
  nb = replace_Znth q (Znth r B 0) N /\
  pivot_normalized_prefix m k r e m D C A B nb d c a /\
  selection_basis m k d a b rows /\ pivot_nonbasic_columns k b rows nb /\
  (forall i, 0 <= i < m ->
    (i = r \/ pivot_coef A k i e <> 0) ->
    normalize_row_gcd k i d c a nb = 1) /\
  pivot_equations_equivalent m k D C A B d c a b.

(* Immediately before normalizing an elimination row, its entering column
   has been cleared and every other coefficient is the exact combination.
   The before-table agrees with all other rows. *)
Definition pivot_elimination_raw (m k r e i mu nu : Z)
    (D C A db cb ab d c a : list Z) : Prop :=
  d = replace_Znth i (mu * Znth i D 0) db /\
  c = replace_Znth i (mu * Znth i C 0 + nu * Znth r cb 0) cb /\
  (forall j v, 0 <= j < m -> 0 <= v < k ->
    pivot_coef a k j v =
      if j =? i then
        if v =? e then 0 else mu * pivot_coef A k j v + nu * pivot_coef ab k r v
      else pivot_coef ab k j v).

(* The C contract's ghost slot is uniquely determined by the entry metadata.
   It imposes no additional mathematical restriction on a nonbasic e. *)
Lemma pivot_nonbasic_slot k B R N e :
  pivot_nonbasic_columns k B R N ->
  0 <= e < k -> Znth e R 0 = UINT_MAX ->
  exists q, 0 <= q < Zlength N /\ Znth q N 0 = e /\
    (forall j, 0 <= j < Zlength N -> Znth j N 0 = e -> j = q).
Proof.
  intros ([Hnd _] & Hnb) He Hre.
  pose proof (proj2 (Hnb e He) Hre) as Hin.
  destruct (In_nth N e 0 Hin) as [q [Hq Hnth]].
  exists (Z.of_nat q).
  split; [rewrite Zlength_correct; lia|].
  split.
  - change (nth (Z.to_nat (Z.of_nat q)) N 0 = e).
    now rewrite Nat2Z.id.
  - intros j Hj Hjval.
    unfold Znth in Hjval.
    rewrite Zlength_correct in Hj.
    assert (Z.to_nat j = q)%nat as Heq.
    { eapply (proj1 (NoDup_nth N 0) Hnd); lia. }
    lia.
Qed.

(* Converting a row slice back to a flattened cell preserves the indexing. *)
Lemma pivot_row_slice_coef k i v A :
  0 <= i -> 0 <= v < k ->
  Znth v (sublist (i*k) ((i+1)*k) A) 0 = pivot_coef A k i v.
Proof.
  intros Hi Hv. unfold pivot_coef.
  rewrite Znth_sublist by nia. f_equal. lia.
Qed.


(* The staged normalize call returns precisely the primitive form of its
   selected row. Its postcondition supplies the flattened coefficient list. *)
Lemma pivot_normalize_row_snapshot m k i D C A N dn cn an :
  0 <= i < m -> 0 < k ->
  Zlength D = m -> Zlength C = m ->
  (forall v, In v N -> 0 <= v < k) ->
  normalize_result m k i D C A N dn cn an ->
  pivot_row_snapshot k i dn cn an =
  pivot_primitive_row N (Znth i D 0) (Znth i C 0)
    (sublist (i*k) ((i+1)*k) A) k.
Proof.
  intros Hi Hk HD HC Hdom Hres.
  assert (Hdiv :
    fold_left Z.gcd
      (map (fun v => Znth v (sublist (i*k) ((i+1)*k) A) 0) N ++ [Znth i C 0])
      (Znth i D 0) = normalize_row_gcd k i D C A N).
  { unfold normalize_row_gcd, normalize_row_values.
    f_equal. f_equal. apply map_ext_in. intros v Hv.
    rewrite pivot_row_slice_coef by (pose proof (Hdom v Hv); lia).
    reflexivity. }
  unfold pivot_row_snapshot, pivot_primitive_row. rewrite Hdiv.
  unfold normalize_result in Hres. cbn zeta in Hres.
  destruct Hres as [-> [-> (Hlength & Hdone & Hrest)]].
  rewrite !Znth_replace_Znth_Same by lia.
  f_equal.
  apply (pivot_list_ext _ _ k).
  - rewrite Zlength_sublist by nia. nia.
  - rewrite Zlength_map, pivot_range_length by lia. reflexivity.
  - intros v Hv. rewrite pivot_map_range_at by lia.
    repeat rewrite pivot_row_slice_coef by lia.
    rewrite sublist_self in Hdone, Hrest by reflexivity.
    assert (Hidx : 0 <= i*k+v < m*k) by
      (apply pivot_row_slot_bounds__finish_elimination; assumption).
    unfold pivot_coef.
    destruct (in_dec Z.eq_dec v N) as [Hin|Hout].
    + apply Hdone; [exact Hidx|now exists v].
    + apply Hrest; [exact Hidx|].
      intros q Hq Heq. apply Hout. now replace v with q by lia.
Qed.


Lemma pivot_normalized_prefix_initial__first_normalization m k i e D C A B N dr cr ar dn cn an :
  0 <= i < m ->
  0 <= e < k ->
  Zlength D = m -> Zlength C = m ->
  Zlength dr = m -> Zlength cr = m ->
  Zlength A = m*k -> Zlength ar = m*k ->
  (forall v, In v N -> 0 <= v < k) ->
  pivot_raw_table m k i e D C A B dr cr ar ->
  normalize_result m k i dr cr ar N dn cn an ->
  0 < Znth i dr 0 ->
  pivot_normalized_prefix m k i e 0 D C A B N dn cn an /\
  0 < Znth i dn 0.
Proof.
  intros Hi He HD HC Hdr Hcr HA Har Hcols Hraw Hnormalize Hpositive.
  assert (Hk : 0 < k) by lia.
  pose proof (pivot_normalize_row_snapshot m k i dr cr ar N dn cn an
    Hi Hk Hdr Hcr Hcols Hnormalize) as Hsnapshot.
  destruct Hraw as (Hraw_d & Hraw_c & Hraw_a).
  destruct Hnormalize as (Hnorm_d & Hnorm_c & Han & _ & Hframe).
  split.
  - intros j Hj.
    rewrite (proj2 (Z.ltb_ge j 0)) by lia.
    destruct (Z.eq_dec j i) as [-> | Hji].
    + rewrite Z.eqb_refl. cbn [orb].
      unfold pivot_final_row, pivot_normalized_row.
      rewrite Z.eqb_refl, Hsnapshot.
      assert (Hrow :
        sublist (i*k) ((i+1)*k) ar =
        map (fun v => pivot_row_coef e (Znth i B 0) (pivot_coef A k i e)
          (Znth i D 0) v (pivot_coef A k i v)) (Zrange 0 k)).
      { apply (pivot_list_ext _ _ k).
        - rewrite Zlength_sublist by nia. nia.
        - rewrite Zlength_map, pivot_range_length by lia. reflexivity.
        - intros v Hv. rewrite pivot_row_slice_coef, pivot_map_range_at by lia.
          rewrite (Hraw_a i v Hi Hv), Z.eqb_refl. reflexivity. }
      rewrite Hrow, Hraw_d, Hraw_c, !Znth_replace_Znth_Same by lia.
      reflexivity.
    + rewrite (proj2 (Z.eqb_neq j i) Hji). cbn [orb].
      unfold pivot_row_snapshot.
      rewrite Hnorm_d, Hnorm_c, Hraw_d, Hraw_c.
      rewrite !Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
      f_equal.
      apply (pivot_list_ext _ _ k).
      * rewrite Zlength_sublist by nia. nia.
      * rewrite Zlength_sublist by nia. nia.
      * intros v Hv. rewrite !pivot_row_slice_coef by lia.
        pose proof (Hraw_a j v Hj Hv) as Hraw_slot.
        rewrite (proj2 (Z.eqb_neq j i) Hji) in Hraw_slot.
        unfold pivot_coef in Hraw_slot |- *.
        rewrite <- Hraw_slot.
        apply Hframe.
        -- apply pivot_row_slot_bounds__finish_elimination; assumption.
        -- intros w Hw.
           rewrite sublist_self in Hw by reflexivity.
           apply pivot_row_slot_distinct__finish_elimination; [exact Hv | now apply Hcols | now left].
  - rewrite Hnorm_d, Znth_replace_Znth_Same by lia.
    destruct (normalize_row_gcd_exact k i dr cr ar N Hpositive) as (Hg & Hexact & _).
    unfold pivot_divides_exactly in Hexact.
    nia.
Qed.
Lemma pivot_normalized_row_old_basic_zero__elimination_normalization m k r e D A B R C N v q :
  0 <= r < m -> 0 <= q < m -> 0 <= v < k ->
  selection_basis m k D A B R ->
  v = Znth q B 0 -> v <> Znth r B 0 ->
  let '(_, _, coeffs) := pivot_normalized_row k r e D C A B N in
  Znth v coeffs 0 = 0.
Proof.
  intros Hr Hq Hv [_ [_ Hbzero]] Hqv Hvb.
  unfold pivot_normalized_row, pivot_primitive_row.
  cbn zeta.
  rewrite pivot_map_range_at by exact Hv.
  assert (Hz : pivot_coef A k r v = 0).
  { unfold pivot_coef. now rewrite Hqv, Hbzero by assumption. }
  assert (Hraw : pivot_row_coef e (Znth r B 0)
      (pivot_coef A k r e) (Znth r D 0) v (pivot_coef A k r v) = 0).
  { unfold pivot_row_coef. rewrite Hz.
    destruct (v =? e); [reflexivity|].
    assert ((v =? Znth r B 0) = false) by (apply Z.eqb_neq; exact Hvb).
    rewrite H, Z.mul_0_r. reflexivity. }
  destruct (in_dec Z.eq_dec v N); rewrite pivot_map_range_at, Hraw by exact Hv.
  - match goal with |- context [Z.quot 0 ?g] => destruct g; reflexivity end.
  - reflexivity.
Qed.
Lemma pivot_elimination_slot_done__elimination_normalization m k r e i q mu nu D C A B R N
    db cb ab ac :
  0 <= r < m -> 0 <= i < m -> 0 <= e < k ->
  i <> r -> m <= k -> k < UINT_MAX ->
  0 <= q < Zlength N ->
  Zlength N = k-m -> Zlength B = m -> Zlength R = k ->
  Zlength ac = m*k ->
  selection_basis m k D A B R ->
  Znth e R 0 = UINT_MAX ->
  let b := Znth r B 0 in
  let bn := pivot_basic r e B in
  let rn := pivot_row_map r e B R in
  let nn := replace_Znth q b N in
  pivot_nonbasic_columns k bn rn nn ->
  pivot_normalized_prefix m k r e i D C A B nn db cb ab ->
  pivot_elimination_slots m k r e i (k-m) mu nu A nn ab ac ->
  let di := replace_Znth i (mu * Znth i D 0) db in
  let ci := replace_Znth i (mu * Znth i C 0 + nu * Znth r cb 0) cb in
  let ai := replace_Znth (i*k+e) 0 ac in
  pivot_elimination_raw m k r e i mu nu D C A db cb ab di ci ai /\
  normalize_basic_zero k i ai bn.
Proof.
  intros Hr Hi He Hir Hmk Hmax Hq Hn HB HR Hac Hbasis Hentry.
  cbv zeta.
  set (b := Znth r B 0).
  set (bn := pivot_basic r e B).
  set (rn := pivot_row_map r e B R).
  set (nn := replace_Znth q b N).
  intros [Hdomains Hnb] Hprefix Hslots.
  set (ai := replace_Znth (i*k+e) 0 ac).
  destruct (pivot_basis_distinct__pivot_result m k r e D A B R
    Hr Hmk Hmax Hbasis Hentry) as [Hb [HneverE HneverB]].
  fold b in Hb, HneverB.
  destruct Hbasis as [Hrow [Hcol Hbasic]].
  assert (Hother_map : forall v, 0 <= v < k -> v <> e -> v <> b ->
    Znth v rn 0 = Znth v R 0).
  { intros v Hv Hve Hvb. unfold rn, pivot_row_map. fold b.
    rewrite !Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
    reflexivity. }
  assert (Hb_in : In b nn).
  { assert (Hq_in : 0 <= q < Zlength nn)
      by (unfold nn; rewrite Zlength_replace_Znth; exact Hq).
    pose proof (Znth_In_Zlength nn 0 q Hq_in) as Hnth.
    unfold nn in Hnth. now rewrite Znth_replace_Znth_Same in Hnth by exact Hq. }
  assert (Hslots_full : Zlength nn = k-m).
  { unfold nn. now rewrite Zlength_replace_Znth. }
  unfold pivot_elimination_slots in Hslots.
  rewrite <- Hslots_full, sublist_self in Hslots by reflexivity.
  assert (Hpivot_zero : forall v j, 0 <= v < k -> 0 <= j < m ->
      v = Znth j B 0 -> v <> b -> pivot_coef ab k r v = 0).
  { intros v j Hv Hj Hjv Hvb.
    pose proof (Hprefix r Hr) as Hrp.
    unfold pivot_row_snapshot, pivot_final_row in Hrp.
    rewrite Z.eqb_refl in Hrp. cbn [orb] in Hrp.
    pose proof
      (pivot_normalized_row_old_basic_zero__elimination_normalization m k r e D A B R C nn v j
         Hr Hj Hv (conj Hrow (conj Hcol Hbasic)) Hjv Hvb) as Hzero.
    destruct (pivot_normalized_row k r e D C A B nn) as [[pd pc] pa].
    try rewrite Z.eqb_refl in Hrp.
    assert (Hslice : sublist (r*k) ((r+1)*k) ab = pa) by congruence.
    rewrite <- pivot_row_slice_coef by lia. now rewrite Hslice. }
  assert (Hcoefs : forall j v, 0 <= j < m -> 0 <= v < k ->
    pivot_coef ai k j v =
    if j =? i then if v =? e then 0
       else mu * pivot_coef A k j v + nu * pivot_coef ab k r v
    else pivot_coef ab k j v).
  { intros j v Hj Hv.
    pose proof (pivot_row_slot_bounds__finish_elimination m k j v Hj Hv) as Hidx.
    pose proof (pivot_row_slot_bounds__finish_elimination m k i e Hi He) as Hei.
    destruct (Z.eq_dec j i) as [->|Hji].
    - rewrite Z.eqb_refl.
      destruct (Z.eq_dec v e) as [->|Hve].
      + rewrite Z.eqb_refl. unfold pivot_coef, ai.
        now rewrite Znth_replace_Znth_Same by lia.
      + assert (Hveb : (v =? e) = false) by (apply Z.eqb_neq; exact Hve).
        rewrite Hveb.
        assert (Hunchanged : pivot_coef ai k i v = pivot_coef ac k i v).
        { unfold ai, pivot_coef. apply Znth_replace_Znth_Diff; lia. }
        rewrite Hunchanged, (Hslots i v Hi Hv), Z.eqb_refl, Hveb.
        cbn.
        destruct (in_dec Z.eq_dec v nn) as [Hvin|Hvout]; [reflexivity|].
        assert (Hvb : v <> b) by (intros ->; contradiction).
        assert (Hactive : Znth v R 0 <> UINT_MAX).
        { rewrite <- Hother_map by assumption.
          intro Hsent. apply Hvout. now apply (proj2 (Hnb v Hv)). }
        destruct (Hcol v Hv Hactive) as [Hmap_index Hvj].
        assert (Hentry_zero : pivot_coef A k i v = 0).
        { unfold pivot_coef. rewrite <- Hvj. apply Hbasic; assumption. }
        assert (Hbefore_zero : pivot_coef ab k i v = 0).
        { pose proof (Hprefix i Hi) as Hri.
          assert (Hirb : (i =? r) = false) by (apply Z.eqb_neq; exact Hir).
          rewrite Hirb, Z.ltb_irrefl in Hri. cbn in Hri.
          unfold pivot_row_snapshot in Hri.
          assert (Hslice : sublist (i*k) ((i+1)*k) ab = sublist (i*k) ((i+1)*k) A)
            by congruence.
          rewrite <- pivot_row_slice_coef by lia.
          rewrite Hslice, pivot_row_slice_coef by lia. exact Hentry_zero. }
        rewrite Hentry_zero, Hbefore_zero,
          (Hpivot_zero v (Znth v R 0) Hv Hmap_index (eq_sym Hvj) Hvb).
        ring.
    - assert (Hjib : (j =? i) = false) by (apply Z.eqb_neq; exact Hji).
      rewrite Hjib.
      assert (Hunchanged : pivot_coef ai k j v = pivot_coef ac k j v).
      { unfold ai, pivot_coef. apply Znth_replace_Znth_Diff; try lia.
        apply pivot_row_slot_distinct__finish_elimination; auto. }
      now rewrite Hunchanged, (Hslots j v Hj Hv), Hjib. }
  split; [exact (conj eq_refl (conj eq_refl Hcoefs))|].
  unfold normalize_basic_zero. apply Forall_forall.
  intros v Hv.
  destruct (In_nth bn v 0 Hv) as [t [Ht Hnth]].
  set (j := Z.of_nat t).
  assert (Hjlen : Zlength bn = m).
  { unfold bn, pivot_basic. now rewrite Zlength_replace_Znth. }
  assert (Hj : 0 <= j < m).
  { rewrite Zlength_correct in Hjlen. unfold j. lia. }
  assert (Hval : Znth j bn 0 = v).
  { unfold j, Znth. now rewrite Nat2Z.id. }
  destruct (Z.eq_dec j r) as [Hjr|Hjr].
  - rewrite Hjr in Hval.
    assert (Hev : v = e).
    { unfold bn, pivot_basic in Hval. rewrite Znth_replace_Znth_Same in Hval by lia.
      now symmetry. }
    rewrite Hev. change (pivot_coef ai k i e = 0).
    now rewrite (Hcoefs i e Hi He), !Z.eqb_refl.
  - assert (Hvj : v = Znth j B 0).
    { unfold bn, pivot_basic in Hval. rewrite Znth_replace_Znth_Diff in Hval by lia.
      now symmetry. }
    destruct (Hrow j Hj) as [Hvdom _].
    rewrite <- Hvj in Hvdom.
    assert (Hve : (v =? e) = false).
    { apply Z.eqb_neq. now rewrite Hvj; apply HneverE. }
    assert (Hvb : v <> b) by (rewrite Hvj; now apply HneverB).
    change (pivot_coef ai k i v = 0).
    rewrite (Hcoefs i v Hi Hvdom), Z.eqb_refl, Hve, (Hpivot_zero v j Hvdom Hj Hvj Hvb).
    unfold pivot_coef. rewrite Hvj, Hbasic by assumption. ring.
Qed.
Lemma pivot_elimination_prefix_after_normalize__elimination_normalization
    m k r e i mu nu D C A B N db cb ab di ci ai dn cn an :
  0 <= r < m -> 0 <= i < m -> 0 < k -> i <> r ->
  (forall v, In v N -> 0 <= v < k) ->
  Zlength A = m*k -> Zlength ab = m*k -> Zlength ai = m*k ->
  Zlength dn = m -> Zlength cn = m ->
  0 < Znth r db 0 ->
  pivot_coef A k i e <> 0 ->
  mu = Z.quot (Znth r db 0) (Z.gcd (Znth r db 0) (pivot_coef A k i e)) ->
  nu = Z.quot (pivot_coef A k i e) (Z.gcd (Znth r db 0) (pivot_coef A k i e)) ->
  pivot_normalized_prefix m k r e i D C A B N db cb ab ->
  pivot_elimination_raw m k r e i mu nu D C A db cb ab di ci ai ->
  normalize_result m k i di ci ai N dn cn an ->
  pivot_normalized_prefix m k r e (i+1) D C A B N dn cn an /\
  Znth r dn 0 = Znth r db 0.
Proof.
  intros Hr Hi Hk Hir Hdom HA Hab Hai Hdn Hcn Hpositive Henter Hmu Hnu
    Hprefix Hraw Hnormalize.
  destruct Hraw as (HrawD & HrawC & HrawA).
  pose proof Hnormalize as Hnormalized.
  destruct Hnormalized as (HnormD & HnormC & Han & _ & HnormFrame).
  assert (Hdi : Zlength di = m).
  { rewrite HnormD, Zlength_replace_Znth in Hdn. exact Hdn. }
  assert (Hci : Zlength ci = m).
  { rewrite HnormC, Zlength_replace_Znth in Hcn. exact Hcn. }
  assert (Hdb : Zlength db = m).
  { rewrite HrawD, Zlength_replace_Znth in Hdi. exact Hdi. }
  assert (Hcb : Zlength cb = m).
  { rewrite HrawC, Zlength_replace_Znth in Hci. exact Hci. }
  assert (HframeD : forall j, 0 <= j < m -> j <> i -> Znth j dn 0 = Znth j db 0).
  { intros j Hj Hji. rewrite HnormD, Znth_replace_Znth_Diff by lia.
    rewrite HrawD, Znth_replace_Znth_Diff by lia. reflexivity. }
  assert (HframeC : forall j, 0 <= j < m -> j <> i -> Znth j cn 0 = Znth j cb 0).
  { intros j Hj Hji. rewrite HnormC, Znth_replace_Znth_Diff by lia.
    rewrite HrawC, Znth_replace_Znth_Diff by lia. reflexivity. }
  split; [|apply HframeD; lia].
  intros j Hj.
  destruct (Z.eq_dec j i) as [->|Hji].
  - assert (Hvisit : (i <? i+1) = true) by (apply Z.ltb_lt; lia).
    rewrite Hvisit, Bool.orb_true_r.
    rewrite (pivot_normalize_row_snapshot m k i di ci ai N dn cn an
      Hi Hk Hdi Hci Hdom Hnormalize).
    pose proof (Hprefix r Hr) as Hpivot.
    unfold pivot_final_row in Hpivot |- *.
    rewrite Z.eqb_refl in Hpivot. cbn [orb] in Hpivot.
    destruct (pivot_normalized_row k r e D C A B N) as [[P T] U].
    try rewrite Z.eqb_refl in Hpivot.
    unfold pivot_row_snapshot in Hpivot.
    assert (HpD : Znth r db 0 = P) by congruence.
    assert (HpC : Znth r cb 0 = T) by congruence.
    assert (HpA : sublist (r*k) ((r+1)*k) ab = U) by congruence.
    assert (Hirb : (i =? r) = false) by (apply Z.eqb_neq; exact Hir).
    assert (Hx : (pivot_coef A k i e =? 0) = false) by (apply Z.eqb_neq; exact Henter).
    rewrite Hirb, Hx, <- HpD, <- HpC, <- Hmu, <- Hnu.
    rewrite HrawD, HrawC, !Znth_replace_Znth_Same by lia.
    f_equal.
    apply (pivot_list_ext _ _ k).
    + rewrite Zlength_sublist by nia. nia.
    + rewrite Zlength_map, pivot_range_length by lia. reflexivity.
    + intros v Hv.
      rewrite pivot_row_slice_coef, pivot_map_range_at by lia.
      rewrite (HrawA i v Hi Hv), Z.eqb_refl.
      rewrite <- HpA, pivot_row_slice_coef by lia.
      reflexivity.
  - assert (HframeA : sublist (j*k) ((j+1)*k) an =
        sublist (j*k) ((j+1)*k) ab).
    { apply (pivot_list_ext _ _ k).
      - rewrite Zlength_sublist by nia. nia.
      - rewrite Zlength_sublist by nia. nia.
      - intros v Hv. rewrite !pivot_row_slice_coef by lia.
        unfold pivot_coef.
        rewrite HnormFrame.
        + change (pivot_coef ai k j v = pivot_coef ab k j v).
          rewrite (HrawA j v Hj Hv).
          apply Z.eqb_neq in Hji. now rewrite Hji.
        + exact (pivot_row_slot_bounds__finish_elimination m k j v Hj Hv).
        + intros w Hw.
          rewrite sublist_self in Hw by reflexivity.
          apply pivot_row_slot_distinct__finish_elimination; [exact Hv|now apply Hdom|now left]. }
    assert (Hframe : pivot_row_snapshot k j dn cn an = pivot_row_snapshot k j db cb ab).
    { unfold pivot_row_snapshot.
      rewrite HframeD, HframeC, HframeA by assumption. reflexivity. }
    rewrite Hframe, (Hprefix j Hj).
    assert (Hvisit : (j <? i) = (j <? i+1)).
    { destruct (j <? i) eqn:Htest; symmetry.
      - apply Z.ltb_lt in Htest. apply Z.ltb_lt. lia.
      - apply Z.ltb_ge in Htest. apply Z.ltb_ge. lia. }
    now rewrite Hvisit.
Qed.
Lemma pivot_unvisited_nonbasic__pivot_negation (N : list Z) s :
  NoDup N -> 0 <= s < Zlength N ->
  ~ In (Znth s N 0) (sublist 0 s N) /\
  (forall v, In v (sublist 0 (s+1) N) <->
    In v (sublist 0 s N) \/ v = Znth s N 0).
Proof.
  intros Hdistinct Hslot. split.
  - rewrite <- (sublist_self N (Zlength N)) in Hdistinct by reflexivity.
    rewrite (sublist_split 0 (Zlength N) s N) in Hdistinct by lia.
    rewrite (sublist_split s (Zlength N) (s+1) N) in Hdistinct by lia.
    rewrite (sublist_single 0 s N) in Hdistinct by lia.
    apply NoDup_remove_2 in Hdistinct.
    intro Hin. apply Hdistinct, in_or_app. now left.
  - intros v.
    rewrite (sublist_split 0 (s+1) s N), (sublist_single 0 s N) by lia.
    rewrite in_app_iff. simpl. intuition congruence.
Qed.

(* Distinct valid columns in the same row, or entries in distinct rows,
   have different flattened indices. *)
Lemma pivot_flat_index_injective__pivot_negation k i v j w :
  0 <= v < k -> 0 <= w < k ->
  i*k+v = j*k+w -> i = j /\ v = w.
Proof.
  intros Hv Hw Hflat.
  assert (Hrow : i = j).
  { destruct (Z.lt_trichotomy i j) as [Hij | [Heq | Hji]].
    - pose proof (Z.mul_le_mono_nonneg_r (i+1) j k ltac:(lia) ltac:(lia)).
      nia.
    - exact Heq.
    - pose proof (Z.mul_le_mono_nonneg_r (j+1) i k ltac:(lia) ltac:(lia)).
      nia. }
  subst j. split; lia.
Qed.
Lemma pivot_negated_slots_step__pivot_negation m k i s A N cur :
  let v := Znth s N 0 in
  NoDup N -> 0 <= s < Zlength N ->
  0 <= i < m -> 0 <= v < k -> Zlength cur = m*k ->
  pivot_negated_slots m k i s A N cur ->
  pivot_negated_slots m k i (s+1) A N
    (replace_Znth (i*k+v) (-Znth (i*k+v) A 0) cur).
Proof.
  cbn zeta. intros Hdistinct Hslot Hi Hv Hlength Hcur.
  destruct (pivot_unvisited_nonbasic__pivot_negation N s Hdistinct Hslot)
    as [_ Hprefix].
  set (v := Znth s N 0) in *.
  intros j w Hj Hw. unfold pivot_coef.
  assert (Hindex : 0 <= i*k+v < Zlength cur) by nia.
  assert (Hother : 0 <= j*k+w < Zlength cur) by nia.
  destruct (Z.eq_dec (i*k+v) (j*k+w)) as [Heq | Hdiff].
  - destruct (pivot_flat_index_injective__pivot_negation k i v j w Hv Hw Heq)
      as [-> ->].
    rewrite Z.eqb_refl, ListLib.Base.Positional.Znth_replace_Znth_Same by lia.
    destruct (in_dec Z.eq_dec w (sublist 0 (s+1) N)) as [_ | Habsent].
    + reflexivity.
    + exfalso. apply Habsent, Hprefix. now right.
  - rewrite ListLib.Base.Positional.Znth_replace_Znth_Diff by assumption.
    specialize (Hcur j w Hj Hw). unfold pivot_coef in Hcur.
    destruct (j =? i) eqn:Hrows.
    + apply Z.eqb_eq in Hrows. subst j.
      destruct (in_dec Z.eq_dec w (sublist 0 s N)) as [Hold | Hold];
        destruct (in_dec Z.eq_dec w (sublist 0 (s+1) N)) as [Hnew | Hnew];
        try exact Hcur.
      * exfalso. apply Hnew, Hprefix. now left.
      * apply Hprefix in Hnew. destruct Hnew as [Hcontra | ->]; contradiction.
    + exact Hcur.
Qed.
Lemma pivot_raw_positive__raw_pivot_row m k i e b D C A B R N Ac :
  0 <= i < m -> 0 <= e < k -> 0 <= b < k ->
  b = Znth i B 0 -> b <> e -> 0 < pivot_coef A k i e ->
  Zlength Ac = m*k -> Zlength N = k-m ->
  selection_basis m k D A B R ->
  pivot_nonbasic_columns k B R N ->
  pivot_negated_slots m k i (k-m) A N Ac ->
  pivot_raw_table m k i e D C A B
    (replace_Znth i (Z.abs (pivot_coef A k i e)) D)
    (replace_Znth i (- Znth i C 0) C)
    (replace_Znth (i*k+e) 0 (replace_Znth (i*k+b) (Znth i D 0) Ac)).
Proof.
  intros Hi He Hb Hbasic Hbe Hpositive HAc HN Hbasis Hnonbasic Hneg.
  assert (Hsign : (0 <? pivot_coef A k i e) = true) by (apply Z.ltb_lt; lia).
  assert (Henter : 0 <= i*k+e < m*k) by
    (apply pivot_row_slot_bounds__finish_elimination; assumption).
  assert (Hleave : 0 <= i*k+b < m*k) by
    (apply pivot_row_slot_bounds__finish_elimination; assumption).
  unfold pivot_raw_table, pivot_row_constant, pivot_row_coef, pivot_orientation.
  cbn zeta. rewrite Hsign, <- Hbasic.
  split; [reflexivity|].
  split; [f_equal; ring|].
  intros j v Hj Hv.
  assert (Hindex : 0 <= j*k+v < m*k) by
    (apply pivot_row_slot_bounds__finish_elimination; assumption).
  specialize (Hneg j v Hj Hv).
  rewrite <- HN, sublist_self in Hneg by reflexivity.
  unfold pivot_coef in Hneg |- *.
  destruct (Z.eq_dec j i) as [->|Hji].
  - rewrite Z.eqb_refl in Hneg |- *.
    destruct (Z.eq_dec v e) as [->|Hve].
    + rewrite Z.eqb_refl, Znth_replace_Znth_Same by
        (rewrite Zlength_replace_Znth; lia).
      reflexivity.
    + rewrite (proj2 (Z.eqb_neq v e) Hve).
      rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec v b) as [->|Hvb].
      * rewrite Z.eqb_refl, Znth_replace_Znth_Same by lia.
        ring.
      * rewrite (proj2 (Z.eqb_neq v b) Hvb), Znth_replace_Znth_Diff by lia.
        destruct (in_dec Z.eq_dec v N) as [Hin|Hout].
        -- rewrite Hneg. ring.
        -- destruct Hnonbasic as [_ Hrow].
           destruct Hbasis as (_ & Hreverse & Hzero).
           assert (Hmapped : Znth v R 0 <> UINT_MAX).
           { intro Hmax. apply Hout. apply (proj2 (Hrow v Hv)); exact Hmax. }
           destruct (Hreverse v Hv Hmapped) as [Hrowindex Hcol].
           specialize (Hzero i (Znth v R 0) Hi Hrowindex).
           rewrite Hcol in Hzero.
           rewrite Hneg, Hzero. reflexivity.
  - rewrite (proj2 (Z.eqb_neq j i) Hji) in Hneg |- *.
    assert (Hdifferent_e : i*k+e <> j*k+v) by
      (apply pivot_row_slot_distinct__finish_elimination; try assumption; left; lia).
    assert (Hdifferent_b : i*k+b <> j*k+v) by
      (apply pivot_row_slot_distinct__finish_elimination; try assumption; left; lia).
    rewrite !Znth_replace_Znth_Diff by
      (try rewrite Zlength_replace_Znth; lia).
    exact Hneg.
Qed.
Lemma pivot_raw_negative__raw_pivot_row m k i e b D C A B :
  0 <= i < m -> 0 <= e < k -> 0 <= b < k ->
  b = Znth i B 0 -> b <> e -> pivot_coef A k i e < 0 ->
  Zlength A = m*k ->
  pivot_raw_table m k i e D C A B
    (replace_Znth i (Z.abs (pivot_coef A k i e)) D) C
    (replace_Znth (i*k+e) 0 (replace_Znth (i*k+b) (- Znth i D 0) A)).
Proof.
  intros Hi He Hb Hbasic Hbe Hnegative HA.
  assert (Hsign : (0 <? pivot_coef A k i e) = false) by (apply Z.ltb_ge; lia).
  assert (Henter : 0 <= i*k+e < m*k) by
    (apply pivot_row_slot_bounds__finish_elimination; assumption).
  assert (Hleave : 0 <= i*k+b < m*k) by
    (apply pivot_row_slot_bounds__finish_elimination; assumption).
  unfold pivot_raw_table, pivot_row_constant, pivot_row_coef, pivot_orientation.
  cbn zeta. rewrite Hsign, <- Hbasic.
  split; [reflexivity|].
  split.
  - replace (- (-1) * Znth i C 0) with (Znth i C 0) by ring.
    symmetry. apply replace_Znth_Znth.
  - intros j v Hj Hv.
    assert (Hindex : 0 <= j*k+v < m*k) by
      (apply pivot_row_slot_bounds__finish_elimination; assumption).
    unfold pivot_coef.
    destruct (Z.eq_dec j i) as [->|Hji].
    + rewrite Z.eqb_refl.
      destruct (Z.eq_dec v e) as [->|Hve].
      * rewrite Z.eqb_refl, Znth_replace_Znth_Same by
          (rewrite Zlength_replace_Znth; lia).
        reflexivity.
      * rewrite (proj2 (Z.eqb_neq v e) Hve).
        rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
        destruct (Z.eq_dec v b) as [->|Hvb].
        -- rewrite Z.eqb_refl, Znth_replace_Znth_Same by lia.
           ring.
        -- rewrite (proj2 (Z.eqb_neq v b) Hvb), Znth_replace_Znth_Diff by lia.
           ring.
    + rewrite (proj2 (Z.eqb_neq j i) Hji).
      assert (Hdifferent_e : i*k+e <> j*k+v) by
        (apply pivot_row_slot_distinct__finish_elimination; try assumption; left; lia).
      assert (Hdifferent_b : i*k+b <> j*k+v) by
        (apply pivot_row_slot_distinct__finish_elimination; try assumption; left; lia).
      rewrite !Znth_replace_Znth_Diff by
        (try rewrite Zlength_replace_Znth; lia).
      reflexivity.
Qed.
Lemma pivot_slot_absent__elimination_columns (N : list Z) s :
  NoDup N -> 0 <= s < Zlength N ->
  ~ In (Znth s N 0) (sublist 0 s N).
Proof.
  intros Hnodup Hs Hin.
  rewrite <- (sublist_self N (Zlength N)) in Hnodup by reflexivity.
  rewrite (sublist_split 0 (Zlength N) s N) in Hnodup by lia.
  rewrite (sublist_split s (Zlength N) (s+1) N) in Hnodup by lia.
  rewrite (sublist_single 0 s N) in Hnodup by lia.
  simpl in Hnodup.
  apply NoDup_remove_2 in Hnodup.
  apply Hnodup, in_or_app. now left.
Qed.
Lemma pivot_prefix_membership__elimination_columns (N : list Z) s v :
  0 <= s < Zlength N ->
  v <> Znth s N 0 ->
  (In v (sublist 0 (s + 1) N) <-> In v (sublist 0 s N)).
Proof.
  intros Hs Hneq.
  rewrite (sublist_split 0 (s + 1) s N) by lia.
  rewrite (sublist_single 0 s N) by lia.
  rewrite in_app_iff. simpl. intuition congruence.
Qed.
Lemma pivot_elimination_slot_step__elimination_columns m k r e i s mu nu
    A N before cur new :
  0 <= s < Zlength N ->
  pivot_elimination_slots m k r e i s mu nu A N before cur ->
  (forall j u, 0 <= j < m -> 0 <= u < k ->
    pivot_coef new k j u =
      if andb (j =? i) (andb (u =? Znth s N 0) (negb (u =? e))) then
        mu * pivot_coef A k j u + nu * pivot_coef before k r u
      else pivot_coef cur k j u) ->
  pivot_elimination_slots m k r e i (s + 1) mu nu A N before new.
Proof.
  intros Hs Hold Hnew j u Hj Hu.
  rewrite (Hnew j u Hj Hu), (Hold j u Hj Hu).
  destruct (j =? i) eqn:Hrow; simpl.
  2: reflexivity.
  destruct (u =? e) eqn:Henter; simpl.
  - now destruct (u =? Znth s N 0).
  - destruct (u =? Znth s N 0) eqn:Hslot; simpl.
    + apply Z.eqb_eq in Hslot.
      destruct (in_dec Z.eq_dec u (sublist 0 (s + 1) N)) as [Hin|Hout].
      * reflexivity.
      * exfalso. apply Hout.
        rewrite (sublist_split 0 (s + 1) s N) by lia.
        rewrite (sublist_single 0 s N) by lia.
        apply in_or_app. right. simpl. auto.
    + apply Z.eqb_neq in Hslot.
      pose proof (pivot_prefix_membership__elimination_columns N s u Hs Hslot).
      destruct (in_dec Z.eq_dec u (sublist 0 s N)),
        (in_dec Z.eq_dec u (sublist 0 (s + 1) N)); intuition.
Qed.
Lemma pivot_member_at__basis_metadata v (xs : list Z) :
  In v xs <-> exists j, 0 <= j < Zlength xs /\ Znth j xs 0 = v.
Proof.
  split.
  - intros Hin.
    destruct (In_nth xs v 0 Hin) as [j [Hj Hval]].
    exists (Z.of_nat j). split.
    + rewrite Zlength_correct. lia.
    + unfold Znth. now rewrite Nat2Z.id.
  - intros [j [Hj <-]]. now apply Znth_In_Zlength.
Qed.
Lemma pivot_nodup_indices__basis_metadata (xs : list Z) :
  NoDup xs <->
  forall i j, 0 <= i < Zlength xs -> 0 <= j < Zlength xs ->
    Znth i xs 0 = Znth j xs 0 -> i = j.
Proof.
  split.
  - intros Hnd i j Hi Hj Heq.
    rewrite Zlength_correct in Hi, Hj. unfold Znth in Heq.
    assert (Z.to_nat i = Z.to_nat j).
    { eapply (proj1 (NoDup_nth xs 0) Hnd); [lia | lia | exact Heq]. }
    lia.
  - intros Hunique. apply (proj2 (NoDup_nth xs 0)).
    intros i j Hi Hj Heq.
    assert (Z.of_nat i = Z.of_nat j).
    { apply Hunique; try (rewrite Zlength_correct; lia).
      unfold Znth. now rewrite !Nat2Z.id. }
    lia.
Qed.
Lemma pivot_replace_nodup__basis_metadata i x (xs : list Z) :
  0 <= i < Zlength xs -> NoDup xs -> ~ In x xs ->
  NoDup (replace_Znth i x xs) /\
  (forall v, In v (replace_Znth i x xs) <->
    v = x \/ (In v xs /\ v <> Znth i xs 0)).
Proof.
  intros Hi Hnd Hfresh.
  pose proof (proj1 (pivot_nodup_indices__basis_metadata xs) Hnd) as Hunique.
  split.
  - apply (proj2 (pivot_nodup_indices__basis_metadata _)).
    intros j l Hj Hl Heq.
    rewrite Zlength_replace_Znth in Hj, Hl.
    destruct (Z.eq_dec i j) as [<- | Hij];
      destruct (Z.eq_dec i l) as [<- | Hil]; try reflexivity.
    + rewrite Znth_replace_Znth_Same, Znth_replace_Znth_Diff in Heq by lia.
      exfalso. apply Hfresh. rewrite Heq. now apply Znth_In_Zlength.
    + rewrite Znth_replace_Znth_Diff, Znth_replace_Znth_Same in Heq by lia.
      exfalso. apply Hfresh. rewrite <- Heq. now apply Znth_In_Zlength.
    + rewrite !Znth_replace_Znth_Diff in Heq by lia.
      now apply Hunique.
  - intros v. split.
    + intros Hin.
      apply pivot_member_at__basis_metadata in Hin.
      destruct Hin as [j [Hj Hv]].
      rewrite Zlength_replace_Znth in Hj.
      destruct (Z.eq_dec i j) as [<- | Hij].
      * left. rewrite Znth_replace_Znth_Same in Hv by lia. symmetry. exact Hv.
      * right. rewrite Znth_replace_Znth_Diff in Hv by lia.
        split.
        -- apply pivot_member_at__basis_metadata. now exists j.
        -- intros Heq. apply Hij. apply Hunique; try assumption. congruence.
    + intros [-> | [Hin Hneq]].
      * apply pivot_member_at__basis_metadata. exists i.
        rewrite Zlength_replace_Znth, Znth_replace_Znth_Same by lia. auto.
      * apply pivot_member_at__basis_metadata in Hin.
        destruct Hin as [j [Hj Hv]].
        apply pivot_member_at__basis_metadata. exists j.
        rewrite Zlength_replace_Znth, Znth_replace_Znth_Diff by (try congruence; lia).
        auto.
Qed.
Lemma pivot_swap_nonbasic__basis_metadata m k r e q D A B R N :
  0 <= r < m -> 0 <= e < k -> m <= k -> k < UINT_MAX ->
  Zlength B = m -> Zlength R = k ->
  selection_basis m k D A B R -> pivot_nonbasic_columns k B R N ->
  0 <= q < Zlength N -> Znth q N 0 = e -> Znth e R 0 = UINT_MAX ->
  pivot_nonbasic_columns k (pivot_basic r e B) (pivot_row_map r e B R)
    (replace_Znth q (Znth r B 0) N).
Proof.
  intros Hr He Hmk Hk HB HR Hbasis [[Hnd [HBdom [HNdom Hcover]]] Hold] Hq Hqe Hsent.
  destruct (pivot_basis_distinct__pivot_result m k r e D A B R
    Hr Hmk Hk Hbasis Hsent) as [Hb [Hnotenter _]].
  destruct Hbasis as [Hrow _].
  set (b := Znth r B 0).
  assert (Hbe : b <> e) by (apply Hnotenter; exact Hr).
  destruct (Hrow r Hr) as [_ [Hrb _]].
  fold b in Hb, Hrb.
  assert (HfreshN : ~ In b N).
  { intros Hin. pose proof (proj1 (Hold b Hb) Hin). lia. }
  assert (HfreshB : ~ In e B).
  { intros Hin. apply pivot_member_at__basis_metadata in Hin.
    destruct Hin as [j [Hj Hjval]]. rewrite HB in Hj.
    exact (Hnotenter j Hj Hjval). }
  assert (HndB : NoDup B).
  { apply (proj2 (pivot_nodup_indices__basis_metadata B)).
    intros j l Hj Hl Heq. rewrite HB in Hj, Hl.
    destruct (Hrow j Hj) as [_ [Hjmap _]].
    destruct (Hrow l Hl) as [_ [Hlmap _]]. congruence. }
  destruct (pivot_replace_nodup__basis_metadata r e B ltac:(lia) HndB HfreshB)
    as [_ HBswap].
  destruct (pivot_replace_nodup__basis_metadata q b N Hq Hnd HfreshN)
    as [HndN HNswap].
  rewrite Hqe in HNswap.
  set (Rn := pivot_row_map r e B R).
  assert (HRe : Znth e Rn 0 = r).
  { unfold Rn, pivot_row_map. fold b.
    rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
    now rewrite Znth_replace_Znth_Same by lia. }
  assert (HRb : Znth b Rn 0 = UINT_MAX).
  { unfold Rn, pivot_row_map. fold b.
    now rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth; lia). }
  assert (HRother : forall v, 0 <= v < k -> v <> e -> v <> b ->
      Znth v Rn 0 = Znth v R 0).
  { intros v Hv Hve Hvb. unfold Rn, pivot_row_map. fold b.
    repeat rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
    reflexivity. }
  assert (Hsentinel : forall v, 0 <= v < k ->
      In v (replace_Znth q b N) <-> Znth v Rn 0 = UINT_MAX).
  { intros v Hv. rewrite HNswap.
    destruct (Z.eq_dec v e) as [-> | Hve].
    - rewrite HRe. split; [intros [H | [_ H]] | intros H]; lia.
    - destruct (Z.eq_dec v b) as [-> | Hvb].
      + rewrite HRb. tauto.
      + rewrite HRother by assumption. rewrite <- (Hold v Hv). tauto. }
  split; [| exact Hsentinel].
  unfold normalize_columns, pivot_basic. fold b.
  split; [exact HndN |].
  split.
  - intros v Hv. apply HBswap in Hv. destruct Hv as [-> | [Hv _]]; auto.
  - split.
    + intros v Hv. assert (Hbound : 0 <= v < k).
      { apply HNswap in Hv. destruct Hv as [-> | [Hv _]]; [exact Hb |].
        exact (proj1 (HNdom v Hv)). }
      split; [exact Hbound | now apply Hsentinel].
    + intros v Hv. rewrite HBswap, HNswap.
      destruct (Z.eq_dec v e) as [-> | Hve]; [tauto |].
      destruct (Z.eq_dec v b) as [-> | Hvb]; [tauto |].
      fold b. specialize (Hcover v Hv). tauto.
Qed.
Lemma pivot_Znth_overflow__final_result (l : list Z) j :
  Zlength l <= j -> Znth j l 0 = 0.
Proof.
  unfold Znth. rewrite Zlength_correct. intros Hj.
  apply nth_overflow. lia.
Qed.
Lemma pivot_Znth_replace_other__final_result (l : list Z) i j z :
  0 <= i < Zlength l -> 0 <= j -> j <> i ->
  Znth j (replace_Znth i z l) 0 = Znth j l 0.
Proof.
  intros Hi Hj Hneq. destruct (Z_lt_ge_dec j (Zlength l)).
  - apply Znth_replace_Znth_Diff; lia.
  - rewrite !pivot_Znth_overflow__final_result; try rewrite Zlength_replace_Znth; lia.
Qed.
Lemma pivot_final_metadata__final_result m k r e q D A B R N :
  0 <= r < m -> 0 <= e < k -> m <= k -> k < UINT_MAX ->
  0 <= q < Zlength N -> Znth q N 0 = e ->
  selection_basis m k D A B R ->
  pivot_nonbasic_columns k B R N ->
  Znth e R 0 = UINT_MAX ->
  let b := Znth r B 0 in
  let Bn := pivot_basic r e B in
  let Rn := pivot_row_map r e B R in
  let Nn := replace_Znth q b N in
  pivot_nonbasic_columns k Bn Rn Nn ->
  Znth r Bn 0 = e /\
  (forall i, 0 <= i < m -> i <> r -> Znth i Bn 0 = Znth i B 0) /\
  (forall i, 0 <= i < m ->
    0 <= Znth i Bn 0 < k /\ Znth (Znth i Bn 0) Rn 0 = i) /\
  (forall v, 0 <= v < k -> Znth v Rn 0 <> UINT_MAX ->
    0 <= Znth v Rn 0 < m /\ Znth (Znth v Rn 0) Bn 0 = v).
Proof.
  intros Hr He Hmk Hk Hq Hqe Hbasis [[Hnd _] _] Heold b Bn Rn Nn Hnew.
  destruct (pivot_basis_distinct__pivot_result m k r e D A B R
    Hr Hmk Hk Hbasis Heold) as [Hb [Hnoenter Hdistinct]].
  destruct Hbasis as [Hrow [Hcol _]].
  destruct Hnew as [(_ & _ & _ & Hcover) Hsentinel].
  assert (Hbe : b <> e) by (apply Hnoenter; exact Hr).
  assert (Hne : ~ In e Nn).
  { intros Hin. destruct (In_nth Nn e 0 Hin) as [t [Ht Hval]].
    assert (HtN : 0 <= Z.of_nat t < Zlength N).
    { assert (Zlength Nn = Zlength N) by (unfold Nn; apply Zlength_replace_Znth).
      rewrite Zlength_correct in H. lia. }
    assert (Hzn : Znth (Z.of_nat t) Nn 0 = e).
    { unfold Znth. now rewrite Nat2Z.id. }
    clear Hval. rename Hzn into Hval.
    unfold Nn in Hval.
    destruct (Z.eq_dec (Z.of_nat t) q) as [E|E].
    - rewrite E, Znth_replace_Znth_Same in Hval by exact Hq. contradiction.
    - rewrite Znth_replace_Znth_Diff in Hval by lia.
      unfold Znth in Hval, Hqe. rewrite Nat2Z.id in Hval.
      rewrite Zlength_correct in Hq, HtN.
      assert (t = Z.to_nat q)%nat.
      { eapply (proj1 (NoDup_nth N 0) Hnd); lia. }
      lia. }
  assert (Hrl : 0 <= r < Zlength B).
  { destruct (Z_lt_ge_dec r (Zlength B)); [lia|].
    destruct (Hcover e He) as [Hin|Hin]; [|contradiction].
    unfold Bn, pivot_basic in Hin. rewrite replace_Znth_nothing in Hin by lia.
    destruct (In_nth B e 0 Hin) as [t [Ht Hv]].
    exfalso. apply (Hnoenter (Z.of_nat t)).
    - rewrite Zlength_correct in *. lia.
    - unfold Znth. now rewrite Nat2Z.id. }
  assert (Heb : 0 <= e < Zlength R).
  { destruct (Z_lt_ge_dec e (Zlength R)); [lia|].
    rewrite pivot_Znth_overflow__final_result in Heold by lia. discriminate. }
  assert (Hbnew : Znth b Rn 0 = UINT_MAX).
  { apply (proj1 (Hsentinel b Hb)).
    assert (Hnbq : 0 <= q < Zlength Nn) by
      (unfold Nn; now rewrite Zlength_replace_Znth).
    assert (Hnbval : Znth q Nn 0 = b) by
      (unfold Nn; now rewrite Znth_replace_Znth_Same).
    rewrite <- Hnbval.
    unfold Znth. apply nth_In. rewrite Zlength_correct in Hnbq. lia. }
  assert (Hbb : 0 <= b < Zlength R).
  { destruct (Z_lt_ge_dec b (Zlength R)); [lia|].
    unfold Rn, pivot_row_map in Hbnew. fold b in Hbnew.
    rewrite pivot_Znth_overflow__final_result in Hbnew
      by (rewrite !Zlength_replace_Znth; lia).
    discriminate. }
  assert (HB_r : Znth r Bn 0 = e).
  { unfold Bn, pivot_basic. now rewrite Znth_replace_Znth_Same. }
  assert (HB_other : forall i, 0 <= i < m -> i <> r -> Znth i Bn 0 = Znth i B 0).
  { intros i Hi Hir. unfold Bn, pivot_basic.
    apply pivot_Znth_replace_other__final_result; lia. }
  assert (HR_e : Znth e Rn 0 = r).
  { unfold Rn, pivot_row_map. fold b.
    rewrite pivot_Znth_replace_other__final_result by
      (try rewrite Zlength_replace_Znth; lia).
    now rewrite Znth_replace_Znth_Same. }
  assert (HR_other : forall v, 0 <= v < k -> v <> e -> v <> b ->
    Znth v Rn 0 = Znth v R 0).
  { intros v Hv Hve Hvb. unfold Rn, pivot_row_map. fold b.
    rewrite !pivot_Znth_replace_other__final_result by
      (try rewrite Zlength_replace_Znth; lia).
    reflexivity. }
  split; [exact HB_r|]. split; [exact HB_other|]. split.
  - intros i Hi. destruct (Z.eq_dec i r) as [->|Hir].
    + rewrite HB_r, HR_e. auto.
    + destruct (Hrow i Hi) as (Hbi & Hri & _).
      rewrite HB_other by assumption.
      rewrite HR_other by auto. auto.
  - intros v Hv Hactive. destruct (Z.eq_dec v e) as [->|Hve].
    + rewrite HR_e, HB_r. auto.
    + assert (Hvb : v <> b) by (intro E; subst v; contradiction).
      rewrite HR_other in * by assumption.
      destruct (Hcol v Hv Hactive) as [Hri Hbv].
      assert (Hir : Znth v R 0 <> r) by (intro E; rewrite E in Hbv; fold b in Hbv; congruence).
      rewrite HB_other by assumption. auto.
Qed.
Lemma pivot_primitive_row_semantics__final_result k N d0 c0 a0 d c a :
  0 < d0 ->
  (forall v, In v N -> 0 <= v < k) ->
  (forall v, 0 <= v < k -> ~ In v N -> Znth v a0 0 = 0) ->
  (d,c,a) = pivot_primitive_row N d0 c0 a0 k ->
  exists g, 0 < g /\ 0 < d /\
    d0 = d*g /\ c0 = c*g /\
    (forall v, 0 <= v < k -> Znth v a0 0 = Znth v a 0 * g) /\
    fold_left Z.gcd (map (fun v => Znth v a 0) N ++ [c]) d = 1.
Proof.
  intros Hd Hnb Hmask Hres.
  set (values := map (fun v => Znth v a0 0) N ++ [c0]).
  set (g := fold_left Z.gcd values d0).
  assert (Hg : 0 < g) by (apply normalize_fold_gcd_positive; assumption).
  destruct (normalize_fold_gcd_divides values d0) as [Hdd Hvals].
  fold g in Hdd, Hvals.
  unfold values in Hvals. apply Forall_app in Hvals as [Ha Hc].
  rewrite Forall_forall in Ha, Hc.
  assert (Hexact : forall z, (g | z) -> z = Z.quot z g * g).
  { intros z [u Hu]. rewrite Hu, Z.quot_mul by lia. reflexivity. }
  unfold pivot_primitive_row in Hres. fold values g in Hres.
  injection Hres as -> -> ->.
  pose proof (Hexact d0 Hdd) as Hdd'.
  assert (Hcc : c0 = Z.quot c0 g * g).
  { apply Hexact, Hc. now left. }
  assert (Haa : forall v, 0 <= v < k ->
    Znth v a0 0 =
    Znth v (map (fun w => if in_dec Z.eq_dec w N then Z.quot (Znth w a0 0) g else Znth w a0 0)
                (Zrange 0 k)) 0 * g).
  { intros v Hv. rewrite pivot_map_range_at by exact Hv.
    destruct (in_dec Z.eq_dec v N) as [Hin|Hout].
    - apply Hexact, Ha, in_map_iff. exists v. auto.
    - rewrite Hmask by assumption. ring. }
  exists g. split; [exact Hg|]. split; [nia|].
  split; [exact Hdd'|]. split; [exact Hcc|]. split; [exact Haa|].
  match goal with |- fold_left Z.gcd ?outvals ?outd = 1 =>
    assert (Hscaled : values = map (fun z => z*g) outvals);
    [ unfold values; rewrite map_app, map_map; cbn [map];
      rewrite <- Hcc; f_equal; apply map_ext_in; intros v Hv; apply Haa, Hnb; exact Hv
    | assert (Hmul : g = fold_left Z.gcd outvals outd * g);
      [ unfold g at 1; rewrite Hscaled; rewrite Hdd' at 1;
        now rewrite normalize_fold_gcd_mul by lia | nia ] ]
  end.
Qed.
Lemma pivot_primitive_snapshot__final_result k i N d0 c0 f d c a :
  0 <= i -> 0 < d0 ->
  (forall v, In v N -> 0 <= v < k) ->
  (forall v, 0 <= v < k -> ~ In v N -> f v = 0) ->
  pivot_row_snapshot k i d c a =
    pivot_primitive_row N d0 c0 (map f (Zrange 0 k)) k ->
  exists g, 0 < g /\ 0 < Znth i d 0 /\
    d0 = Znth i d 0*g /\ c0 = Znth i c 0*g /\
    (forall v, 0 <= v < k -> f v = pivot_coef a k i v * g) /\
    normalize_row_gcd k i d c a N = 1.
Proof.
  intros Hi Hd Hnb Hmask Hsnap.
  unfold pivot_row_snapshot in Hsnap.
  destruct (pivot_primitive_row_semantics__final_result k N d0 c0 _
    (Znth i d 0) (Znth i c 0) _ Hd Hnb ltac:(intros v Hv; rewrite pivot_map_range_at by exact Hv; apply Hmask, Hv) Hsnap)
    as (g & Hg & Hpos & Hden & Hconst & Hcoeff & Hprimitive).
  exists g. split; [exact Hg|]. split; [exact Hpos|].
  split; [exact Hden|]. split; [exact Hconst|]. split.
  - intros v Hv. specialize (Hcoeff v Hv).
    rewrite pivot_map_range_at, pivot_row_slice_coef in Hcoeff by assumption.
    exact Hcoeff.
  - unfold normalize_row_gcd, normalize_row_values.
    rewrite <- Hprimitive. f_equal. f_equal.
    apply map_ext_in. intros v Hv.
    rewrite pivot_row_slice_coef by auto. reflexivity.
Qed.
Lemma pivot_scaled_residual__final_result (cols : list Z) (x : Z -> Q)
    (g d0 c0 : Z) (f0 : Z -> Z) (d c : Z) (f : Z -> Z) (b : Z) :
  d0 = (d*g)%Z -> c0 = (c*g)%Z ->
  (forall v, In v cols -> f0 v = (f v*g)%Z) ->
  (inject_Z d0 * x b - inject_Z c0 -
    fold_right Qplus 0 (map (fun v => inject_Z (f0 v) * x v) cols) ==
   inject_Z g * (inject_Z d * x b - inject_Z c -
    fold_right Qplus 0 (map (fun v => inject_Z (f v) * x v) cols)))%Q.
Proof.
  intros -> -> Hf.
  rewrite !inject_Z_mult.
  transitivity (inject_Z d * inject_Z g * x b - inject_Z c * inject_Z g -
    fold_right Qplus 0
      (map (fun v => inject_Z g * (inject_Z (f v) * x v) + 0*0) cols))%Q.
  - apply Qplus_comp; [reflexivity|]. apply Qopp_comp.
    apply pivot_dot_ext__pivot_result. intros v Hv.
    rewrite (Hf v Hv), inject_Z_mult. ring.
  - rewrite pivot_dot_linear__pivot_result. ring.
Qed.
Lemma pivot_integer_factor_zero__final_result (g : Z) (p : Q) :
  g <> 0%Z -> (inject_Z g * p == 0)%Q -> (p == 0)%Q.
Proof.
  intros Hg Hp. apply (Qmult_integral_l (inject_Z g)).
  - intro E. apply Hg. now apply inject_Z_injective.
  - exact Hp.
Qed.
Lemma pivot_final_rows_sound__final_result m k r e q D C A B R N d c a :
  (0 <= r < m)%Z -> (0 <= e < k)%Z -> (m <= k)%Z -> (k < UINT_MAX)%Z ->
  (0 <= q < Zlength N)%Z -> Znth q N 0%Z = e ->
  selection_basis m k D A B R -> pivot_nonbasic_columns k B R N ->
  Znth e R 0%Z = UINT_MAX -> pivot_coef A k r e <> 0%Z ->
  let b := Znth r B 0%Z in
  let Bn := pivot_basic r e B in
  let Rn := pivot_row_map r e B R in
  let Nn := replace_Znth q b N in
  pivot_nonbasic_columns k Bn Rn Nn ->
  pivot_normalized_prefix m k r e m D C A B Nn d c a ->
  pivot_optimized_result m k r e q D C A B R N d c a Bn Rn Nn.
Proof.
  intros Hr He Hmk Hk Hq Hqe Hbasis Hmeta Her Hh b Bn Rn Nn Hmeta' Hprefix.
  pose proof (pivot_final_metadata__final_result m k r e q D A B R N
    Hr He Hmk Hk Hq Hqe Hbasis Hmeta Her Hmeta') as Hupdate.
  fold Bn Rn in Hupdate.
  destruct Hupdate as (HBr & HBother & Hrow_map & Hmap_row).
  assert (Hb : (0 <= b < k)%Z).
  { apply (proj1 (proj1 Hbasis r Hr)). }
  assert (Hbe : b <> e).
  { intro E. pose proof (proj1 (proj2 (proj1 Hbasis r Hr))) as Hrow.
    fold b in Hrow. rewrite E, Her in Hrow. lia. }
  destruct Hbasis as (Hrow & Hcol & Hzero).
  assert (Hbasic_zero : forall i j, (0 <= i < m)%Z -> (0 <= j < m)%Z ->
    pivot_coef A k i (Znth j B 0%Z) = 0%Z) by exact Hzero.
  assert (Henters : forall j, (0 <= j < m)%Z -> Znth j B 0%Z <> e).
  { intros j Hj E. pose proof (proj1 (proj2 (Hrow j Hj))) as Hrowj.
    rewrite E, Her in Hrowj. lia. }
  assert (Hdiff : forall j, (0 <= j < m)%Z -> j <> r -> Znth j B 0%Z <> b).
  { intros j Hj Hjr E. pose proof (proj1 (proj2 (Hrow j Hj))) as Hrowj.
    pose proof (proj1 (proj2 (Hrow r Hr))) as Hrowr.
    rewrite E in Hrowj. fold b in Hrowr. congruence. }
  assert (Hnonbasic : forall v, In v Nn -> (0 <= v < k)%Z).
  { intros v Hv. exact (proj1 (proj1 (proj2 (proj2 (proj1 Hmeta'))) v Hv)). }
  assert (Hnew_basic : forall v, (0 <= v < k)%Z -> ~ In v Nn ->
    v = e \/ exists j, (0 <= j < m)%Z /\ j <> r /\ v = Znth j B 0%Z).
  { intros v Hv Hout.
    pose proof (proj2 Hmeta' v Hv) as Hiff.
    destruct (Hmap_row v Hv ltac:(intuition)) as [Hj Hbv].
    destruct (Z.eq_dec (Znth v Rn 0%Z) r) as [E|E].
    - rewrite E, HBr in Hbv. now left.
    - right. exists (Znth v Rn 0%Z). rewrite HBother in Hbv by assumption. auto. }
  assert (Hsnap : forall i, (0 <= i < m)%Z ->
    pivot_row_snapshot k i d c a = pivot_final_row k r e i D C A B Nn).
  { intros i Hi. pose proof (Hprefix i Hi) as H.
    rewrite (proj2 (Z.ltb_lt i m) (proj2 Hi)), Bool.orb_true_r in H. exact H. }
  set (h := pivot_coef A k r e).
  set (P := Znth r d 0%Z).
  set (T := Znth r c 0%Z).
  set (U := sublist (r*k)%Z ((r+1)*k)%Z a).
  set (f := fun v => pivot_row_coef e b h (Znth r D 0%Z) v (pivot_coef A k r v)).
  assert (Hnor : (P,T,U) = pivot_normalized_row k r e D C A B Nn).
  { pose proof (Hsnap r Hr) as H.
    unfold pivot_final_row in H. rewrite Z.eqb_refl in H.
    destruct (pivot_normalized_row k r e D C A B Nn) as [[pp tt] uu].
    exact H. }
  assert (Hfzero : forall v, (0 <= v < k)%Z -> ~ In v Nn -> f v = 0%Z).
  { intros v Hv Hout. unfold f, pivot_row_coef.
    destruct (Hnew_basic v Hv Hout) as [->|(j & Hj & Hjr & ->)].
    - now rewrite Z.eqb_refl.
    - rewrite (proj2 (Z.eqb_neq _ _) (Henters j Hj)),
        (proj2 (Z.eqb_neq _ _) (Hdiff j Hj Hjr)), Hbasic_zero by assumption.
      ring. }
  destruct (pivot_primitive_snapshot__final_result k r Nn (Z.abs h)
    (pivot_row_constant h (Znth r C 0%Z)) f d c a
    ltac:(lia) ltac:(apply Z.abs_pos; exact Hh) Hnonbasic Hfzero Hnor)
    as (gr & Hgr & HP & HDr & HCr & HAr & HGcdr).
  fold P in HP, HDr. fold T in HCr.
  assert (HAe : pivot_coef a k r e = 0%Z).
  { specialize (HAr e He). unfold f, pivot_row_coef in HAr.
    rewrite Z.eqb_refl in HAr. nia. }
  assert (HAzero : forall v, (0 <= v < k)%Z -> ~ In v Nn -> pivot_coef a k r v = 0%Z).
  { intros v Hv Hout. specialize (HAr v Hv). rewrite Hfzero in HAr by assumption. nia. }
  set (mu := fun i => Z.quot P (Z.gcd P (pivot_coef A k i e))).
  set (nu := fun i => Z.quot (pivot_coef A k i e) (Z.gcd P (pivot_coef A k i e))).
  set (frow := fun i v => if (v =? e)%Z then 0%Z
                else (mu i * pivot_coef A k i v + nu i * pivot_coef a k r v)%Z).
  assert (Hmuls : forall i, (0 < mu i)%Z /\ (mu i * pivot_coef A k i e)%Z = (nu i * P)%Z).
  { intro i.
    destruct (pivot_gcd_exact P (pivot_coef A k i e) HP) as (Hg & Hden & Hx).
    unfold pivot_divides_exactly in Hden, Hx.
    fold (mu i) in Hden. fold (nu i) in Hx. split; nia. }
  assert (Hunchanged : forall i, (0 <= i < m)%Z -> i <> r -> pivot_coef A k i e = 0%Z ->
    Znth i d 0%Z = Znth i D 0%Z /\ Znth i c 0%Z = Znth i C 0%Z /\
    (forall v, (0 <= v < k)%Z -> pivot_coef a k i v = pivot_coef A k i v)).
  { intros i Hi Hir Hz. specialize (Hsnap i Hi).
    unfold pivot_final_row in Hsnap. rewrite <- Hnor in Hsnap.
    rewrite (proj2 (Z.eqb_neq _ _) Hir), Hz, Z.eqb_refl in Hsnap.
    unfold pivot_row_snapshot in Hsnap.
    injection Hsnap as H1 H2 H3. split; [assumption|]. split; [assumption|].
    intros v Hv. rewrite <- !pivot_row_slice_coef by lia. congruence. }
  assert (Hfmask : forall i, (0 <= i < m)%Z -> forall v,
    (0 <= v < k)%Z -> ~ In v Nn -> frow i v = 0%Z).
  { intros i Hi v Hv Hout. unfold frow.
    destruct (Hnew_basic v Hv Hout) as [->|(j & Hj & Hjr & ->)].
    - now rewrite Z.eqb_refl.
    - rewrite (proj2 (Z.eqb_neq _ _) (Henters j Hj)),
        (Hbasic_zero i j Hi Hj), HAzero by assumption. ring. }
  assert (Hchanged : forall i, (0 <= i < m)%Z -> i <> r -> pivot_coef A k i e <> 0%Z ->
    exists g, (0 < g)%Z /\ (0 < Znth i d 0%Z)%Z /\
    (mu i * Znth i D 0%Z)%Z = (Znth i d 0%Z*g)%Z /\
    (mu i * Znth i C 0%Z + nu i*T)%Z = (Znth i c 0%Z*g)%Z /\
    (forall v, (0 <= v < k)%Z -> frow i v = (pivot_coef a k i v * g)%Z) /\
    normalize_row_gcd k i d c a Nn = 1%Z).
  { intros i Hi Hir Hz. specialize (Hsnap i Hi).
    unfold pivot_final_row in Hsnap. rewrite <- Hnor in Hsnap.
    rewrite (proj2 (Z.eqb_neq _ _) Hir), (proj2 (Z.eqb_neq _ _) Hz) in Hsnap.
    apply (pivot_primitive_snapshot__final_result k i Nn _ _ (frow i));
      try lia; try exact Hnonbasic; try (apply Hfmask; exact Hi).
    - pose proof (proj1 (Hmuls i)). pose proof (proj2 (proj2 (Hrow i Hi))). nia.
    - unfold frow. unfold U in Hsnap. unfold mu, nu.
      rewrite Hsnap. f_equal. apply map_ext_in. intros v Hv.
      apply (proj2 (In_Zrange 0 k v)) in Hv.
      rewrite pivot_row_slice_coef by lia. reflexivity. }
  unfold pivot_optimized_result.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hprefix|]. split.
  - split.
    + intros i Hi. destruct (Hrow_map i Hi) as [Hdom Hslot].
      split; [exact Hdom|]. split; [exact Hslot|].
      destruct (Z.eq_dec i r) as [->|Hir]; [exact HP|].
      destruct (Z.eq_dec (pivot_coef A k i e) 0) as [Hz|Hz].
      * rewrite (proj1 (Hunchanged i Hi Hir Hz)). exact (proj2 (proj2 (Hrow i Hi))).
      * destruct (Hchanged i Hi Hir Hz) as (g & Hg & Hpos & _). exact Hpos.
    + split; [exact Hmap_row|].
      intros i j Hi Hj.
      change (pivot_coef a k i (Znth j Bn 0%Z) = 0%Z).
      assert (Hv : (0 <= Znth j Bn 0%Z < k)%Z) by apply (proj1 (Hrow_map j Hj)).
      assert (Hout : ~ In (Znth j Bn 0%Z) Nn).
      { intro H. apply (proj1 (proj2 Hmeta' _ Hv)) in H.
        rewrite (proj2 (Hrow_map j Hj)) in H. lia. }
      destruct (Z.eq_dec i r) as [->|Hir]; [apply HAzero; assumption|].
      destruct (Z.eq_dec (pivot_coef A k i e) 0) as [Hz|Hz].
      * destruct (Hunchanged i Hi Hir Hz) as (_ & _ & Hsame).
        rewrite Hsame by assumption.
        destruct (Z.eq_dec j r) as [->|Hjr].
        -- rewrite HBr. exact Hz.
        -- rewrite HBother by assumption. apply Hbasic_zero; assumption.
      * destruct (Hchanged i Hi Hir Hz) as (g & Hg & _ & _ & _ & Hscale & _).
        specialize (Hscale _ Hv). rewrite Hfmask in Hscale by assumption. nia.
  - split; [exact Hmeta'|]. split.
    + intros i Hi Hactive. destruct (Z.eq_dec i r) as [->|Hir]; [exact HGcdr|].
      destruct Hactive as [H|H]; [contradiction|].
      destruct (Hchanged i Hi Hir H) as (g & _ & _ & _ & _ & _ & Hgcd). exact Hgcd.
    + unfold pivot_equations_equivalent. intro x.
      set (cols := Zrange 0 k).
      set (dot := fun (f : Z -> Z) => fold_right Qplus 0%Q
        (map (fun v => (inject_Z (f v) * x v)%Q) cols)).
      set (res := fun (den con : Z) (f : Z -> Z) (bas : Z) =>
        (inject_Z den * x bas - inject_Z con - dot f)%Q).
      set (old := fun i => res (Znth i D 0%Z) (Znth i C 0%Z)
        (pivot_coef A k i) (Znth i B 0%Z)).
      set (new := fun i => res (Znth i d 0%Z) (Znth i c 0%Z)
        (pivot_coef a k i) (Znth i Bn 0%Z)).
      assert (Holds : forall dd cc aa bb,
        pivot_table_equations m k dd cc aa bb x <->
        forall i, (0 <= i < m)%Z ->
          (res (Znth i dd 0%Z) (Znth i cc 0%Z) (pivot_coef aa k i) (Znth i bb 0%Z) == 0)%Q).
      { intros dd cc aa bb. unfold pivot_table_equations, res, dot, cols.
        split; intros H i Hi; apply pivot_equation_residual__pivot_result; now apply H. }
      rewrite !Holds. fold old new.
      assert (Hcols : forall v, In v cols -> (0 <= v < k)%Z).
      { intros v Hv. apply (proj2 (In_Zrange 0 k v)); exact Hv. }
      assert (He_col : In e cols) by (apply In_Zrange; exact He).
      assert (Hb_col : In b cols) by (apply In_Zrange; exact Hb).
      assert (Hnd : NoDup cols) by (apply NoDup_Zrange).
      set (s := pivot_orientation h).
      assert (Hs : s <> 0%Z).
      { unfold s, pivot_orientation. destruct ((0 <? h)%Z); lia. }
      assert (Habs : Z.abs h = (s*h)%Z).
      { unfold s, pivot_orientation.
        destruct (Z.ltb_spec 0 h).
        - rewrite Z.abs_eq by lia. ring.
        - rewrite Z.abs_neq by lia. ring. }
      assert (Hdot_r : (dot f == - inject_Z s * dot (pivot_coef A k r) +
        inject_Z s * inject_Z h * x e + inject_Z s * inject_Z (Znth r D 0%Z) * x b)%Q).
      { transitivity ((-inject_Z s) * dot (pivot_coef A k r) +
          0 * fold_right Qplus 0 (map (fun _ : Z => 0%Q) cols) +
          (inject_Z s * inject_Z h * x e +
            inject_Z s * inject_Z (Znth r D 0%Z) * x b))%Q.
        2: ring.
        unfold dot. apply (pivot_rational_sum__pivot_result cols _ _ _ _ _ _ _ e b);
          [exact Hnd|exact He_col|exact Hb_col|].
        intros v Hv. unfold f, pivot_row_coef. fold s.
        destruct (Z.eqb_spec v e) as [->|Hve].
        - rewrite (proj2 (Z.eqb_neq e b) ltac:(congruence)). fold h. ring.
        - destruct (Z.eqb_spec v b) as [->|Hvb].
          + assert (Hbasic_b : pivot_coef A k r b = 0%Z) by (apply Hbasic_zero; exact Hr).
            rewrite Hbasic_b, inject_Z_mult. ring.
          + rewrite inject_Z_mult, inject_Z_opp. ring. }
      assert (Hpivot : (inject_Z gr * new r == - inject_Z s * old r)%Q).
      { unfold new at 1. rewrite HBr.
        transitivity (res (Z.abs h) (pivot_row_constant h (Znth r C 0%Z)) f e).
        - symmetry. unfold res, dot. apply pivot_scaled_residual__final_result;
            [exact HDr|exact HCr|intros v Hv; apply HAr, Hcols, Hv].
        - unfold old, res. rewrite Hdot_r, Habs.
          unfold pivot_row_constant. fold s b.
          rewrite !inject_Z_mult, inject_Z_opp. ring. }
      assert (Hsame : forall i, (0 <= i < m)%Z -> i <> r -> pivot_coef A k i e = 0%Z ->
        (new i == old i)%Q).
      { intros i Hi Hir Hz.
        destruct (Hunchanged i Hi Hir Hz) as (Hden & Hconst & Hcoef).
        unfold old, new, res. rewrite HBother by assumption. rewrite Hden, Hconst.
        assert (Hdot : (dot (pivot_coef a k i) == dot (pivot_coef A k i))%Q).
        { unfold dot. apply pivot_dot_ext__pivot_result. intros v Hv.
          rewrite Hcoef by (apply Hcols; exact Hv). reflexivity. }
        now rewrite Hdot. }
      assert (Hmix : forall i, (0 <= i < m)%Z -> i <> r -> pivot_coef A k i e <> 0%Z ->
        exists g, (0 < g)%Z /\ (inject_Z g * new i ==
          inject_Z (mu i) * old i + inject_Z (nu i) * new r)%Q).
      { intros i Hi Hir Hz.
        destruct (Hchanged i Hi Hir Hz) as (g & Hg & _ & Hden & Hconst & Hcoef & _).
        exists g. split; [exact Hg|].
        assert (Hrcoef : (dot (frow i) ==
          inject_Z (mu i) * dot (pivot_coef A k i) +
          inject_Z (nu i) * dot (pivot_coef a k r) -
          inject_Z (mu i) * inject_Z (pivot_coef A k i e) * x e)%Q).
        { transitivity (inject_Z (mu i) * dot (pivot_coef A k i) +
            inject_Z (nu i) * dot (pivot_coef a k r) +
            ((-inject_Z (mu i)) * inject_Z (pivot_coef A k i e) * x e + 0))%Q.
          2: ring.
          unfold dot. apply (pivot_rational_sum__pivot_result cols _ _ _ _ _ _ _ e b);
            [exact Hnd|exact He_col|exact Hb_col|].
          intros v Hv. unfold frow.
          destruct (Z.eqb_spec v e) as [->|Hve].
          - rewrite (proj2 (Z.eqb_neq e b) ltac:(congruence)), HAe. ring.
          - rewrite inject_Z_plus, !inject_Z_mult.
            destruct (v =? b)%Z; ring. }
        transitivity (res (mu i * Znth i D 0%Z)%Z (mu i * Znth i C 0%Z + nu i*T)%Z
          (frow i) (Znth i Bn 0%Z)).
        - symmetry. unfold new, res, dot. apply pivot_scaled_residual__final_result;
            [exact Hden|exact Hconst|intros v Hv; apply Hcoef, Hcols, Hv].
        - pose proof (f_equal inject_Z (proj2 (Hmuls i))) as Hcross.
          rewrite !inject_Z_mult in Hcross.
          unfold old, new, res. rewrite HBother by assumption. rewrite HBr, Hrcoef.
          fold P T. rewrite inject_Z_plus, !inject_Z_mult, Hcross. ring. }
      split; intros Equations.
      * change (forall i, (0 <= i < m)%Z -> (old i == 0)%Q) in Equations.
        change (forall i, (0 <= i < m)%Z -> (new i == 0)%Q).
        assert (Hnew_r : (new r == 0)%Q).
        { apply (pivot_integer_factor_zero__final_result gr); [lia|].
          rewrite Hpivot, (Equations r Hr). ring. }
        intros i Hi. destruct (Z.eq_dec i r) as [->|Hir]; [exact Hnew_r|].
        destruct (Z.eq_dec (pivot_coef A k i e) 0) as [Hz|Hz].
        -- rewrite (Hsame i Hi Hir Hz). exact (Equations i Hi).
        -- destruct (Hmix i Hi Hir Hz) as [g [Hg Hcomb]].
           apply (pivot_integer_factor_zero__final_result g); [lia|].
           rewrite Hcomb, (Equations i Hi), Hnew_r. ring.
      * change (forall i, (0 <= i < m)%Z -> (new i == 0)%Q) in Equations.
        change (forall i, (0 <= i < m)%Z -> (old i == 0)%Q).
        assert (Hold_r : (old r == 0)%Q).
        { apply (pivot_integer_factor_zero__final_result (-s)%Z); [lia|].
          rewrite inject_Z_opp, <- Hpivot, (Equations r Hr). ring. }
        intros i Hi. destruct (Z.eq_dec i r) as [->|Hir]; [exact Hold_r|].
        destruct (Z.eq_dec (pivot_coef A k i e) 0) as [Hz|Hz].
        -- rewrite <- (Hsame i Hi Hir Hz). exact (Equations i Hi).
        -- destruct (Hmix i Hi Hir Hz) as [g [Hg Hcomb]].
           apply (pivot_integer_factor_zero__final_result (mu i)).
           ++ pose proof (proj1 (Hmuls i)). lia.
           ++ transitivity (inject_Z (mu i) * old i + inject_Z (nu i) * new r)%Q.
              ** rewrite (Equations r Hr). ring.
              ** rewrite <- Hcomb, (Equations i Hi). ring.
Qed.
