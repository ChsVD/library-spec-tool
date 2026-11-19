From Coq Require Import ZArith List Lia String.
From AUXLib Require Import ListLib.
From ListLib.General Require Import Length.
From ListLib.Base Require Import Positional.
From SumLib Require Import ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_lib.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import build_opt_lib.
From SimpleC.EE.Applications_human.simplex_gmp_minimal Require Import pivot_fme_model_lib.
Import ListNotations naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.

(* Basis metadata, restricted to the facts needed for this row. Other rows may
   still be at an intermediate elimination stage. *)
Definition normalize_columns (k : Z) (basic row nb : list Z) : Prop :=
  NoDup nb /\
  (forall v, In v basic -> 0 <= v < k) /\
  (forall v, In v nb -> 0 <= v < k /\ Znth v row 0 = UINT_MAX) /\
  (forall v, 0 <= v < k -> In v basic \/ In v nb).

Definition normalize_basic_zero (k r : Z) (a b : list Z) : Prop :=
  Forall (fun v => Znth (r*k+v) a 0 = 0) b.

Definition normalize_row_values (k r : Z) (a c nb : list Z) : list Z :=
  map (fun j => Znth (r*k+j) a 0) nb ++ [Znth r c 0].

Definition normalize_prefix_gcd (d s : Z) (values : list Z) : Z :=
  fold_left Z.gcd (sublist 0 s values) d.

Definition normalize_row_gcd (k r : Z) (d c a nb : list Z) : Z :=
  fold_left Z.gcd (normalize_row_values k r a c nb) (Znth r d 0).

(* Mathematical state of the coefficient array when the visited columns
   have been divided by the common positive divisor. *)
Definition normalize_coeff_prefix (m k r g s : Z)
    (a nb out : list Z) : Prop :=
  Zlength out = m*k /\
  (forall p, 0 <= p < m*k ->
      (exists j, In j (sublist 0 s nb) /\ p = r*k+j) ->
      Znth p out 0 = Z.quot (Znth p a 0) g) /\
  (forall p, 0 <= p < m*k ->
      (forall j, In j (sublist 0 s nb) -> p <> r*k+j) ->
      Znth p out 0 = Znth p a 0).

Definition normalize_result (m k r : Z) (d c a nb dn cn an : list Z) : Prop :=
  let g := normalize_row_gcd k r d c a nb in
  dn = replace_Znth r (Z.quot (Znth r d 0) g) d /\
  cn = replace_Znth r (Z.quot (Znth r c 0) g) c /\
  normalize_coeff_prefix m k r g (Zlength nb) a nb an.

(* The positive one-limb case exposes exactly the readable limb required
   by the source's short-circuit check for g=1. *)
Lemma normalize_single_limb_open p z :
  mpd_store_Z_compact UINT_MOD p z 1 |--
    “ 1 <= z < UINT_MOD ” && UIntArray.full p 1 [z].
Proof.
  unfold mpd_store_Z_compact.
  Intros data.
  assert (Hsingle : exists limb, data = [limb]).
  { destruct data as [|limb [|next tail]].
    - rewrite Zlength_nil in *. lia.
    - eauto.
    - repeat rewrite Zlength_cons in *.
      pose proof (Zlength_nonneg tail). lia. }
  destruct Hsingle as [limb ->].
  match goal with H : list_to_Z UINT_MOD [limb] = z /\ _ |- _ =>
    destruct H as [Hval [Hhigh Hbounds]]
  end.
  rewrite list_to_Z_single in Hval.
  subst z.
  simpl in Hhigh, Hbounds.
  unfold mpd_store_list.
  rewrite Zlength_cons, Zlength_nil in *.
  change (Z.succ 0) with 1 in *.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. lia.
Qed.

Lemma normalize_single_limb_close p z :
  1 <= z < UINT_MOD ->
  UIntArray.full p 1 [z] |-- mpd_store_Z_compact UINT_MOD p z 1.
Proof.
  intros Hz.
  unfold mpd_store_Z_compact.
  Exists [z].
  unfold mpd_store_list.
  rewrite Zlength_cons, Zlength_nil.
  change (Z.succ 0) with 1 in *.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; rewrite ?list_to_Z_single; simpl; lia.
Qed.

(* A nonzero initial denominator makes every prefix divisor positive. *)
Lemma normalize_fold_gcd_positive values d :
  0 < d -> 0 < fold_left Z.gcd values d.
Proof.
  revert d. induction values as [|x tail IH]; intros d Hd; simpl.
  - exact Hd.
  - apply IH. pose proof (Z.gcd_nonneg d x).
    assert (Z.gcd d x <> 0) by (intro E; apply Z.gcd_eq_0 in E; lia).
    lia.
Qed.

(* Divisibility characterization is independent of the scan order. *)
Lemma normalize_fold_gcd_divides values d :
  let g := fold_left Z.gcd values d in (g | d) /\ Forall (Z.divide g) values.
Proof.
  revert d. induction values as [|x tail IH]; intro d; cbn zeta.
  - simpl. split; [apply Z.divide_refl|constructor].
  - simpl. destruct (IH (Z.gcd d x)) as [Hstep Htail].
    split.
    + eapply Z.divide_trans; [exact Hstep|apply Z.gcd_divide_l].
    + constructor; [eapply Z.divide_trans; [exact Hstep|apply Z.gcd_divide_r]|exact Htail].
Qed.

Lemma normalize_fold_gcd_greatest values d c :
  (c | d) -> Forall (Z.divide c) values -> (c | fold_left Z.gcd values d).
Proof.
  revert d. induction values as [|x tail IH]; intros d Hd Hvalues; simpl.
  - exact Hd.
  - inversion Hvalues; subst. apply IH; auto using Z.gcd_greatest.
Qed.

Lemma normalize_prefix_gcd_step d s values :
  0 <= s < Zlength values ->
  normalize_prefix_gcd d (s+1) values =
  Z.gcd (normalize_prefix_gcd d s values) (Znth s values 0).
Proof.
  intro Hs. unfold normalize_prefix_gcd.
  rewrite (sublist_split 0 (s+1) s values) by lia.
  rewrite (sublist_single 0 s values) by lia.
  rewrite fold_left_app. reflexivity.
Qed.

Lemma normalize_fold_gcd_one values : fold_left Z.gcd values 1 = 1.
Proof.
  induction values as [|x tail IH]; [reflexivity|].
  change (fold_left Z.gcd tail (Z.gcd 1 x) = 1).
  now rewrite Z.gcd_1_l.
Qed.

(* The checked tdiv_r caller provides the signed truncating remainder. *)
Lemma normalize_rem_gcd g x :
  0 < g -> Z.gcd g (Z.rem x g) = Z.gcd g x.
Proof.
  intro H; rewrite (Z.gcd_comm g (Z.rem x g)).
  apply Z.gcd_rem. lia.
Qed.

Lemma normalize_divides_quot x g :
  g <> 0 -> (g | x) -> pivot_divides_exactly x g.
Proof.
  intros H [w ->]. unfold pivot_divides_exactly.
  rewrite Z.quot_mul by assumption. reflexivity.
Qed.

Lemma normalize_slot_range k basic row nb s :
  normalize_columns k basic row nb ->
  0 <= s < Zlength nb ->
  0 <= Znth s nb 0 < k /\ Znth (Znth s nb 0) row 0 = UINT_MAX.
Proof.
  intros (_ & _ & Hnb & _) Hs.
  apply Hnb, Znth_In_Zlength. exact Hs.
Qed.

Lemma normalize_row_values_length k r a c nb :
  Zlength (normalize_row_values k r a c nb) = Zlength nb + 1.
Proof.
  unfold normalize_row_values.
  now rewrite Zlength_app_cons, Zlength_map.
Qed.

Lemma normalize_row_values_column k r a c nb s :
  0 <= s < Zlength nb ->
  Znth s (normalize_row_values k r a c nb) 0 = Znth (r*k + Znth s nb 0) a 0.
Proof.
  intro Hs. unfold normalize_row_values.
  rewrite app_Znth1 by (rewrite Zlength_map; exact Hs).
  exact (@Znth_map Z Z (fun j => Znth (r*k+j) a 0) nb s 0 0 Hs).
Qed.

Lemma normalize_row_values_constant k r a c nb :
  Znth (Zlength nb) (normalize_row_values k r a c nb) 0 = Znth r c 0.
Proof.
  unfold normalize_row_values.
  rewrite app_Znth2 by (rewrite Zlength_map; lia).
  rewrite Zlength_map, Z.sub_diag. reflexivity.
Qed.

Lemma normalize_prefix_gcd_empty d values : normalize_prefix_gcd d 0 values = d.
Proof. reflexivity. Qed.

Lemma normalize_prefix_gcd_finish d s values :
  0 <= s <= Zlength values ->
  (s = Zlength values \/ normalize_prefix_gcd d s values = 1) ->
  normalize_prefix_gcd d s values = fold_left Z.gcd values d.
Proof.
  intros Hs [->|Ht].
  - unfold normalize_prefix_gcd. now rewrite sublist_self.
  - rewrite Ht. unfold normalize_prefix_gcd in Ht.
    rewrite <- (sublist_self values (Zlength values)) by reflexivity.
    rewrite (sublist_split 0 (Zlength values) s values) by lia.
    rewrite fold_left_app, Ht. symmetry. apply normalize_fold_gcd_one.
Qed.

Lemma normalize_coeff_prefix_empty m k r g a nb :
  Zlength a = m*k -> normalize_coeff_prefix m k r g 0 a nb a.
Proof.
  intro Ha. split; [exact Ha|].
  change (sublist 0 0 nb) with (@nil Z).
  split; [intros p Hp [j [Hj _]]; contradiction|auto].
Qed.

Lemma normalize_result_unit m k r d c a nb :
  normalize_row_gcd k r d c a nb = 1 ->
  Zlength a = m*k -> normalize_result m k r d c a nb d c a.
Proof.
  intros Hg Ha. unfold normalize_result.
  rewrite Hg, !Z.quot_1_r, !replace_Znth_Znth.
  repeat split; try assumption.
  intros. now rewrite Z.quot_1_r.
Qed.

(* Both the constant and each selected coefficient are divisible by the
   same positive numerical factor, with C's signed exact quotient. *)
Lemma normalize_row_gcd_exact k r d c a nb :
  0 < Znth r d 0 ->
  let g := normalize_row_gcd k r d c a nb in
  0 < g /\ pivot_divides_exactly (Znth r d 0) g /\
  pivot_divides_exactly (Znth r c 0) g /\
  (forall j, In j nb -> pivot_divides_exactly (Znth (r*k+j) a 0) g).
Proof.
  intros Hd. cbn zeta. unfold normalize_row_gcd.
  pose proof (normalize_fold_gcd_positive (normalize_row_values k r a c nb)
      (Znth r d 0) Hd) as Hg.
  destruct (normalize_fold_gcd_divides (normalize_row_values k r a c nb)
      (Znth r d 0)) as [Hdiv Hentry].
  rewrite Forall_forall in Hentry.
  split; [exact Hg|]. split.
  - apply normalize_divides_quot; [lia|exact Hdiv].
  - split.
    + apply normalize_divides_quot; [lia|apply Hentry].
      unfold normalize_row_values. apply in_or_app. right. left. reflexivity.
    + intros j Hj. apply normalize_divides_quot; [lia|apply Hentry].
      unfold normalize_row_values. apply in_or_app. left. apply in_map_iff. now exists j.
Qed.

(* Processing one fresh column only replaces that flattened slot. *)
Lemma normalize_coeff_prefix_write m k r g s a nb cur :
  normalize_coeff_prefix m k r g s a nb cur ->
  0 <= s < Zlength nb ->
  0 <= r*k + Znth s nb 0 < m*k ->
  normalize_coeff_prefix m k r g (s+1) a nb
    (replace_Znth (r*k + Znth s nb 0)
       (Z.quot (Znth (r*k + Znth s nb 0) a 0) g) cur).
Proof.
  intros (Hlen & Hdone & Hrest) Hs Hidx.
  set (j0 := Znth s nb 0) in *.
  split; [now rewrite Zlength_replace_Znth|].
  rewrite (sublist_split 0 (s+1) s nb) by lia.
  rewrite (sublist_single 0 s nb) by lia.
  fold j0. split.
  - intros p Hp [j [Hj Heq]].
    destruct (Z.eq_dec p (r*k+j0)) as [->|Hdiff].
    + apply Znth_replace_Znth_Same. lia.
    + rewrite Znth_replace_Znth_Diff by lia.
      apply Hdone; [exact Hp|].
      apply in_app_or in Hj as [Hin|[He|[]]].
      * now exists j.
      * lia.
  - intros p Hp Houtside.
    rewrite Znth_replace_Znth_Diff; try lia.
    + apply Hrest; [exact Hp|].
      intros j Hj. apply Houtside. apply in_or_app. now left.
    + intro Hcontra. apply (Houtside j0); [apply in_or_app; right; now left|lia].
Qed.

(* NoDup ensures the coefficient visited in this iteration is still its
   entry value in the array produced by earlier iterations. *)
Lemma normalize_coeff_prefix_unvisited m k r g s a nb cur :
  NoDup nb -> normalize_coeff_prefix m k r g s a nb cur ->
  0 <= s < Zlength nb ->
  0 <= r*k + Znth s nb 0 < m*k ->
  Znth (r*k+Znth s nb 0) cur 0 = Znth (r*k+Znth s nb 0) a 0.
Proof.
  intros Hnodup (_ & _ & Hrest) Hs Hindex.
  apply Hrest; [exact Hindex|].
  intros j Hin Eq.
  replace j with (Znth s nb 0) in Hin by lia.
  rewrite <- (sublist_self nb (Zlength nb)) in Hnodup by reflexivity.
  rewrite (sublist_split 0 (Zlength nb) s nb) in Hnodup by lia.
  rewrite (sublist_split s (Zlength nb) (s+1) nb) in Hnodup by lia.
  rewrite (sublist_single 0 s nb) in Hnodup by lia.
  simpl in Hnodup.
  apply NoDup_remove_2 in Hnodup.
  apply Hnodup, in_or_app. now left.
Qed.

Lemma normalize_coeff_prefix_zero m k r g s a nb cur :
  normalize_coeff_prefix m k r g s a nb cur ->
  0 <= s < Zlength nb ->
  0 <= r*k + Znth s nb 0 < m*k ->
  g <> 0 ->
  Znth (r*k + Znth s nb 0) a 0 = 0 ->
  Znth (r*k + Znth s nb 0) cur 0 = 0 ->
  normalize_coeff_prefix m k r g (s+1) a nb cur.
Proof.
  intros Hcur Hs Hidx Hg Ha Hzero.
  pose proof (normalize_coeff_prefix_write _ _ _ _ _ _ _ _ Hcur Hs Hidx) as H.
  rewrite Ha, Z.quot_0_l in H by lia.
  replace (replace_Znth (r*k + Znth s nb 0) 0 cur) with cur in H.
  2:{ symmetry. rewrite <- Hzero at 2. apply replace_Znth_Znth. }
  exact H.
Qed.

(* An exact output divides the whole target row, including its zero basic
   columns. The common scale is positive, so the original and normalized
   Q equations have the same solutions. Other rows are framed in the
   definition of normalize_result. *)
Lemma normalize_result_scales m k r d c a basic row nb dn cn an :
  simplex_dimensions_ok m (k-m) -> 0 <= r < m ->
  Zlength d = m -> Zlength c = m ->
  normalize_columns k basic row nb -> normalize_basic_zero k r a basic ->
  0 < Znth r d 0 -> normalize_result m k r d c a nb dn cn an ->
  let g := normalize_row_gcd k r d c a nb in
  0 < g /\ 0 < Znth r dn 0 /\
  Znth r d 0 = Znth r dn 0 * g /\ Znth r c 0 = Znth r cn 0 * g /\
  (forall j, 0 <= j < k -> Znth (r*k+j) a 0 = Znth (r*k+j) an 0 * g).
Proof.
  intros Hdim Hr Hdlen Hclen Hcols Hzeros Hd Hres.
  cbn zeta. unfold normalize_result in Hres. cbn zeta in Hres.
  set (g := normalize_row_gcd k r d c a nb) in *.
  destruct (normalize_row_gcd_exact k r d c a nb Hd)
    as [Hg [HdivD [HdivC HdivA]]].
  fold g in Hg, HdivD, HdivC, HdivA.
  destruct Hres as [-> [-> (Hlen & Hdone & Hrest)]].
  rewrite !Znth_replace_Znth_Same by lia.
  unfold pivot_divides_exactly in *.
  repeat split; try assumption.
  - nia.
  - intros j Hj.
    assert (Hp : 0 <= r*k+j < m*k).
    { replace k with (m+(k-m)) in Hj by lia.
      pose proof (simplex_dimensions_index m (k-m) r j Hdim Hr Hj) as Hindex.
      replace (m+(k-m)) with k in Hindex by lia. exact Hindex. }
    rewrite sublist_self in Hdone, Hrest by reflexivity.
    destruct (in_dec Z.eq_dec j nb) as [Hin|Hnotin].
    + rewrite (Hdone _ Hp) by now exists j.
      apply HdivA; exact Hin.
    + destruct Hcols as (_ & _ & _ & Hcover).
      destruct (Hcover j Hj) as [Hb|Hnb]; [|contradiction].
      unfold normalize_basic_zero in Hzeros.
      rewrite Forall_forall in Hzeros.
      rewrite (Hrest _ Hp) by (intros p Hpin E; apply Hnotin; now replace j with p by lia).
      rewrite (Hzeros j Hb). lia.
Qed.

Lemma normalize_fold_gcd_mul g values d :
  0 <= g ->
  fold_left Z.gcd (map (fun x => x*g) values) (d*g) =
  fold_left Z.gcd values d * g.
Proof.
  revert d. induction values as [|x tail IH]; intros d Hg; simpl.
  - reflexivity.
  - rewrite Z.gcd_mul_mono_r_nonneg by exact Hg. apply IH. exact Hg.
Qed.

Lemma normalize_result_primitive m k r d c a basic row nb dn cn an :
  simplex_dimensions_ok m (k-m) -> 0 <= r < m ->
  Zlength d = m -> Zlength c = m ->
  normalize_columns k basic row nb -> normalize_basic_zero k r a basic ->
  0 < Znth r d 0 -> normalize_result m k r d c a nb dn cn an ->
  normalize_row_gcd k r dn cn an nb = 1.
Proof.
  intros Hd Hr Hdl Hcl Hcols Hzero Hpos Hres.
  destruct (normalize_result_scales m k r d c a basic row nb dn cn an
      Hd Hr Hdl Hcl Hcols Hzero Hpos Hres)
    as (Hg & Hdn & HD & HC & HA).
  set (g := normalize_row_gcd k r d c a nb) in *.
  destruct Hcols as (_ & _ & Hnb & _).
  assert (Hvals : normalize_row_values k r a c nb =
    map (fun x => x*g) (normalize_row_values k r an cn nb)).
  { unfold normalize_row_values. rewrite map_app, map_map. simpl.
    rewrite <- HC. f_equal.
    apply map_ext_in. intros j Hj.
    apply HA. apply Hnb. exact Hj. }
  assert (Hmul : g = normalize_row_gcd k r dn cn an nb * g).
  { unfold g at 1. unfold normalize_row_gcd.
    rewrite Hvals, HD, normalize_fold_gcd_mul by lia. reflexivity. }
  nia.
Qed.
