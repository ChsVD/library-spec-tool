From Coq Require Import ZArith List Lia.
From Coq Require Import QArith.Qcanon QArith.Qreduction setoid_ring.Field.
From SetsClass Require Import SetsClass RelsDomain.
From SimpleC.EE.Applications_human.simplex_find_entering_preserve Require Export simplex_find_entering_preserve_lib.
From SimpleC.EE.Applications_human.simplex_initialize Require Export simplex_initialize_lib.
From SimpleC.EE.Applications_human.simplex_pivot Require Export simplex_pivot_lib.
Import ListNotations.
Local Open Scope Z_scope.

(* A checked row reads only nonbasic values. The arrays may disagree on every
   basic entry: these are exactly the entries changed by sequential commits. *)
Lemma solve_recompute_row_ext : forall ib an ad vn vd wn wd rn rd i cols,
 0 <= cols ->
 (forall j, 0 <= j < cols -> Znth j ib 0 = 0 ->
   Znth j vn 0 = Znth j wn 0 /\ Znth j vd 0 = Znth j wd 0%Z) ->
 simplex_recompute_row ib an ad vn vd rn rd i cols =
 simplex_recompute_row ib an ad wn wd rn rd i cols.
Proof.
 intros ib an ad vn vd wn wd rn rd i cols HC.
 revert cols HC. refine (natlike_ind (fun cols => _) _ _).
 - intros. reflexivity.
 - intros k HK IH HE. replace (Z.succ k) with (k+1) by lia.
   rewrite !simplex_recompute_row_step by lia.
   rewrite IH by (intros; apply HE; lia).
   unfold simplex_recompute_column.
   destruct (simplex_recompute_row ib an ad wn wd rn rd i k) as [[n d]|]; [|reflexivity].
   destruct (Z.eqb (Znth k ib 0%Z) 0%Z) eqn:EB; simpl; [|reflexivity].
   apply Z.eqb_eq in EB. destruct (HE k ltac:(lia) EB) as [HN HD].
   rewrite HN, HD. reflexivity.
Qed.

(* Positive-denominator interpretation of the actual cross-product compare. *)
Lemma solve_fraction_le : forall a b c d,
 0<b -> 0<d ->
 ((simplex_pivot_fraction a b <= simplex_pivot_fraction c d)%Qc <-> a*d<=c*b).
Proof.
 intros a b c d HB HD. unfold simplex_pivot_fraction, Qcle. change ((Qred (QArith_base.Qmake a (Z.to_pos b)) <= Qred (QArith_base.Qmake c (Z.to_pos d)))%Q <-> a*d<=c*b).
 rewrite Qred_le. unfold QArith_base.Qle. simpl.
 rewrite !Z2Pos.id by lia. tauto.
Qed.
Lemma solve_fraction_lt : forall a b c d,
 0<b -> 0<d ->
 ((simplex_pivot_fraction a b < simplex_pivot_fraction c d)%Qc <-> a*d<c*b).
Proof.
 intros a b c d HB HD. unfold simplex_pivot_fraction, Qclt. change ((Qred (QArith_base.Qmake a (Z.to_pos b)) < Qred (QArith_base.Qmake c (Z.to_pos d)))%Q <-> a*d<c*b).
 rewrite Qred_lt. unfold QArith_base.Qlt. simpl.
 rewrite !Z2Pos.id by lia. tauto.
Qed.
Lemma solve_compare_nonnegative : forall a b c d,
 0<b -> 0<d -> 0<=simplex_rat_compare_order a b c d ->
 (simplex_pivot_fraction c d<=simplex_pivot_fraction a b)%Qc.
Proof.
 intros a b c d HB HD HE. apply solve_fraction_le; auto.
 unfold simplex_rat_compare_order in HE.
 destruct (Z.compare_spec (a*d) (c*b)); simpl in HE; lia.
Qed.
Lemma solve_compare_nonpositive : forall a b c d,
 0<b -> 0<d -> simplex_rat_compare_order a b c d<=0 ->
 (simplex_pivot_fraction a b<=simplex_pivot_fraction c d)%Qc.
Proof.
 intros a b c d HB HD HE. apply solve_fraction_le; auto.
 unfold simplex_rat_compare_order in HE.
 destruct (Z.compare_spec (a*d) (c*b)); simpl in HE; lia.
Qed.
Lemma solve_compare_negative : forall a b c d,
 0<b -> 0<d -> simplex_rat_compare_order a b c d<0 ->
 (simplex_pivot_fraction a b<simplex_pivot_fraction c d)%Qc.
Proof.
 intros a b c d HB HD HE. apply solve_fraction_lt; auto.
 unfold simplex_rat_compare_order in HE.
 destruct (Z.compare_spec (a*d) (c*b)); simpl in HE; lia.
Qed.
Lemma solve_compare_positive : forall a b c d,
 0<b -> 0<d -> 0<simplex_rat_compare_order a b c d ->
 (simplex_pivot_fraction c d<simplex_pivot_fraction a b)%Qc.
Proof.
 intros a b c d HB HD HE. apply solve_fraction_lt; auto.
 unfold simplex_rat_compare_order in HE.
 destruct (Z.compare_spec (a*d) (c*b)); simpl in HE; lia.
Qed.

Lemma solve_scan_zero_bounds : forall hl hu vn vd ln ld un ud,
 0<vd -> 0<ld -> 0<ud ->
 simplex_scan_row hl hu vn vd ln ld un ud=Some 0 ->
 (hl<>0 -> (simplex_pivot_fraction ln ld<=simplex_pivot_fraction vn vd)%Qc) /\
 (hu<>0 -> (simplex_pivot_fraction vn vd<=simplex_pivot_fraction un ud)%Qc).
Proof.
 intros hl hu vn vd ln ld un ud HD HL HU HE. unfold simplex_scan_row in HE.
 destruct (Z.eqb hl 0 || Z.eqb (simplex_rat_compare_flag vn vd ln ld) 1)%bool; [|discriminate].
 destruct (Z.eqb hu 0 || Z.eqb (simplex_rat_compare_flag vn vd un ud) 1)%bool; [|discriminate].
 destruct (negb (Z.eqb hu 0) && Z.ltb 0 (simplex_rat_compare_order vn vd un ud))%bool eqn:EU; [discriminate|].
 destruct (negb (Z.eqb hl 0) && Z.ltb (simplex_rat_compare_order vn vd ln ld) 0)%bool eqn:EL; [discriminate|].
 split; intros HB.
 - rewrite (proj2 (Z.eqb_neq hl 0) HB) in EL. cbn in EL. apply Z.ltb_ge in EL.
   apply solve_compare_nonnegative; auto.
 - rewrite (proj2 (Z.eqb_neq hu 0) HB) in EU. cbn in EU. apply Z.ltb_ge in EU.
   apply solve_compare_nonpositive; auto.
Qed.
Lemma solve_scan_row_sign : forall hl hu vn vd ln ld un ud direction,
 simplex_scan_row hl hu vn vd ln ld un ud=Some direction ->
 direction=0 \/ direction=1 \/ direction= -1.
Proof.
 intros. unfold simplex_scan_row in H.
 destruct (_ || _)%bool; [|discriminate]. destruct (_ || _)%bool; [|discriminate].
 destruct (_ && _)%bool; [inversion H; auto|]. destruct (_ && _)%bool; inversion H; auto.
Qed.
Lemma solve_scan_row_lower : forall hl hu vn vd ln ld un ud,
 0<vd -> 0<ld -> simplex_scan_row hl hu vn vd ln ld un ud=Some 1 ->
 hl<>0 /\ (simplex_pivot_fraction vn vd<simplex_pivot_fraction ln ld)%Qc.
Proof.
 intros hl hu vn vd ln ld un ud HD HL HE. unfold simplex_scan_row in HE.
 destruct (_ || _)%bool; [|discriminate]. destruct (_ || _)%bool; [|discriminate].
 destruct (negb (Z.eqb hu 0) && Z.ltb 0 (simplex_rat_compare_order vn vd un ud))%bool; [discriminate|].
 destruct (negb (Z.eqb hl 0) && Z.ltb (simplex_rat_compare_order vn vd ln ld) 0)%bool eqn:EL; [|discriminate].
 apply Bool.andb_true_iff in EL. destruct EL as [HB HC]. apply Bool.negb_true_iff in HB. apply Z.eqb_neq in HB.
 apply Z.ltb_lt in HC. split; [exact HB|]. apply solve_compare_negative; auto.
Qed.
Lemma solve_scan_row_upper : forall hl hu vn vd ln ld un ud,
 0<vd -> 0<ud -> simplex_scan_row hl hu vn vd ln ld un ud=Some (-1) ->
 hu<>0 /\ (simplex_pivot_fraction un ud<simplex_pivot_fraction vn vd)%Qc.
Proof.
 intros hl hu vn vd ln ld un ud HD HU HE. unfold simplex_scan_row in HE.
 destruct (_ || _)%bool; [|discriminate]. destruct (_ || _)%bool; [|discriminate].
 destruct (negb (Z.eqb hu 0) && Z.ltb 0 (simplex_rat_compare_order vn vd un ud))%bool eqn:EU.
 - apply Bool.andb_true_iff in EU. destruct EU as [HB HC]. apply Bool.negb_true_iff in HB. apply Z.eqb_neq in HB.
   apply Z.ltb_lt in HC. split; [exact HB|]. apply solve_compare_positive; auto.
 - destruct (negb (Z.eqb hl 0) && Z.ltb (simplex_rat_compare_order vn vd ln ld) 0)%bool; discriminate.
Qed.
Lemma solve_violation_selected_row : forall b hl hu vn vd ln ld un ud cols rows r direction,
 simplex_find_violation_spec b hl hu vn vd ln ld un ud cols rows 1 r direction -> 0<=r ->
 0<=r<rows /\ (direction=1 \/ direction= -1) /\
 simplex_scan_rows b hl hu vn vd ln ld un ud r=Some direction.
Proof.
 intros b hl hu vn vd ln ld un ud cols rows r direction HS HR.
 unfold simplex_find_violation_spec, simplex_find_violation_result in HS.
 destruct HS as [[_ [HOK [best HC]]]|[HF _]]; [|discriminate].
 apply simplex_scan_candidate_facts in HC.
 destruct HC as [[HE _]|[HROW [HNE [HD _]]]]; [lia|].
 specialize (HOK r HROW). unfold simplex_scan_check in HOK.
 unfold simplex_scan_direction in HD,HNE.
 destruct (simplex_scan_rows b hl hu vn vd ln ld un ud r) as [d|] eqn:EO; [|discriminate].
 subst direction. unfold simplex_scan_rows in EO.
 pose proof (solve_scan_row_sign _ _ _ _ _ _ _ _ _ EO) as HSG.
 split; [exact HROW|]. split; [tauto|reflexivity].
Qed.

Lemma solve_no_violation_rows : forall b hl hu vn vd ln ld un ud cols rows r direction,
 simplex_find_violation_spec b hl hu vn vd ln ld un ud cols rows 1 r direction -> r<0 ->
 forall i, 0<=i<rows -> simplex_scan_rows b hl hu vn vd ln ld un ud i=Some 0.
Proof.
 intros b hl hu vn vd ln ld un ud cols rows r direction HS HR i HI.
 unfold simplex_find_violation_spec, simplex_find_violation_result in HS.
 destruct HS as [[_ [HOK [best HC]]]|[HF _]]; [|discriminate].
 apply simplex_scan_candidate_facts in HC.
 destruct HC as [[_ [_ [_ HZERO]]]|[HROW _]]; [|lia].
 specialize (HOK i HI). specialize (HZERO i HI).
 unfold simplex_scan_check in HOK. unfold simplex_scan_direction in HZERO.
 destruct (simplex_scan_rows b hl hu vn vd ln ld un ud i) as [d|]; [|discriminate].
 subst d. reflexivity.
Qed.

Lemma solve_no_entering_columns : forall ib an hl hu vn vd ln ld un ud direction cols e,
 simplex_find_entering_spec ib an hl hu vn vd ln ld un ud direction cols 1 e -> e<0 ->
 forall j, 0<=j<cols -> simplex_enter_observations ib an hl hu vn vd ln ld un ud direction j=Some false.
Proof.
 intros ib an hl hu vn vd ln ld un ud direction cols e HS HE.
 unfold simplex_find_entering_spec, simplex_enter_result in HS.
 destruct HS as [[_ [_ HSKIP]]|[k [HK [_ [[_ [HEQ _]]|[HF _]]]]]]; auto; lia.
Qed.
Lemma solve_linear_le : forall xs f g,
 (forall j, In j xs -> (f j<=g j)%Qc) ->
 (simplex_pivot_linear xs f<=simplex_pivot_linear xs g)%Qc.
Proof.
 induction xs as [|x xs IH]; intros f g HE.
 - apply Qcle_refl.
 - change ((f x+simplex_pivot_linear xs f <= g x+simplex_pivot_linear xs g)%Qc).
   apply Qcplus_le_compat.
   + apply HE. left. reflexivity.
   + apply IH. intros j HJ. apply HE. right. exact HJ.
Qed.

(* A successful skipped nonbasic/nonzero column was blocked by the selected
   bound. Arithmetic failure never enters this lemma's Some-false premise. *)
Lemma solve_enter_blocked : forall a direction hl hu vn vd ln ld un ud,
 a<>0 -> simplex_enter_column 0 a direction hl hu vn vd ln ld un ud=Some false ->
 let increase := ((Z.ltb 0 a && Z.ltb 0 direction) ||
                  (Z.ltb a 0 && Z.ltb direction 0%Z))%bool in
 (increase=true /\ hu<>0 /\ 0<=simplex_rat_compare_order vn vd un ud) \/
 (increase=false /\ hl<>0 /\ simplex_rat_compare_order vn vd ln ld<=0).
Proof.
 intros a direction hl hu vn vd ln ld un ud HA HE.
 unfold simplex_enter_column in HE. rewrite Z.eqb_refl in HE.
 rewrite (proj2 (Z.eqb_neq a 0%Z) HA) in HE. cbn [negb orb] in HE.
 cbn zeta. destruct ((Z.ltb 0 a && Z.ltb 0 direction) ||
                  (Z.ltb a 0 && Z.ltb direction 0%Z))%bool eqn:EI.
 - destruct (Z.eqb hu 0%Z) eqn:HU; [discriminate|].
   destruct (Z.eqb (simplex_rat_compare_flag vn vd un ud) 1); [|discriminate].
   inversion HE as [EO]. apply Z.ltb_ge in EO.
   left. split; [reflexivity|]. split; [apply Z.eqb_neq; exact HU|exact EO].
 - destruct (Z.eqb hl 0%Z) eqn:HL; [discriminate|].
   destruct (Z.eqb (simplex_rat_compare_flag vn vd ln ld) 1); [|discriminate].
   inversion HE as [EO]. apply Z.ltb_ge in EO.
   right. split; [reflexivity|]. split; [apply Z.eqb_neq; exact HL|exact EO].
Qed.

Lemma solve_mult_nonnegative : forall a x y:Qc,
 (0<=a)%Qc -> (x<=y)%Qc -> (a*x<=a*y)%Qc.
Proof. intros. rewrite !(Qcmult_comm a). apply Qcmult_le_compat_r; auto. Qed.
Lemma solve_mult_nonpositive : forall a x y:Qc,
 (a<=0)%Qc -> (x<=y)%Qc -> (a*y<=a*x)%Qc.
Proof.
 intros a x y HA HE.
 assert (HN:(0<= -a)%Qc).
 { pose proof (Qcopp_le_compat a 0 HA) as H. replace (-0)%Qc with 0%Qc in H by ring. exact H. }
 pose proof (solve_mult_nonnegative (-a)%Qc x y HN HE) as H.
 apply Qcopp_le_compat in H.
 replace (-(-a*y))%Qc with (a*y)%Qc in H by ring.
 replace (-(-a*x))%Qc with (a*x)%Qc in H by ring. exact H.
Qed.

Lemma solve_blocked_assignment : forall a direction hl hu vn vd ln ld un ud (z:Qc),
 a<>0 -> 0<vd -> 0<ld -> 0<ud ->
 simplex_enter_column 0 a direction hl hu vn vd ln ld un ud=Some false ->
 (hl<>0 -> (simplex_pivot_fraction ln ld<=z)%Qc) ->
 (hu<>0 -> (z<=simplex_pivot_fraction un ud)%Qc) ->
 let increase := ((Z.ltb 0 a && Z.ltb 0 direction) ||
                  (Z.ltb a 0 && Z.ltb direction 0%Z))%bool in
 if increase then (z<=simplex_pivot_fraction vn vd)%Qc
 else (simplex_pivot_fraction vn vd<=z)%Qc.
Proof.
 intros a direction hl hu vn vd ln ld un ud z HA HD HL HU HE HLOW HUP.
 destruct (solve_enter_blocked a direction hl hu vn vd ln ld un ud HA HE)
 as [[HI [HB HC]]|[HI [HB HC]]]; cbn zeta in *; rewrite HI.
 - exact (Qcle_trans z (simplex_pivot_fraction un ud) (simplex_pivot_fraction vn vd)
     (HUP HB) (solve_compare_nonnegative vn vd un ud HD HU HC)).
 - exact (Qcle_trans (simplex_pivot_fraction vn vd) (simplex_pivot_fraction ln ld) z
     (solve_compare_nonpositive vn vd ln ld HD HL HC) (HLOW HB)).
Qed.

(* Direction-specific monotonicity of every blocked term at any legal
   assignment. No equality with a bound or search success on later fields is
   presumed; the premise is the actual successful skip observation. *)
Lemma solve_blocked_term_plus : forall a ad hl hu vn vd ln ld un ud (z:Qc),
 a<>0 -> 0<ad -> 0<vd -> 0<ld -> 0<ud ->
 simplex_enter_column 0 a 1 hl hu vn vd ln ld un ud=Some false ->
 (hl<>0 -> (simplex_pivot_fraction ln ld<=z)%Qc) ->
 (hu<>0 -> (z<=simplex_pivot_fraction un ud)%Qc) ->
 (simplex_pivot_fraction a ad*z <=
  simplex_pivot_fraction a ad*simplex_pivot_fraction vn vd)%Qc.
Proof.
 intros a ad hl hu vn vd ln ld un ud z HA HAD HVD HLD HUD HE HL HU.
 pose proof (solve_blocked_assignment a 1 hl hu vn vd ln ld un ud z
   HA HVD HLD HUD HE HL HU) as HB.
 cbn in HB. rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_r in HB. cbn in HB. destruct (Z.ltb 0 a) eqn:HS; cbn in HB.
 - apply Z.ltb_lt in HS. apply solve_mult_nonnegative; [|exact HB].
   change (simplex_pivot_fraction 0 1<=simplex_pivot_fraction a ad)%Qc.
   apply solve_fraction_le; lia.
 - apply Z.ltb_ge in HS. apply solve_mult_nonpositive; [|exact HB].
   change (simplex_pivot_fraction a ad<=simplex_pivot_fraction 0 1)%Qc.
   apply solve_fraction_le; lia.
Qed.
Lemma solve_blocked_term_minus : forall a ad hl hu vn vd ln ld un ud (z:Qc),
 a<>0 -> 0<ad -> 0<vd -> 0<ld -> 0<ud ->
 simplex_enter_column 0 a (-1) hl hu vn vd ln ld un ud=Some false ->
 (hl<>0 -> (simplex_pivot_fraction ln ld<=z)%Qc) ->
 (hu<>0 -> (z<=simplex_pivot_fraction un ud)%Qc) ->
 (simplex_pivot_fraction a ad*simplex_pivot_fraction vn vd <=
  simplex_pivot_fraction a ad*z)%Qc.
Proof.
 intros a ad hl hu vn vd ln ld un ud z HA HAD HVD HLD HUD HE HL HU.
 pose proof (solve_blocked_assignment a (-1) hl hu vn vd ln ld un ud z
   HA HVD HLD HUD HE HL HU) as HB.
 cbn in HB. rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_r in HB. cbn in HB. destruct (Z.ltb a 0%Z) eqn:HS; cbn in HB.
 - apply Z.ltb_lt in HS. apply solve_mult_nonpositive; [|exact HB].
   change (simplex_pivot_fraction a ad<=simplex_pivot_fraction 0 1)%Qc.
   apply solve_fraction_le; lia.
 - apply Z.ltb_ge in HS. apply solve_mult_nonnegative; [|exact HB].
   change (simplex_pivot_fraction 0 1<=simplex_pivot_fraction a ad)%Qc.
   apply solve_fraction_le; lia.
Qed.

(* Bounds are mathematical constraints on a rational assignment. All four
   arrays here describe active columns; this predicate owns no C memory. *)
Definition simplex_solve_bounds (hl hu ln ld un ud:list Z) (cols:Z) (z:Z->Qc) : Prop :=
 forall j, 0<=j<cols ->
   (Znth j hl 0<>0 -> (simplex_pivot_fraction (Znth j ln 0%Z) (Znth j ld 0%Z)<=z j)%Qc) /\
   (Znth j hu 0<>0 -> (z j<=simplex_pivot_fraction (Znth j un 0%Z) (Znth j ud 0%Z))%Qc).

Theorem solve_no_violation_all_bounds : forall b ib hl hu vn vd ln ld un ud rows cols r direction,
 (forall j, 0<=j<cols -> 0<Znth j vd 0 /\ 0<Znth j ld 0 /\ 0<Znth j ud 0) ->
 (forall j, 0<=j<cols -> Znth j ib 0<>0 -> exists i, 0<=i<rows /\ Znth i b 0=j) ->
 (forall j, 0<=j<cols -> Znth j ib 0=0 ->
   (Znth j hl 0<>0 -> (simplex_pivot_fraction (Znth j ln 0%Z) (Znth j ld 0%Z)<=simplex_pivot_fraction (Znth j vn 0%Z) (Znth j vd 0%Z))%Qc) /\
   (Znth j hu 0<>0 -> (simplex_pivot_fraction (Znth j vn 0%Z) (Znth j vd 0%Z)<=simplex_pivot_fraction (Znth j un 0%Z) (Znth j ud 0%Z))%Qc)) ->
 simplex_find_violation_spec b hl hu vn vd ln ld un ud cols rows 1 r direction -> r<0 ->
 simplex_solve_bounds hl hu ln ld un ud cols
   (fun j=>simplex_pivot_fraction (Znth j vn 0) (Znth j vd 0)).
Proof.
 intros b ib hl hu vn vd ln ld un ud rows cols r direction HD HB HNB HS HR j HJ.
 destruct (Z.eq_dec (Znth j ib 0) 0) as [HI|HI]; [apply HNB; auto|].
 destruct (HB j HJ HI) as [i [HROW HE]].
 pose proof (solve_no_violation_rows b hl hu vn vd ln ld un ud cols rows r direction HS HR i HROW) as HZERO.
 unfold simplex_scan_rows in HZERO. rewrite HE in HZERO.
 destruct (HD j HJ) as [HV [HL HU]].
 exact (solve_scan_zero_bounds (Znth j hl 0) (Znth j hu 0) (Znth j vn 0) (Znth j vd 0)
   (Znth j ln 0) (Znth j ld 0) (Znth j un 0) (Znth j ud 0) HV HL HU HZERO).
Qed.

(* Original input uses a nine-int physical row stride. Its orientation is
   A0+sum Ax<=0; the auxiliary variable equals that expression, with upper 0. *)
Definition simplex_solve_input_row (a:list Z) (inputs i:Z) (x:Z->Qc) : Qc :=
 (simplex_pivot_fraction (Znth (i*9)%Z a 0%Z) 1%Z +
 simplex_pivot_linear (Zrange 0%Z inputs) (fun j=>
  simplex_pivot_fraction (Znth (i*9+j+1)%Z a 0%Z) 1%Z*x j))%Qc.
Definition simplex_solve_constraints (a:list Z) (rows inputs:Z) (x:Z->Qc) : Prop :=
 forall i, 0<=i<rows -> (simplex_solve_input_row a inputs i x<=0)%Qc.
Definition simplex_solve_source (a:list Z) (rows inputs:Z) (z:Z->Qc) : Prop :=
 forall i, 0<=i<rows ->
 z (inputs+i)%Z=simplex_solve_input_row a inputs i z /\ (z (inputs+i)%Z<=0)%Qc.

Lemma solve_input_row_ext : forall a inputs i x y,
 (forall j, 0<=j<inputs -> x j=y j) ->
 simplex_solve_input_row a inputs i x=simplex_solve_input_row a inputs i y.
Proof.
 intros. unfold simplex_solve_input_row. f_equal. apply simplex_pivot_linear_ext.
 intros j HJ. apply In_Zrange in HJ. rewrite H by auto. reflexivity.
Qed.

Theorem solve_source_extension : forall a rows inputs x,
 0<=inputs -> simplex_solve_constraints a rows inputs x ->
 exists z:Z->Qc, (forall j, 0<=j<inputs -> z j=x j) /\
 simplex_solve_source a rows inputs z.
Proof.
 intros a rows inputs x HN HX.
 exists (fun j=>if j <? inputs then x j else simplex_solve_input_row a inputs (j-inputs) x).
 assert (HP:forall j, 0<=j<inputs ->
   (if j <? inputs then x j else simplex_solve_input_row a inputs (j-inputs) x)=x j).
 { intros j HJ. rewrite (proj2 (Z.ltb_lt j inputs) ltac:(lia)). reflexivity. }
 split; [exact HP|]. intros i HI.
 rewrite (proj2 (Z.ltb_ge (inputs+i) inputs) ltac:(lia)).
 replace (inputs+i-inputs) with i by lia. split; [|apply HX; auto].
 apply solve_input_row_ext. intros j HJ. symmetry. apply HP; auto.
Qed.
Theorem solve_source_projection : forall a rows inputs z,
 simplex_solve_source a rows inputs z -> simplex_solve_constraints a rows inputs z.
Proof. intros a rows inputs z HS i HI. destruct (HS i HI) as [HE HB]. rewrite <-HE. exact HB. Qed.



Theorem solve_no_entering_row_conflict_plus : forall ib an ad hl hu vn vd ln ld un ud cols b (rhs:Qc),
 0<=cols -> 0<=b<cols ->
 (forall j, 0<=j<cols -> 0<Znth j ad 0 /\ 0<Znth j vd 0 /\
   0<Znth j ld 0 /\ 0<Znth j ud 0 /\ (Znth j ib 0<>0 -> Znth j an 0=0)) ->
 (forall j, 0<=j<cols ->
   simplex_enter_observations ib an hl hu vn vd ln ld un ud 1 j=Some false) ->
 simplex_pivot_fraction (Znth b vn 0%Z) (Znth b vd 0%Z) =
 (rhs+simplex_pivot_linear (Zrange 0%Z cols) (fun j=>
   simplex_pivot_fraction (Znth j an 0%Z) (Znth j ad 0%Z)*
   simplex_pivot_fraction (Znth j vn 0%Z) (Znth j vd 0%Z)))%Qc ->
 Znth b hl 0<>0 ->
 (simplex_pivot_fraction (Znth b vn 0%Z) (Znth b vd 0%Z)<
  simplex_pivot_fraction (Znth b ln 0%Z) (Znth b ld 0%Z))%Qc ->
 forall z:Z->Qc, simplex_solve_bounds hl hu ln ld un ud cols z ->
 z b=(rhs+simplex_pivot_linear (Zrange 0%Z cols) (fun j=>
   simplex_pivot_fraction (Znth j an 0%Z) (Znth j ad 0%Z)*z j))%Qc -> False.
Proof.
 intros ib an ad hl hu vn vd ln ld un ud cols b rhs HC HB HD HS HE HHL HVIOL z HZ HROW.
 assert (HSUM:(simplex_pivot_linear (Zrange 0%Z cols) (fun j=>
   simplex_pivot_fraction (Znth j an 0%Z) (Znth j ad 0%Z)*z j) <=
   simplex_pivot_linear (Zrange 0%Z cols) (fun j=>
   simplex_pivot_fraction (Znth j an 0%Z) (Znth j ad 0%Z)*
   simplex_pivot_fraction (Znth j vn 0%Z) (Znth j vd 0%Z)))%Qc).
 { apply solve_linear_le. intros j HJ. apply In_Zrange in HJ.
   destruct (HD j HJ) as [HA [HV [HL [HU HZERO]]]].
   destruct (Z.eq_dec (Znth j an 0%Z) 0%Z) as [EA|EA].
   - rewrite EA, pivot_fraction_zero__success_math by auto. rewrite !Qcmult_0_l. apply Qcle_refl.
   - assert (HIB:Znth j ib 0=0) by (destruct (Z.eq_dec (Znth j ib 0%Z) 0%Z); auto; exfalso; apply EA; apply HZERO; auto).
     pose proof (HS j HJ) as HO. unfold simplex_enter_observations in HO. rewrite HIB in HO.
     destruct (HZ j HJ) as [HLOW HUP].
     exact (solve_blocked_term_plus (Znth j an 0%Z) (Znth j ad 0%Z) (Znth j hl 0%Z)
       (Znth j hu 0%Z) (Znth j vn 0%Z) (Znth j vd 0%Z) (Znth j ln 0%Z) (Znth j ld 0%Z)
       (Znth j un 0%Z) (Znth j ud 0%Z) (z j) EA HA HV HL HU HO HLOW HUP). }
 assert (HLE:(z b<=simplex_pivot_fraction (Znth b vn 0%Z) (Znth b vd 0%Z))%Qc).
 { rewrite HROW, HE. apply Qcplus_le_compat; [apply Qcle_refl|exact HSUM]. }
 destruct (HZ b HB) as [HLOW _].
 apply (Qclt_not_le _ _ HVIOL). eapply Qcle_trans; [apply HLOW; exact HHL|exact HLE].
Qed.

Theorem solve_no_entering_row_conflict_minus : forall ib an ad hl hu vn vd ln ld un ud cols b (rhs:Qc),
 0<=cols -> 0<=b<cols ->
 (forall j, 0<=j<cols -> 0<Znth j ad 0 /\ 0<Znth j vd 0 /\
   0<Znth j ld 0 /\ 0<Znth j ud 0 /\ (Znth j ib 0<>0 -> Znth j an 0=0)) ->
 (forall j, 0<=j<cols ->
   simplex_enter_observations ib an hl hu vn vd ln ld un ud (-1) j=Some false) ->
 simplex_pivot_fraction (Znth b vn 0%Z) (Znth b vd 0%Z) =
 (rhs+simplex_pivot_linear (Zrange 0%Z cols) (fun j=>
   simplex_pivot_fraction (Znth j an 0%Z) (Znth j ad 0%Z)*
   simplex_pivot_fraction (Znth j vn 0%Z) (Znth j vd 0%Z)))%Qc ->
 Znth b hu 0<>0 ->
 (simplex_pivot_fraction (Znth b un 0%Z) (Znth b ud 0%Z)<
  simplex_pivot_fraction (Znth b vn 0%Z) (Znth b vd 0%Z))%Qc ->
 forall z:Z->Qc, simplex_solve_bounds hl hu ln ld un ud cols z ->
 z b=(rhs+simplex_pivot_linear (Zrange 0%Z cols) (fun j=>
   simplex_pivot_fraction (Znth j an 0%Z) (Znth j ad 0%Z)*z j))%Qc -> False.
Proof.
 intros ib an ad hl hu vn vd ln ld un ud cols b rhs HC HB HD HS HE HHU HVIOL z HZ HROW.
 assert (HSUM:(simplex_pivot_linear (Zrange 0%Z cols) (fun j=>
   simplex_pivot_fraction (Znth j an 0%Z) (Znth j ad 0%Z)*
   simplex_pivot_fraction (Znth j vn 0%Z) (Znth j vd 0%Z)) <=
   simplex_pivot_linear (Zrange 0%Z cols) (fun j=>
   simplex_pivot_fraction (Znth j an 0%Z) (Znth j ad 0%Z)*z j))%Qc).
 { apply solve_linear_le. intros j HJ. apply In_Zrange in HJ.
   destruct (HD j HJ) as [HA [HV [HL [HU HZERO]]]].
   destruct (Z.eq_dec (Znth j an 0%Z) 0%Z) as [EA|EA].
   - rewrite EA, pivot_fraction_zero__success_math by auto. rewrite !Qcmult_0_l. apply Qcle_refl.
   - assert (HIB:Znth j ib 0=0) by (destruct (Z.eq_dec (Znth j ib 0%Z) 0%Z); auto; exfalso; apply EA; apply HZERO; auto).
     pose proof (HS j HJ) as HO. unfold simplex_enter_observations in HO. rewrite HIB in HO.
     destruct (HZ j HJ) as [HLOW HUP].
     exact (solve_blocked_term_minus (Znth j an 0%Z) (Znth j ad 0%Z) (Znth j hl 0%Z)
       (Znth j hu 0%Z) (Znth j vn 0%Z) (Znth j vd 0%Z) (Znth j ln 0%Z) (Znth j ld 0%Z)
       (Znth j un 0%Z) (Znth j ud 0%Z) (z j) EA HA HV HL HU HO HLOW HUP). }
 assert (HLE:(simplex_pivot_fraction (Znth b vn 0%Z) (Znth b vd 0%Z)<=z b)%Qc).
 { rewrite HROW, HE. apply Qcplus_le_compat; [apply Qcle_refl|exact HSUM]. }
 destruct (HZ b HB) as [_ HUP].
 apply (Qclt_not_le _ _ HVIOL). eapply Qcle_trans; [exact HLE|apply HUP; exact HHU].
Qed.

Lemma solve_linear_singleton : forall k f,
 simplex_pivot_linear [k] f = f k.
Proof. intros. change ((f k+0)%Qc=f k). ring. Qed.
Lemma solve_linear_app : forall xs ys f,
 simplex_pivot_linear (xs++ys) f =
 (simplex_pivot_linear xs f + simplex_pivot_linear ys f)%Qc.
Proof. induction xs; intros; simpl [simplex_pivot_linear] in *; [ring|].
 rewrite IHxs. ring. Qed.

(* Canonicality is proved from the actual normalized checked operations,
   never added to the already-published callee contract. *)
Lemma solve_recompute_column_coprime : forall ib an ad vn vd i j n d u v,
 0<d -> Z.gcd (Z.abs n) d=1 ->
 0<Znth (i*24+j)%Z ad 0 -> 0<Znth j vd 0 ->
 simplex_recompute_column ib an ad vn vd i (Some(n,d)) j=Some(u,v) ->
 0<v /\ Z.gcd (Z.abs u) v=1.
Proof.
 intros ib an ad vn vd i j n d u v HD HG HA HV HE.
 unfold simplex_recompute_column in HE.
 destruct (negb (Z.eqb (Znth j ib 0%Z) 0%Z) || Z.eqb (Znth (i*24+j)%Z an 0%Z) 0%Z)%bool.
 - inversion HE; subst. auto.
 - destruct (Z.eqb (simplex_rat_mul_flag _ _ _ _) 1) eqn:EM; [|discriminate].
   destruct (pivot_mul_quotients__success_math (Znth (i*24+j)%Z an 0%Z) (Znth (i*24+j)%Z ad 0%Z) (Znth j vn 0%Z) (Znth j vd 0%Z) HA HV) as [HT _].
   set (p := Z.quot (Znth (i*24+j)%Z an 0 * Znth j vn 0%Z) (Z.gcd (Z.abs (Znth (i*24+j)%Z an 0 * Znth j vn 0%Z)) (Znth (i*24+j)%Z ad 0 * Znth j vd 0%Z))) in *.
   set (t := Z.quot (Znth (i*24+j)%Z ad 0 * Znth j vd 0%Z) (Z.gcd (Z.abs (Znth (i*24+j)%Z an 0 * Znth j vn 0%Z)) (Znth (i*24+j)%Z ad 0 * Znth j vd 0%Z))) in *.
   destruct (Z.eqb (simplex_rat_add_flag _ _ _ _) 1) eqn:EA; [|discriminate].
   inversion HE; subst. split.
   + apply (proj1 (pivot_add_quotients__success_math n d p t HD HT)).
   + apply simplex_rat_reduce_coprime. nia.
Qed.

Lemma solve_recompute_row_coprime : forall ib an ad vn vd rn rd i cols,
 0<=cols -> 0<Znth i rd 0 -> Z.gcd (Z.abs (Znth i rn 0%Z)) (Znth i rd 0%Z)=1 ->
 (forall j, 0<=j<cols -> 0<Znth (i*24+j)%Z ad 0 /\ 0<Znth j vd 0%Z) ->
 forall u v, simplex_recompute_row ib an ad vn vd rn rd i cols=Some(u,v) ->
 0<v /\ Z.gcd (Z.abs u) v=1.
Proof.
 intros ib an ad vn vd rn rd i cols HC HD HG.
 revert cols HC. refine (natlike_ind (fun cols=>_) _ _).
 - intros HV u v HE. cbn [simplex_recompute_row] in HE. inversion HE; subst; auto.
 - intros k HK IH HV u v HE. replace (Z.succ k) with (k+1) in HE by lia.
   rewrite simplex_recompute_row_step in HE by lia.
   destruct (simplex_recompute_row ib an ad vn vd rn rd i k) as [[n d]|] eqn:ER; [|discriminate].
   destruct (IH ltac:(intros; apply HV; lia) n d eq_refl) as [HD' HG'].
   destruct (HV k ltac:(lia)) as [HA HB].
   exact (solve_recompute_column_coprime ib an ad vn vd i k n d u v HD' HG' HA HB HE).
Qed.

Lemma solve_recompute_column_value : forall ib an ad vn vd i j n d u v,
 0<d -> 0<Znth (i*24+j)%Z ad 0 -> 0<Znth j vd 0 ->
 simplex_recompute_column ib an ad vn vd i (Some(n,d)) j=Some(u,v) ->
 0<v /\ simplex_pivot_fraction u v =
 (simplex_pivot_fraction n d +
   (if Z.eqb (Znth j ib 0%Z) 0 then
    simplex_pivot_fraction (Znth (i*24+j)%Z an 0%Z) (Znth (i*24+j)%Z ad 0%Z) *
    simplex_pivot_fraction (Znth j vn 0%Z) (Znth j vd 0%Z) else 0%Qc))%Qc.
Proof.
 intros ib an ad vn vd i j n d u v HD HA HV HE.
 unfold simplex_recompute_column in HE.
 destruct (Z.eqb (Znth j ib 0%Z) 0%Z) eqn:EB; simpl in HE.
 - destruct (Z.eqb (Znth (i*24+j)%Z an 0%Z) 0%Z) eqn:EZ; simpl in HE.
   + inversion HE; subst. apply Z.eqb_eq in EZ. rewrite EZ.
     rewrite pivot_fraction_zero__success_math by auto. split; [auto|ring].
   + destruct (Z.eqb (simplex_rat_mul_flag _ _ _ _) 1) eqn:EM; [|discriminate].
     destruct (pivot_mul_quotients__success_math (Znth (i*24+j)%Z an 0%Z) (Znth (i*24+j)%Z ad 0%Z) (Znth j vn 0%Z) (Znth j vd 0%Z) HA HV) as [HT HMV].
     set (p := Z.quot (Znth (i*24+j)%Z an 0 * Znth j vn 0%Z) (Z.gcd (Z.abs (Znth (i*24+j)%Z an 0 * Znth j vn 0%Z)) (Znth (i*24+j)%Z ad 0 * Znth j vd 0%Z))) in *.
   set (t := Z.quot (Znth (i*24+j)%Z ad 0 * Znth j vd 0%Z) (Z.gcd (Z.abs (Znth (i*24+j)%Z an 0 * Znth j vn 0%Z)) (Znth (i*24+j)%Z ad 0 * Znth j vd 0%Z))) in *.
   destruct (Z.eqb (simplex_rat_add_flag _ _ _ _) 1) eqn:EA; [|discriminate].
     inversion HE; subst. destruct (pivot_add_quotients__success_math n d p t HD HT) as [HQ HQV].
     split; [exact HQ|]. rewrite HQV, HMV. reflexivity.
 - inversion HE; subst. split; [auto|ring].
Qed.

(* The checked row is the ordinary rational linear form, over precisely the
   nonbasic columns. This connects exact machine checks with tableau algebra. *)
Theorem solve_recompute_row_value : forall ib an ad vn vd rn rd i cols,
 0<=cols -> 0<Znth i rd 0 ->
 (forall j, 0<=j<cols -> 0<Znth (i*24+j)%Z ad 0 /\ 0<Znth j vd 0%Z) ->
 forall u v, simplex_recompute_row ib an ad vn vd rn rd i cols=Some(u,v) ->
 0<v /\ simplex_pivot_fraction u v =
 (simplex_pivot_fraction (Znth i rn 0%Z) (Znth i rd 0%Z) +
 simplex_pivot_linear (Zrange 0%Z cols) (fun j =>
   if Z.eqb (Znth j ib 0%Z) 0 then
    simplex_pivot_fraction (Znth (i*24+j)%Z an 0%Z) (Znth (i*24+j)%Z ad 0%Z) *
    simplex_pivot_fraction (Znth j vn 0%Z) (Znth j vd 0%Z) else 0%Qc))%Qc.
Proof.
 intros ib an ad vn vd rn rd i cols HC HD.
 revert cols HC. refine (natlike_ind (fun cols=>_) _ _).
 - intros HV u v HE. cbn [simplex_recompute_row] in HE. inversion HE; subst.
   split; [auto|]. change (simplex_pivot_fraction (Znth i rn 0%Z) (Znth i rd 0%Z) = (simplex_pivot_fraction (Znth i rn 0%Z) (Znth i rd 0%Z) + 0%Qc)%Qc). ring.
 - intros k HK IH HV u v HE. replace (Z.succ k) with (k+1) in HE |- * by lia.
   rewrite simplex_recompute_row_step in HE by lia.
   destruct (simplex_recompute_row ib an ad vn vd rn rd i k) as [[n d]|] eqn:ER; [|discriminate].
   destruct (IH ltac:(intros; apply HV; lia) n d eq_refl) as [HD' HROW].
   destruct (HV k ltac:(lia)) as [HA HB].
   destruct (solve_recompute_column_value ib an ad vn vd i k n d u v HD' HA HB HE) as [HV' HEQ].
   split; [exact HV'|]. rewrite HEQ, HROW.
   rewrite simplex_scan_range_snoc, solve_linear_app by lia.
   rewrite solve_linear_singleton. ring.
Qed.

(* Exact reconstruction, including failure: q=0 preserves all completed
   commits. When q=1, each final basic entry is the checked row evaluated at
   the entrance nonbasic snapshot. Distinct basis is needed only to preserve
   earlier commits. No physical padding or inactive initialization is used. *)
Theorem solve_recompute_reconstruction : forall ib an ad rn rd b vn vd rows cols,
 0 <= rows -> 0 <= cols -> Zlength vn = cols -> Zlength vd = cols ->
 (forall i, 0 <= i < rows ->
   0 <= Znth i b 0 < cols /\ Znth (Znth i b 0%Z) ib 0 <> 0%Z) ->
 (forall i k, 0 <= i < rows -> 0 <= k < rows -> i <> k ->
   Znth i b 0 <> Znth k b 0%Z) ->
 forall q on od,
 simplex_recompute_compute ib an ad rn rd b vn vd rows cols = (q,(on,od)) ->
 (q=0 \/ q=1) /\ Zlength on=cols /\ Zlength od=cols /\
 (forall j, 0<=j<cols -> Znth j ib 0=0 ->
    Znth j on 0=Znth j vn 0 /\ Znth j od 0=Znth j vd 0%Z) /\
 (q=1 -> forall i, 0<=i<rows ->
   simplex_recompute_row ib an ad vn vd rn rd i cols =
   Some (Znth (Znth i b 0%Z) on 0, Znth (Znth i b 0%Z) od 0%Z)).
Proof.
 intros ib an ad rn rd b vn vd rows cols HR HC HN HD.
 revert rows HR. refine (natlike_ind (fun rows => _) _ _).
 - intros HB HND q on od HE. cbn [simplex_recompute_compute] in HE.
   inversion HE; subst. repeat split; auto; try lia.
 - intros k HK IH HB HND q on od HE.
   replace (Z.succ k) with (k+1) in HE by lia.
   rewrite simplex_recompute_compute_step in HE by lia.
   destruct (simplex_recompute_compute ib an ad rn rd b vn vd k cols)
     as [cq [cn cd]] eqn:EC.
   destruct (IH ltac:(intros; apply HB; lia)
     ltac:(intros; apply HND; lia) cq cn cd eq_refl)
     as [HQ [HLN [HLD [HNB HROWS]]]].
   destruct HQ as [EQ|EQ]; subst cq.
   + cbn [simplex_recompute_commit] in HE. inversion HE; subst.
     split; [auto|]. split; [exact HLN|]. split; [exact HLD|].
     split; [exact HNB|]. discriminate.
   + unfold simplex_recompute_commit in HE. cbn [Z.eqb] in HE.
     destruct (simplex_recompute_row ib an ad cn cd rn rd k cols)
       as [[u v]|] eqn:ER.
     * inversion HE; subst on od q.
       destruct (HB k ltac:(lia)) as [HBK HIB].
       split; [auto|]. rewrite !Zlength_replace_Znth.
       split; [exact HLN|]. split; [exact HLD|]. split.
       -- intros j HJ HJIB.
          assert (HNE:Znth k b 0 <> j) by (intro E; rewrite E in HIB; contradiction).
          rewrite !Znth_replace_Znth_Diff by lia. apply HNB; auto.
       -- intros _ i HI. destruct (Z.eq_dec i k) as [E|E].
          ++ subst i. rewrite !Znth_replace_Znth_Same by lia.
             rewrite (solve_recompute_row_ext ib an ad vn vd cn cd rn rd k cols HC).
             ** exact ER.
             ** intros j HJ HJIB. destruct (HNB j HJ HJIB); auto.
          ++ assert (HBI:0<=Znth i b 0<cols) by (apply HB; lia).
             assert (HNE:Znth k b 0<>Znth i b 0%Z) by (apply HND; lia).
             rewrite !Znth_replace_Znth_Diff by lia.
             apply HROWS; lia.
     * inversion HE; subst on od q. split; [auto|]. split; [exact HLN|].
       split; [exact HLD|]. split; [exact HNB|]. discriminate.
Qed.

(* The reconstruction theorem also holds at the final values themselves,
   rather than merely at the entrance nonbasic snapshot. *)
Corollary solve_recompute_all_rows : forall ib an ad rn rd b vn vd rows cols on od,
 0<=rows -> 0<=cols -> Zlength vn=cols -> Zlength vd=cols ->
 (forall i, 0<=i<rows -> 0<=Znth i b 0<cols /\ Znth (Znth i b 0%Z) ib 0<>0) ->
 (forall i k, 0<=i<rows -> 0<=k<rows -> i<>k -> Znth i b 0<>Znth k b 0%Z) ->
 simplex_recompute_compute ib an ad rn rd b vn vd rows cols=(1,(on,od)) ->
 forall i, 0<=i<rows ->
 simplex_recompute_row ib an ad on od rn rd i cols =
 Some (Znth (Znth i b 0%Z) on 0, Znth (Znth i b 0%Z) od 0%Z).
Proof.
 intros ib an ad rn rd b vn vd rows cols on od HR HC HN HD HB HND HE i HI.
 destruct (solve_recompute_reconstruction ib an ad rn rd b vn vd rows cols
   HR HC HN HD HB HND 1 on od HE) as [_ [_ [_ [HNB HROWS]]]].
 rewrite (solve_recompute_row_ext ib an ad on od vn vd rn rd i cols HC HNB).
 apply HROWS; auto.
Qed.

(* Removing the basic-column filter is justified by actual zero coefficients,
   not by assigning arbitrary values to basic variables. *)
Lemma solve_recompute_unfilter : forall ib an ad vn vd i cols,
 0<=cols ->
 (forall j, 0<=j<cols -> 0<Znth (i*24+j) ad 0%Z) ->
 (forall j, 0<=j<cols -> Znth j ib 0<>0 -> Znth (i*24+j) an 0=0) ->
 simplex_pivot_linear (Zrange 0 cols) (fun j =>
   if Z.eqb (Znth j ib 0%Z) 0 then
    (simplex_pivot_fraction (Znth (i*24+j)%Z an 0%Z) (Znth (i*24+j)%Z ad 0%Z) *
    simplex_pivot_fraction (Znth j vn 0%Z) (Znth j vd 0%Z))%Qc else 0%Qc) =
 simplex_pivot_linear (Zrange 0 cols) (fun j =>
    (simplex_pivot_fraction (Znth (i*24+j)%Z an 0%Z) (Znth (i*24+j)%Z ad 0%Z) *
    simplex_pivot_fraction (Znth j vn 0%Z) (Znth j vd 0%Z))%Qc).
Proof.
 intros ib an ad vn vd i cols HC HD HZERO.
 apply simplex_pivot_linear_ext. intros j HJ.
 apply In_Zrange in HJ.
 destruct (Z.eqb (Znth j ib 0%Z) 0%Z) eqn:EB; [reflexivity|].
 apply Z.eqb_neq in EB. rewrite (HZERO j HJ EB).
 rewrite pivot_fraction_zero__success_math by (apply HD; auto). ring.
Qed.

Theorem solve_recompute_final_equations : forall ib an ad rn rd b vn vd rows cols on od,
 0<=rows -> 0<=cols -> Zlength vn=cols -> Zlength vd=cols ->
 (forall i, 0<=i<rows -> 0<=Znth i b 0<cols /\ Znth (Znth i b 0%Z) ib 0<>0) ->
 (forall i k, 0<=i<rows -> 0<=k<rows -> i<>k -> Znth i b 0<>Znth k b 0%Z) ->
 (forall i, 0<=i<rows -> 0<Znth i rd 0 /\
    forall j, 0<=j<cols -> 0<Znth (i*24+j) ad 0 /\
      (Znth j ib 0<>0 -> Znth (i*24+j) an 0=0)) ->
 (forall j, 0<=j<cols -> 0<Znth j od 0%Z) ->
 simplex_recompute_compute ib an ad rn rd b vn vd rows cols=(1,(on,od)) ->
 forall i, 0<=i<rows ->
 simplex_pivot_fraction (Znth (Znth i b 0%Z) on 0%Z) (Znth (Znth i b 0%Z) od 0%Z) =
 (simplex_pivot_fraction (Znth i rn 0%Z) (Znth i rd 0%Z) +
 simplex_pivot_linear (Zrange 0%Z cols) (fun j =>
    simplex_pivot_fraction (Znth (i*24+j)%Z an 0%Z) (Znth (i*24+j)%Z ad 0%Z) *
    simplex_pivot_fraction (Znth j on 0%Z) (Znth j od 0%Z)))%Qc.
Proof.
 intros ib an ad rn rd b vn vd rows cols on od HR HC HN HD HB HND HA HV HE i HI.
 pose proof (solve_recompute_all_rows ib an ad rn rd b vn vd rows cols on od
    HR HC HN HD HB HND HE i HI) as HROW.
 destruct (HA i HI) as [HRD HM].
 destruct (solve_recompute_row_value ib an ad on od rn rd i cols HC HRD
    ltac:(intros j HJ; split; [apply HM|apply HV]; auto)
    _ _ HROW) as [_ HVALUE].
 rewrite HVALUE. f_equal. apply solve_recompute_unfilter; auto.
 - intros j HJ. apply HM; auto.
 - intros j HJ. apply HM; auto.
Qed.

Lemma solve_linear_zero_suffix : forall inputs cols (f:Z->Qc),
 0<=inputs<=cols -> (forall j, inputs<=j<cols -> f j=0%Qc) ->
 simplex_pivot_linear (Zrange 0 cols) f=simplex_pivot_linear (Zrange 0%Z inputs) f.
Proof.
 intros inputs cols f HB HZERO.
 rewrite (range_split__failure_rhs 0 inputs cols ltac:(lia)). rewrite solve_linear_app.
 assert (HZ:simplex_pivot_linear (Zrange inputs cols) f=0%Qc).
 { rewrite <-(simplex_pivot_linear_zero (Zrange inputs cols)).
   apply simplex_pivot_linear_ext. intros j HJ. apply In_Zrange in HJ. apply HZERO; auto. }
 rewrite HZ. ring.
Qed.

(* Initialization-to-source bridge. The hypotheses are precisely the public
   initialized field formulas, stated at mathematical values. The theorem
   proves the all-assignment equivalence; it is not assumed as provenance. *)
Theorem solve_initial_source_equiv : forall a n d b hl hu ln ld un ud rows inputs,
 0<=rows -> 0<=inputs ->
 (forall i, 0<=i<rows -> Znth i b 0=inputs+i /\
   simplex_pivot_value n d i=simplex_pivot_fraction (Znth (i*9) a 0) 1 /\
   forall j, 0<=j<inputs+rows ->
    simplex_pivot_value n d (16+i*24+j)=
    (if j <? inputs then simplex_pivot_fraction (Znth (i*9+j+1) a 0) 1 else 0%Qc)) ->
 (forall j, 0<=j<inputs+rows -> Znth j hl 0=0 /\
   Znth j hu 0=(if j <? inputs then 0 else 1) /\
   simplex_pivot_fraction (Znth j un 0) (Znth j ud 0)=0%Qc) ->
 forall z:Z->Qc,
 (simplex_pivot_equations n d b rows (inputs+rows) z /\
  simplex_solve_bounds hl hu ln ld un ud (inputs+rows) z) <->
 simplex_solve_source a rows inputs z.
Proof.
 intros a n d b hl hu ln ld un ud rows inputs HR HN HT HB z.
 assert (HF:forall i,0<=i<rows ->
   (simplex_pivot_value n d i+
    simplex_pivot_linear (Zrange 0%Z (inputs+rows)%Z)
      (fun j=>simplex_pivot_value n d (16+i*24+j)%Z*z j))%Qc =
   simplex_solve_input_row a inputs i z).
 { intros i HI. destruct (HT i HI) as [HBI [HRHS HA]]. rewrite HRHS.
   unfold simplex_solve_input_row. f_equal.
   rewrite (solve_linear_zero_suffix inputs (inputs+rows)
     (fun j=>(simplex_pivot_value n d (16+i*24+j)%Z*z j)%Qc) ltac:(lia)).
   - apply simplex_pivot_linear_ext. intros j HJ. apply In_Zrange in HJ.
     rewrite HA by lia. rewrite (proj2 (Z.ltb_lt j inputs) ltac:(lia)). reflexivity.
   - intros j HJ. rewrite HA by lia.
     rewrite (proj2 (Z.ltb_ge j inputs) ltac:(lia)). ring. }
 split.
 - intros [HE HBOUND] i HI. destruct (HT i HI) as [HBI _].
   specialize (HE i HI). unfold simplex_pivot_equations in HE.
   rewrite HBI, HF in HE by exact HI. split; [exact HE|].
   destruct (HB (inputs+i) ltac:(lia)) as [_ [HH HU]].
   destruct (HBOUND (inputs+i) ltac:(lia)) as [_ HUP].
   rewrite HU in HUP. apply HUP. rewrite HH.
   rewrite (proj2 (Z.ltb_ge (inputs+i) inputs) ltac:(lia)). discriminate.
 - intros HS. split.
   + intros i HI. destruct (HT i HI) as [HBI _].
     rewrite HBI, HF by exact HI. apply HS; auto.
   + intros j HJ. destruct (HB j HJ) as [HL [HH HU]].
     split; [rewrite HL; tauto|]. intros HHNZ. rewrite HU.
     assert (HJN:inputs<=j).
     { destruct (Z.ltb j inputs) eqn:E; [rewrite HH in HHNZ; contradiction|]. apply Z.ltb_ge; exact E. }
     destruct (HS (j-inputs) ltac:(lia)) as [_ HUP].
     replace (inputs+(j-inputs)) with j in HUP by lia. exact HUP.
Qed.

Lemma solve_pivot_zero_basic_columns : forall n d on od b rows cols r e,
 0<=e<cols -> 0<=r<rows -> Zlength b=rows ->
 (forall k, 0<=k<rows -> 0<=Znth k b 0<cols /\ Znth k b 0<>e) ->
 (forall k, 0<=k<rows -> k<>r -> Znth k b 0<>Znth r b 0) ->
 (forall i k, 0<=i<rows -> 0<=k<rows ->
    simplex_pivot_value n d (16+i*24+Znth k b 0)=0%Qc) ->
 simplex_pivot_closed n d on od rows cols r e (Znth r b 0) ->
 forall i k, 0<=i<rows -> 0<=k<rows ->
 simplex_pivot_value on od (16+i*24+Znth k (replace_Znth r e b) 0)=0%Qc.
Proof.
 intros n d on od b rows cols r e HE HR HBL HB HND HZERO HC i k HI HK.
 destruct HC as [HP [HRHS [HROW [HOTH HCOEF]]]].
 destruct (Z.eq_dec k r) as [EK|EK].
 - subst k. rewrite Znth_replace_Znth_Same by lia.
   destruct (Z.eq_dec i r) as [EI|EI].
   + subst i. rewrite HROW by exact HE.
     destruct (Z.eq_dec e e); [reflexivity|contradiction].
   + rewrite HCOEF by auto.
     destruct (Z.eq_dec e e); [reflexivity|contradiction].
 - rewrite Znth_replace_Znth_Diff by lia.
   destruct (HB k HK) as [HBR HBE].
   assert (HBNE:Znth k b 0<>Znth r b 0) by (apply HND; auto).
   assert (HNEW:simplex_pivot_value on od (16+r*24+Znth k b 0)=0%Qc).
   { rewrite HROW by auto.
     destruct (Z.eq_dec (Znth k b 0) e); [contradiction|].
     destruct (Z.eq_dec (Znth k b 0) (Znth r b 0)); [contradiction|].
     rewrite HZERO by auto. field. exact HP. }
   destruct (Z.eq_dec i r) as [EI|EI]; [subst; exact HNEW|].
   rewrite HCOEF by auto. destruct (Z.eq_dec (Znth k b 0) e); [contradiction|].
   rewrite HZERO, HNEW by auto. ring.
Qed.

Theorem solve_recompute_normal_fractions : forall ib an ad rn rd b vn vd rows cols,
 0<=rows -> 0<=cols -> Zlength vn=cols -> Zlength vd=cols ->
 (forall j, 0<=j<cols -> 0<Znth j vd 0 /\ Z.gcd (Z.abs (Znth j vn 0)) (Znth j vd 0)=1) ->
 (forall i, 0<=i<rows -> 0<=Znth i b 0<cols /\
   0<Znth i rd 0 /\ Z.gcd (Z.abs (Znth i rn 0)) (Znth i rd 0)=1 /\
   forall j, 0<=j<cols -> 0<Znth (i*24+j) ad 0) ->
 forall q on od,
 simplex_recompute_compute ib an ad rn rd b vn vd rows cols=(q,(on,od)) ->
 (q=0 \/ q=1) /\ Zlength on=cols /\ Zlength od=cols /\
 forall j, 0<=j<cols -> 0<Znth j od 0 /\ Z.gcd (Z.abs (Znth j on 0)) (Znth j od 0)=1.
Proof.
 intros ib an ad rn rd b vn vd rows cols HR HC HN HD HNORM.
 revert rows HR. refine (natlike_ind (fun rows=>_) _ _).
 - intros HB q on od HE. cbn [simplex_recompute_compute] in HE.
   inversion HE; subst on od q. split; [auto|]. split; [exact HN|]. split; [exact HD|exact HNORM].
 - intros k HK IH HB q on od HE.
   replace (Z.succ k) with (k+1) in HE by lia. rewrite simplex_recompute_compute_step in HE by lia.
   destruct (simplex_recompute_compute ib an ad rn rd b vn vd k cols) as [cq [cn cd]] eqn:EC.
   destruct (IH ltac:(intros; apply HB; lia) cq cn cd eq_refl) as [HQ [HLN [HLD HCF]]].
   destruct HQ as [EQ|EQ]; subst cq; cbn [simplex_recompute_commit] in HE.
   + inversion HE; subst on od q. split; [auto|]. split; [exact HLN|]. split; [exact HLD|exact HCF].
   + destruct (simplex_recompute_row ib an ad cn cd rn rd k cols) as [[u v]|] eqn:ER.
     * inversion HE; subst on od q. destruct (HB k ltac:(lia)) as [HBR [HRD [HRG HA]]].
       destruct (solve_recompute_row_coprime ib an ad cn cd rn rd k cols HC HRD HRG
         ltac:(intros j HJ; split; [apply HA|apply HCF]; auto) u v ER) as [HV HG].
       split; [auto|]. rewrite !Zlength_replace_Znth.
       split; [exact HLN|]. split; [exact HLD|]. intros j HJ.
       destruct (Z.eq_dec (Znth k b 0) j) as [E|E].
       -- subst j. rewrite !Znth_replace_Znth_Same by lia. auto.
       -- rewrite !Znth_replace_Znth_Diff by lia. apply HCF; auto.
     * inversion HE; subst on od q. split; [auto|]. split; [exact HLN|]. split; [exact HLD|exact HCF].
Qed.

Lemma solve_nodup_indexed : forall b,
 NoDup b <-> (forall i k, 0<=i<Zlength b -> 0<=k<Zlength b ->
   i<>k -> Znth i b 0<>Znth k b 0).
Proof.
 intro b. rewrite (NoDup_nth b 0). split.
 - intros H i k HI HK HNE HE. unfold Znth in HE.
   assert (EH:Z.to_nat i=Z.to_nat k).
   { apply H; rewrite Zlength_correct in *; lia||exact HE. }
   lia.
 - intros H i k HI HK HE.
   destruct (Nat.eq_dec i k) as [E|E]; [exact E|]. exfalso.
   apply (H (Z.of_nat i) (Z.of_nat k)); try (rewrite Zlength_correct; lia).
   + lia.
   + unfold Znth. rewrite !Nat2Z.id. exact HE.
Qed.

Lemma solve_pivot_basis_properties : forall b rows cols r e,
 Zlength b=rows -> 0<=r<rows -> 0<=e<cols -> NoDup b ->
 (forall k, 0<=k<rows -> 0<=Znth k b 0<cols /\ Znth k b 0<>e) ->
 Zlength (replace_Znth r e b)=rows /\ NoDup (replace_Znth r e b) /\
 forall k, 0<=k<rows -> 0<=Znth k (replace_Znth r e b) 0<cols.
Proof.
 intros b rows cols r e HL HR HE HND HB.
 split; [rewrite Zlength_replace_Znth; auto|]. split.
 - apply solve_nodup_indexed. rewrite Zlength_replace_Znth, HL.
   intros i k HI HK HIK. destruct (Z.eq_dec r i) as [EI|EI]; destruct (Z.eq_dec r k) as [EK|EK].
   + subst. contradiction.
   + subst i. rewrite Znth_replace_Znth_Same by lia.
     rewrite Znth_replace_Znth_Diff by lia. destruct (HB k HK). congruence.
   + subst k. rewrite Znth_replace_Znth_Same by lia.
     rewrite Znth_replace_Znth_Diff by lia. destruct (HB i HI). congruence.
   + rewrite !Znth_replace_Znth_Diff by lia.
     apply (proj1 (solve_nodup_indexed b) HND); lia.
 - intros k HK. destruct (Z.eq_dec r k) as [E|E].
   + subst k. rewrite Znth_replace_Znth_Same by lia. exact HE.
   + rewrite Znth_replace_Znth_Diff by lia. apply HB; auto.
Qed.

Lemma solve_pivot_marks_at : forall ib cols leaving e j,
 Zlength ib=cols -> 0<=leaving<cols -> 0<=e<cols -> 0<=j<cols -> leaving<>e ->
 Znth j (replace_Znth e 1 (replace_Znth leaving 0 ib)) 0 =
 if Z.eq_dec j e then 1 else if Z.eq_dec j leaving then 0 else Znth j ib 0.
Proof.
 intros ib cols leaving e j HL HB HE HJ HNE.
 destruct (Z.eq_dec j e) as [E|E].
 - subst j. rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth; lia). reflexivity.
 - rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
   destruct (Z.eq_dec j leaving) as [F|F].
   + subst j. rewrite Znth_replace_Znth_Same by lia. reflexivity.
   + rewrite Znth_replace_Znth_Diff by lia. reflexivity.
Qed.

Lemma solve_pivot_mark_consistency : forall b ib rows cols r e,
 Zlength b=rows -> Zlength ib=cols -> 0<=r<rows -> 0<=e<cols -> NoDup b ->
 (forall k,0<=k<rows -> 0<=Znth k b 0<cols /\ Znth (Znth k b 0) ib 0=1) ->
 (forall j,0<=j<cols -> 0<=Znth j ib 0<=1 /\
    (Znth j ib 0=1 <-> exists k,0<=k<rows /\ Znth k b 0=j)) ->
 Znth e ib 0=0 ->
 (forall k,0<=k<rows ->
   Znth (Znth k (replace_Znth r e b) 0)
     (replace_Znth e 1 (replace_Znth (Znth r b 0) 0 ib)) 0=1) /\
 (forall j,0<=j<cols ->
   0<=Znth j (replace_Znth e 1 (replace_Znth (Znth r b 0) 0 ib)) 0<=1 /\
   (Znth j (replace_Znth e 1 (replace_Znth (Znth r b 0) 0 ib)) 0=1 <->
     exists k,0<=k<rows /\ Znth k (replace_Znth r e b) 0=j)).
Proof.
 intros b ib rows cols r e HBL HIL HR HE HND HB HIB HENT.
 destruct (HB r HR) as [HLR HMR].
 assert (HBE:Znth r b 0<>e) by (intro E; rewrite E,HENT in HMR; discriminate).
 assert (HNOE:forall k,0<=k<rows -> Znth k b 0<>e).
 { intros k HK E. destruct (HB k HK) as [_ HM]. rewrite E,HENT in HM; discriminate. }
 assert (HUNIQ:forall k,0<=k<rows -> k<>r -> Znth k b 0<>Znth r b 0).
 { intros. apply (proj1 (solve_nodup_indexed b) HND); lia. }
 split.
 - intros k HK. destruct (Z.eq_dec r k) as [E|E].
   + subst k. rewrite Znth_replace_Znth_Same by lia.
     rewrite (solve_pivot_marks_at ib cols) by auto. destruct (Z.eq_dec e e); congruence.
   + rewrite (Znth_replace_Znth_Diff 0 b r k e) by lia.
     destruct (HB k HK) as [HKR HKM]. rewrite (solve_pivot_marks_at ib cols) by auto.
     destruct (Z.eq_dec (Znth k b 0) e); [exfalso; apply (HNOE k HK); auto|].
     destruct (Z.eq_dec (Znth k b 0) (Znth r b 0)); [exfalso; apply (HUNIQ k HK); auto|exact HKM].
 - intros j HJ. rewrite (solve_pivot_marks_at ib cols) by auto.
   destruct (Z.eq_dec j e) as [E|E].
   + subst j. split; [lia|]. split; intros.
     * exists r. split; [exact HR|]. rewrite Znth_replace_Znth_Same by lia. reflexivity.
     * reflexivity.
   + destruct (Z.eq_dec j (Znth r b 0)) as [F|F].
     * subst j. split; [lia|]. split; [discriminate|]. intros [k [HK HVAL]].
       destruct (Z.eq_dec r k) as [G|G].
       -- subst k. rewrite Znth_replace_Znth_Same in HVAL by lia. congruence.
       -- rewrite Znth_replace_Znth_Diff in HVAL by lia. exfalso. apply (HUNIQ k HK); auto.
     * destruct (HIB j HJ) as [HJ01 HJE]. split; [exact HJ01|]. rewrite HJE. split.
       -- intros [k [HK HVAL]]. exists k. split; [exact HK|].
          assert (HNE:r<>k) by (intro G; subst k; congruence).
          rewrite Znth_replace_Znth_Diff by lia. exact HVAL.
       -- intros [k [HK HVAL]]. exists k. split; [exact HK|].
          destruct (Z.eq_dec r k) as [G|G].
          ++ subst k. rewrite Znth_replace_Znth_Same in HVAL by lia. congruence.
          ++ rewrite Znth_replace_Znth_Diff in HVAL by lia. exact HVAL.
Qed.

Lemma solve_leaving_repair_bounds : forall ib hl hu ln ld un ud cols leaving e direction (value:Z->Qc),
 Zlength ib=cols -> 0<=leaving<cols -> 0<=e<cols -> leaving<>e ->
 (direction=1 \/ direction= -1) ->
 (direction=1 -> Znth leaving hl 0<>0) ->
 (direction= -1 -> Znth leaving hu 0<>0) ->
 (forall j,0<=j<cols -> Znth j hl 0<>0 -> Znth j hu 0<>0 ->
   (simplex_pivot_fraction (Znth j ln 0%Z) (Znth j ld 0%Z)<=
    simplex_pivot_fraction (Znth j un 0%Z) (Znth j ud 0%Z))%Qc) ->
 (forall j,0<=j<cols -> Znth j ib 0=0 ->
   (Znth j hl 0<>0 -> (simplex_pivot_fraction (Znth j ln 0%Z) (Znth j ld 0%Z)<=value j)%Qc) /\
   (Znth j hu 0<>0 -> (value j<=simplex_pivot_fraction (Znth j un 0%Z) (Znth j ud 0%Z))%Qc)) ->
 forall j,0<=j<cols ->
 Znth j (replace_Znth e 1 (replace_Znth leaving 0 ib)) 0=0 ->
 let v:=if Z.eq_dec j leaving then
   (if Z.ltb 0 direction then simplex_pivot_fraction (Znth leaving ln 0) (Znth leaving ld 0)
    else simplex_pivot_fraction (Znth leaving un 0) (Znth leaving ud 0)) else value j in
 (Znth j hl 0<>0 -> (simplex_pivot_fraction (Znth j ln 0%Z) (Znth j ld 0%Z)<=v)%Qc) /\
 (Znth j hu 0<>0 -> (v<=simplex_pivot_fraction (Znth j un 0%Z) (Znth j ud 0%Z))%Qc).
Proof.
 intros ib hl hu ln ld un ud cols leaving e direction value HIL HB HE HNE HD HLOW HUP HCOMP HNB j HJ HM.
 rewrite (solve_pivot_marks_at ib cols) in HM by auto.
 destruct (Z.eq_dec j e) as [E|E]; [discriminate|].
 cbn zeta. destruct (Z.eq_dec j leaving) as [F|F].
 - subst j. destruct HD as [D|D]; subst direction; cbn [Z.ltb].
   + split; intros; [apply Qcle_refl|apply HCOMP; auto].
   + split; intros; [apply HCOMP; auto|apply Qcle_refl].
 - apply HNB; auto.
Qed.

(* Mutable active snapshot. N/D are Pivot's 400 logical slots (separate
   physical rhs/a fields); B/IB and VN/VD are active arrays. Immutable bounds,
   rows/inputs/vars and caller-framed tails are parameters of the computation.
   No logical filler asserts a physical initialization state. *)
Definition simplex_solve_snapshot :=
 (list Z*(list Z*(list Z*(list Z*(list Z*list Z)))))%type.
Definition simplex_solve_pack (n d b ib vn vd:list Z) : simplex_solve_snapshot :=
 (n,(d,(b,(ib,(vn,vd))))).
Definition simplex_solve_row (n:list Z) (r cols:Z) :=
 map (fun j=>Znth (16+r*24+j) n 0) (Zrange 0 cols).
Definition simplex_solve_rhs (n:list Z) (rows:Z) := sublist 0 rows n.
Definition simplex_solve_matrix (default:Z) (n:list Z) (rows cols:Z) :=
 sublist 16 (16+rows*24) (simplex_pivot_pad default rows cols n).

(* One attempted iteration. Tag2 means continue; -1/0/1 are actual terminal
   return codes. Searches precede the budget check even when L=0. The saved
   leaving index is taken before Pivot; rejection retains its exact prefix. *)
Definition simplex_solve_iteration (hl hu ln ld un ud:list Z) (rows cols limit count:Z)
 (s:simplex_solve_snapshot) : Z*simplex_solve_snapshot :=
 let '(n,(d,(b,(ib,(vn,vd))))) := s in
 let '(q,(_, (r,direction))) := simplex_scan_compute (fun i=>Znth i b 0)
   (simplex_scan_rows b hl hu vn vd ln ld un ud) cols rows in
 if Z.eqb q 1 then
   if Z.ltb r 0 then (0,s) else
   let '(qe,e) := simplex_enter_compute
     (simplex_enter_observations ib (simplex_solve_row n r cols) hl hu vn vd ln ld un ud direction) cols in
   if Z.eqb qe 1 then
     if Z.ltb e 0 then (1,s) else
     if Z.leb limit count then (-1,s) else
     let leaving:=Znth r b 0 in
     let '(qp,(on,od)) := simplex_pivot_compute n d rows cols r e leaving in
     let nb:=simplex_pivot_basis b r e qp in
     let nib:=simplex_pivot_marks ib leaving e qp in
     if Z.eqb qp 1 then
       let cvn:=replace_Znth leaving (if Z.ltb 0 direction then Znth leaving ln 0 else Znth leaving un 0) vn in
       let cvd:=replace_Znth leaving (if Z.ltb 0 direction then Znth leaving ld 0 else Znth leaving ud 0) vd in
       let '(qr,(ovn,ovd)) := simplex_recompute_compute nib
         (simplex_solve_matrix 0 on rows cols) (simplex_solve_matrix 1 od rows cols)
         (simplex_solve_rhs on rows) (simplex_solve_rhs od rows) nb cvn cvd rows cols in
       (if Z.eqb qr 1 then 2 else -1, simplex_solve_pack on od nb nib ovn ovd)
     else (-1,simplex_solve_pack on od nb nib vn vd)
   else (-1,s)
 else (-1,s).
Definition simplex_solve_tick (hl hu ln ld un ud:list Z) (rows cols limit:Z)
 (acc:Z*simplex_solve_snapshot) (count:Z) :=
 let '(q,s):=acc in if Z.eqb q 2 then
   simplex_solve_iteration hl hu ln ld un ud rows cols limit count s else acc.
Definition simplex_solve_prefix (hl hu ln ld un ud:list Z) (rows cols limit count:Z)
 (s:simplex_solve_snapshot) :=
 fold_left (simplex_solve_tick hl hu ln ld un ud rows cols limit)
 (Zrange 0 count) (2,s).
Definition simplex_solve_compute (hl hu ln ld un ud:list Z) (rows cols limit:Z)
 (s:simplex_solve_snapshot) :=
 if Z.ltb limit 0 then (-1,s) else
 simplex_solve_prefix hl hu ln ld un ud rows cols limit (limit+1) s.
Definition simplex_solve_result (hl hu ln ld un ud:list Z) (rows cols limit:Z)
 (n d b ib vn vd:list Z) (q:Z) (on od ob oib ovn ovd:list Z) : Prop :=
 simplex_solve_compute hl hu ln ld un ud rows cols limit (simplex_solve_pack n d b ib vn vd)=
 (q,simplex_solve_pack on od ob oib ovn ovd).
Definition simplex_solve_progress (hl hu ln ld un ud:list Z) (rows cols limit count:Z)
 (n d b ib vn vd cn cd cb cib cvn cvd:list Z) : Prop :=
 simplex_solve_prefix hl hu ln ld un ud rows cols limit count (simplex_solve_pack n d b ib vn vd)=
 (2,simplex_solve_pack cn cd cb cib cvn cvd).
Definition simplex_solve_witness (a:list Z) (rows inputs:Z) (vn vd:list Z) : Prop :=
 simplex_solve_constraints a rows inputs (fun j=>simplex_pivot_fraction (Znth j vn 0) (Znth j vd 0)).
Definition simplex_solve_unsat (a:list Z) (rows inputs:Z) : Prop :=
 forall x:Z->Qc, ~simplex_solve_constraints a rows inputs x.

Lemma solve_prefix_step : forall hl hu ln ld un ud rows cols limit count s,
 0<=count -> simplex_solve_prefix hl hu ln ld un ud rows cols limit (count+1) s=
 simplex_solve_tick hl hu ln ld un ud rows cols limit
   (simplex_solve_prefix hl hu ln ld un ud rows cols limit count s) count.
Proof. intros. unfold simplex_solve_prefix. rewrite simplex_scan_range_snoc by auto.
 rewrite fold_left_app. reflexivity. Qed.
Lemma solve_terminal_tick : forall hl hu ln ld un ud rows cols limit q s k,
 q<>2 -> simplex_solve_tick hl hu ln ld un ud rows cols limit (q,s) k=(q,s).
Proof. intros. unfold simplex_solve_tick. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.
Lemma solve_terminal_suffix : forall hl hu ln ld un ud rows cols limit q s ks,
 q<>2 -> fold_left (simplex_solve_tick hl hu ln ld un ud rows cols limit) ks (q,s)=(q,s).
Proof. intros. apply simplex_pivot_fold_fixed. intros. apply solve_terminal_tick; auto. Qed.
Theorem solve_terminal_complete : forall hl hu ln ld un ud rows cols limit count s q sf,
 0<=limit -> 0<=count<=limit -> q<>2 ->
 simplex_solve_tick hl hu ln ld un ud rows cols limit
   (simplex_solve_prefix hl hu ln ld un ud rows cols limit count s) count=(q,sf) ->
 simplex_solve_compute hl hu ln ld un ud rows cols limit s=(q,sf).
Proof.
 intros hl hu ln ld un ud rows cols limit count s q sf HL HC HQ HE.
 unfold simplex_solve_compute. rewrite (proj2 (Z.ltb_ge limit 0) HL).
 unfold simplex_solve_prefix.
 rewrite (range_split__failure_rhs 0 (count+1) (limit+1) ltac:(lia)). rewrite fold_left_app.
 change (fold_left (simplex_solve_tick hl hu ln ld un ud rows cols limit)
   (Zrange (count+1) (limit+1))
   (simplex_solve_prefix hl hu ln ld un ud rows cols limit (count+1) s)=(q,sf)).
 rewrite solve_prefix_step by lia. rewrite HE. apply solve_terminal_suffix; auto.
Qed.

(* Reduced positive-denominator internal fractions, including the actual
   signed-int32 representation domain. This is legality of the represented
   rational, not an assumption that checked operations cannot overflow. *)
Definition simplex_solve_rat (n d:Z) : Prop :=
 -2147483647<=n<=2147483647 /\ 1<=d<=2147483647 /\ Z.gcd (Z.abs n) d=1.
(* Normal mathematical tableau. Machine-readable scalar/list shape bounds
   are also expanded in the C contract. Source equivalence always refers to
   the fixed entrance A; neither A nor a witness is selected at the output. *)
Definition simplex_solve_normal (a hl hu ln ld un ud:list Z) (rows inputs:Z)
 (s:simplex_solve_snapshot) : Prop :=
 let '(n,(d,(b,(ib,(vn,vd))))) :=s in
 let cols:=inputs+rows in
 Zlength n=400 /\ Zlength d=400 /\ Zlength b=rows /\
 Zlength ib=cols /\ Zlength vn=cols /\ Zlength vd=cols /\
 Zlength hl=cols /\ Zlength hu=cols /\ Zlength ln=cols /\
 Zlength ld=cols /\ Zlength un=cols /\ Zlength ud=cols /\
 NoDup b /\
 (forall k,0<=k<rows -> 0<=Znth k b 0<cols /\ Znth (Znth k b 0) ib 0=1) /\
 (forall j,0<=j<cols -> 0<=Znth j ib 0<=1 /\ 0<=Znth j hl 0<=1 /\ 0<=Znth j hu 0<=1 /\
   (Znth j ib 0=1 <-> exists k,0<=k<rows /\ Znth k b 0=j) /\
   simplex_solve_rat (Znth j vn 0) (Znth j vd 0) /\
   simplex_solve_rat (Znth j ln 0) (Znth j ld 0) /\
   simplex_solve_rat (Znth j un 0) (Znth j ud 0) /\
   (Znth j hl 0<>0 -> Znth j hu 0<>0 ->
    (simplex_pivot_fraction (Znth j ln 0%Z) (Znth j ld 0%Z)<=simplex_pivot_fraction (Znth j un 0%Z) (Znth j ud 0%Z))%Qc) /\
   (Znth j ib 0=0 ->
    (Znth j hl 0<>0 -> (simplex_pivot_fraction (Znth j ln 0%Z) (Znth j ld 0%Z)<=simplex_pivot_fraction (Znth j vn 0%Z) (Znth j vd 0%Z))%Qc) /\
    (Znth j hu 0<>0 -> (simplex_pivot_fraction (Znth j vn 0%Z) (Znth j vd 0%Z)<=simplex_pivot_fraction (Znth j un 0%Z) (Znth j ud 0%Z))%Qc))) /\
 (forall k,In k (simplex_pivot_slots rows cols) -> simplex_solve_rat (Znth k n 0) (Znth k d 1)) /\
 (forall i k,0<=i<rows -> 0<=k<rows -> Znth (16+i*24+Znth k b 0) n 0=0) /\
 simplex_pivot_equations n d b rows cols (fun j=>simplex_pivot_fraction (Znth j vn 0) (Znth j vd 0)) /\
 (forall z:Z->Qc,
   (simplex_pivot_equations n d b rows cols z /\ simplex_solve_bounds hl hu ln ld un ud cols z) <->
   simplex_solve_source a rows inputs z).

(* Actual initialization formulas. Only active slots are constrained; D/N
   outside the active footprint are logical fillers handled by view lemmas. *)
Definition simplex_solve_initialized (a hl hu ln ld un ud:list Z) (rows inputs:Z)
 (s:simplex_solve_snapshot) : Prop :=
 let '(n,(d,(b,(ib,(vn,vd))))) :=s in
 let cols:=inputs+rows in
 Zlength n=400 /\ Zlength d=400 /\ Zlength b=rows /\ Zlength ib=cols /\
 Zlength vn=cols /\ Zlength vd=cols /\ Zlength hl=cols /\ Zlength hu=cols /\
 Zlength ln=cols /\ Zlength ld=cols /\ Zlength un=cols /\ Zlength ud=cols /\
 (forall i,0<=i<rows -> Znth i b 0=inputs+i /\ Znth i n 0=Znth (i*9) a 0 /\ Znth i d 1=1) /\
 (forall i j,0<=i<rows -> 0<=j<cols ->
   Znth (16+i*24+j) n 0=simplex_init_coeff a inputs i j /\ Znth (16+i*24+j) d 1=1) /\
 (forall j,0<=j<cols ->
   Znth j ib 0=(if j <? inputs then 0 else 1) /\ Znth j hl 0=0 /\
   Znth j hu 0=(if j <? inputs then 0 else 1) /\
   Znth j ln 0=0 /\ Znth j ld 0=1 /\ Znth j un 0=0 /\ Znth j ud 0=1 /\
   Znth j vn 0=(if j <? inputs then 0 else Znth ((j-inputs)*9) a 0) /\ Znth j vd 0=1).
Definition simplex_solve_success_step (hl hu ln ld un ud:list Z) (rows inputs:Z)
 (s t:simplex_solve_snapshot) : Prop :=
 simplex_solve_iteration hl hu ln ld un ud rows (inputs+rows) 1 0 s=(2,t).
Definition simplex_solve_origin (a hl hu ln ld un ud:list Z) (rows inputs:Z)
 (s:simplex_solve_snapshot) : Prop :=
 exists initial, simplex_solve_initialized a hl hu ln ld un ud rows inputs initial /\
 SetsClass.RelsDomain.clos_refl_trans (simplex_solve_success_step hl hu ln ld un ud rows inputs) initial s.

Lemma solve_success_budget_independent : forall hl hu ln ld un ud rows cols limit count s t,
 count<limit -> simplex_solve_iteration hl hu ln ld un ud rows cols limit count s=(2,t) ->
 simplex_solve_iteration hl hu ln ld un ud rows cols 1 0 s=(2,t).
Proof.
 intros hl hu ln ld un ud rows cols limit count [n [d [b [ib [vn vd]]]]] t HC HE.
 unfold simplex_solve_iteration in HE |- *.
 destruct (simplex_scan_compute (fun i=>Znth i b 0)
   (simplex_scan_rows b hl hu vn vd ln ld un ud) cols rows) as [q [best [r direction]]].
 destruct (Z.eqb q 1); [|discriminate]. destruct (Z.ltb r 0); [discriminate|].
 destruct (simplex_enter_compute (simplex_enter_observations ib (simplex_solve_row n r cols)
   hl hu vn vd ln ld un ud direction) cols) as [qe e].
 destruct (Z.eqb qe 1); [|discriminate]. destruct (Z.ltb e 0); [discriminate|].
 rewrite (proj2 (Z.leb_gt limit count) HC) in HE. cbn [Z.leb]. exact HE.
Qed.
Lemma solve_origin_extend : forall a hl hu ln ld un ud rows inputs limit count s t,
 simplex_solve_origin a hl hu ln ld un ud rows inputs s -> count<limit ->
 simplex_solve_iteration hl hu ln ld un ud rows (inputs+rows) limit count s=(2,t) ->
 simplex_solve_origin a hl hu ln ld un ud rows inputs t.
Proof.
 intros a hl hu ln ld un ud rows inputs limit count s t [initial [HI HO]] HC HE.
 exists initial. split; [exact HI|].
 pose proof (rt_trans_n1 (simplex_solve_success_step hl hu ln ld un ud rows inputs)) as HT.
 sets_unfold in HT. apply (HT initial t).
 exists s. split; [exact HO|]. unfold simplex_solve_success_step.
 eapply solve_success_budget_independent; eauto.
Qed.

Lemma solve_integer_rat : forall n, -2147483647<=n<=2147483647 -> simplex_solve_rat n 1.
Proof. intros. unfold simplex_solve_rat. rewrite Z.gcd_1_r. repeat split; lia. Qed.

Theorem solve_initialized_normal : forall a hl hu ln ld un ud rows inputs s,
 0<=rows -> 0<=inputs ->
 (forall i j,0<=i<rows -> 0<=j<=inputs -> -2147483647<=Znth (i*9+j) a 0<=2147483647) ->
 simplex_solve_initialized a hl hu ln ld un ud rows inputs s ->
 simplex_solve_normal a hl hu ln ld un ud rows inputs s.
Proof.
 intros a hl hu ln ld un ud rows inputs [n [d [b [ib [vn vd]]]]] HR HIN HA HI.
 unfold simplex_solve_initialized in HI. cbn zeta in HI.
 destruct HI as [HN [HD [HBL [HIL [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HROWS [HM HC]]]]]]]]]]]]]].
 unfold simplex_solve_normal. cbn zeta.
 do 12 (split; [assumption|]). split.
 - apply solve_nodup_indexed. rewrite HBL. intros i k HI HK HNE.
   destruct (HROWS i HI) as [BI _]. destruct (HROWS k HK) as [BK _]. rewrite BI,BK. lia.
 - split.
   + intros k HK. destruct (HROWS k HK) as [BI _]. rewrite BI. split; [lia|].
     destruct (HC (inputs+k) ltac:(lia)) as [HIB _]. rewrite HIB.
     rewrite (proj2 (Z.ltb_ge (inputs+k) inputs) ltac:(lia)). reflexivity.
   + split.
     * intros j HJ. destruct (HC j HJ) as [HIB [HL [HU [LNUM [LDEN [UNUM [UDEN [VNUM VDEN]]]]]]]].
       rewrite HIB,HL,HU,LNUM,LDEN,UNUM,UDEN,VNUM,VDEN.
       destruct (Z.ltb j inputs) eqn:EJ.
       -- apply Z.ltb_lt in EJ. do 3 (split; [lia|]). split.
          ++ split; [discriminate|]. intros [k [HK HE]]. destruct (HROWS k HK) as [BI _]. rewrite BI in HE. lia.
          ++ split; [apply solve_integer_rat; lia|]. split; [apply solve_integer_rat; lia|].
             split; [apply solve_integer_rat; lia|]. split; [tauto|]. intros _. split; tauto.
       -- apply Z.ltb_ge in EJ. do 3 (split; [lia|]). split.
          ++ split; intros; [exists (j-inputs); split; [lia|]|reflexivity].
             destruct (HROWS (j-inputs) ltac:(lia)) as [BI _]. rewrite BI. lia.
          ++ split.
             ** apply solve_integer_rat. replace ((j-inputs)*9) with ((j-inputs)*9+0) by lia. apply HA; lia.
             ** split; [apply solve_integer_rat; lia|]. split; [apply solve_integer_rat; lia|].
                split; [tauto|]. discriminate.
     * split.
       -- intros k HK. unfold simplex_pivot_slots in HK. apply in_app_or in HK.
          destruct HK as [HK|HK].
          ++ apply In_Zrange in HK. destruct (HROWS k HK) as [_ [HNUM HDEN]].
             rewrite HNUM,HDEN. apply solve_integer_rat.
             replace (k*9) with (k*9+0) by lia. apply HA; lia.
          ++ apply in_flat_map in HK. destruct HK as [i [HI HK]]. apply In_Zrange in HI.
             apply in_map_iff in HK. destruct HK as [j [E HJ]]. apply In_Zrange in HJ. subst k.
             destruct (HM i j HI HJ) as [HNUM HDEN]. rewrite HNUM,HDEN.
             unfold simplex_init_coeff. destruct (Z.ltb j inputs) eqn:EJ.
             ** apply Z.ltb_lt in EJ. apply solve_integer_rat. replace (i*9+j+1) with (i*9+(j+1)) by lia. apply HA; lia.
             ** apply solve_integer_rat; lia.
       -- split.
          ++ intros i k HI HK. destruct (HROWS k HK) as [BI _]. rewrite BI.
             destruct (HM i (inputs+k) HI ltac:(lia)) as [HN' _]. rewrite HN'.
             unfold simplex_init_coeff. rewrite (proj2 (Z.ltb_ge (inputs+k) inputs) ltac:(lia)). reflexivity.
          ++ split.
             ** intros i HI. destruct (HROWS i HI) as [BI [RN RD]]. rewrite BI.
                destruct (HC (inputs+i) ltac:(lia)) as [_ [_ [_ [_ [_ [_ [_ [VN VD]]]]]]]].
                rewrite VN,VD. rewrite (proj2 (Z.ltb_ge (inputs+i) inputs) ltac:(lia)).
                replace ((inputs+i-inputs)*9) with (i*9) by lia.
                assert (HRHSV:simplex_pivot_value n d i=simplex_pivot_fraction (Znth (i*9) a 0) 1) by (unfold simplex_pivot_value; rewrite RN,RD; reflexivity).
                rewrite HRHSV.
                assert (HZ:simplex_pivot_linear (Zrange 0%Z (inputs+rows)%Z)
                  (fun j=>(simplex_pivot_value n d (16+i*24+j)%Z *
                    simplex_pivot_fraction (Znth j vn 0%Z) (Znth j vd 0%Z))%Qc)=0%Qc).
                { rewrite <-(simplex_pivot_linear_zero (Zrange 0 (inputs+rows))). apply simplex_pivot_linear_ext.
                  intros j HJ. apply In_Zrange in HJ. destruct (HM i j HI HJ) as [AN AD].
                  destruct (HC j HJ) as [_ [_ [_ [_ [_ [_ [_ [VN' VD']]]]]]]].
                  unfold simplex_pivot_value. rewrite AN,AD,VN',VD'. unfold simplex_init_coeff.
                  destruct (Z.ltb j inputs); rewrite pivot_fraction_zero__success_math by lia; ring. }
                rewrite HZ. ring.
             ** apply solve_initial_source_equiv; auto.
                --- intros i HI. destruct (HROWS i HI) as [BI [RN RD]].
                    split; [exact BI|]. split; [unfold simplex_pivot_value; rewrite RN,RD; reflexivity|].
                    intros j HJ. destruct (HM i j HI HJ) as [AN AD].
                    unfold simplex_pivot_value. rewrite AN,AD. unfold simplex_init_coeff.
                    destruct (Z.ltb j inputs); [reflexivity|apply pivot_fraction_zero__success_math; lia].
                --- intros j HJ. destruct (HC j HJ) as [_ [HL [HU [_ [_ [UN [UD _]]]]]]].
                    split; [exact HL|]. split; [exact HU|]. rewrite UN,UD.
                    apply pivot_fraction_zero__success_math; lia.
Qed.

Lemma solve_rhs_nth : forall n rows i default,
 0<=i<rows -> Znth i (simplex_solve_rhs n rows) default=Znth i n default.
Proof. intros. unfold simplex_solve_rhs. rewrite Znth_sublist0 by lia. reflexivity. Qed.
Lemma solve_matrix_nth : forall filler n rows cols i j default,
 Zlength n=400 -> 0<=rows<=16 -> 0<=cols<=24 -> 0<=i<rows -> 0<=j<cols ->
 Znth (i*24+j) (simplex_solve_matrix filler n rows cols) default=Znth (16+i*24+j) n 0.
Proof.
 intros filler n rows cols i j default HN HR HC HI HJ. unfold simplex_solve_matrix.
 rewrite Znth_sublist by lia. replace (i*24+j+16) with (16+i*24+j) by lia.
 rewrite (Znth_indep _ _ default filler) by (rewrite simplex_pivot_pad_length; lia).
 rewrite simplex_pivot_pad_active by (auto; apply simplex_pivot_a_active; auto).
 apply Znth_indep. lia.
Qed.
Lemma solve_rhs_length : forall n rows,
 Zlength n=400 -> 0<=rows<=16 -> Zlength (simplex_solve_rhs n rows)=rows.
Proof. intros. unfold simplex_solve_rhs. rewrite Zlength_sublist by lia. lia. Qed.
Lemma solve_matrix_length : forall filler n rows cols,
 0<=rows<=16 -> Zlength (simplex_solve_matrix filler n rows cols)=rows*24.
Proof. intros. unfold simplex_solve_matrix. rewrite Zlength_sublist by (rewrite ?simplex_pivot_pad_length; lia). lia. Qed.

Lemma solve_pivot_source_preserved : forall a hl hu ln ld un ud n d pn pd b rows inputs r e,
 (forall z,(simplex_pivot_equations n d b rows (inputs+rows) z /\
   simplex_solve_bounds hl hu ln ld un ud (inputs+rows) z) <-> simplex_solve_source a rows inputs z) ->
 simplex_pivot_equiv n d pn pd b rows (inputs+rows) r e ->
 forall z,(simplex_pivot_equations pn pd (replace_Znth r e b) rows (inputs+rows) z /\
   simplex_solve_bounds hl hu ln ld un ud (inputs+rows) z) <-> simplex_solve_source a rows inputs z.
Proof. intros. unfold simplex_pivot_equiv in H0. rewrite <-H, <-H0. tauto. Qed.

Lemma solve_den_default : forall d k,
 Zlength d=400 -> 0<=k<400 -> Znth k d 0=Znth k d 1.
Proof. intros. apply Znth_indep; lia. Qed.

Theorem solve_recompute_pivot_equations : forall n d b ib vn vd ovn ovd rows cols,
 Zlength n=400 -> Zlength d=400 -> Zlength b=rows -> Zlength vn=cols -> Zlength vd=cols ->
 0<=rows<=16 -> 0<=cols<=24 -> NoDup b ->
 (forall i,0<=i<rows -> 0<=Znth i b 0<cols /\ Znth (Znth i b 0) ib 0<>0) ->
 (forall i,0<=i<rows -> 0<Znth i d 1 /\ forall j,0<=j<cols ->
   0<Znth (16+i*24+j) d 1 /\ (Znth j ib 0<>0 -> Znth (16+i*24+j) n 0=0)) ->
 (forall j,0<=j<cols -> 0<Znth j ovd 0) ->
 simplex_recompute_compute ib (simplex_solve_matrix 0 n rows cols) (simplex_solve_matrix 1 d rows cols)
   (simplex_solve_rhs n rows) (simplex_solve_rhs d rows) b vn vd rows cols=(1,(ovn,ovd)) ->
 simplex_pivot_equations n d b rows cols (fun j=>simplex_pivot_fraction (Znth j ovn 0) (Znth j ovd 0)).
Proof.
 intros n d b ib vn vd ovn ovd rows cols HN HD HBL HVN HVD HR HC HND HB HT HV HE.
 assert (HDE:forall i,0<=i<rows -> 0<Znth i (simplex_solve_rhs d rows) 0 /\
   forall j,0<=j<cols -> 0<Znth (i*24+j) (simplex_solve_matrix 1 d rows cols) 0 /\
    (Znth j ib 0<>0 -> Znth (i*24+j) (simplex_solve_matrix 0 n rows cols) 0=0)).
 { intros i HI. rewrite solve_rhs_nth by auto. rewrite solve_den_default by (auto; lia).
   destruct (HT i HI) as [HDI HM]. split; [exact HDI|]. intros j HJ.
   rewrite !solve_matrix_nth by auto. rewrite solve_den_default by (auto; lia). apply HM; auto. }
 pose proof (solve_recompute_final_equations ib (simplex_solve_matrix 0 n rows cols)
   (simplex_solve_matrix 1 d rows cols) (simplex_solve_rhs n rows) (simplex_solve_rhs d rows)
   b vn vd rows cols ovn ovd ltac:(lia) ltac:(lia) HVN HVD HB
   ltac:(intros; apply (proj1 (solve_nodup_indexed b) HND); lia) HDE HV HE) as HMATH.
 intros i HI. specialize (HMATH i HI).
 rewrite !solve_rhs_nth in HMATH by auto.
 rewrite (solve_den_default d i HD ltac:(lia)) in HMATH.
 unfold simplex_pivot_value. rewrite HMATH. f_equal. apply simplex_pivot_linear_ext.
 intros j HJ. apply In_Zrange in HJ.
 rewrite !solve_matrix_nth by auto.
 rewrite (solve_den_default d (16+i*24+j) HD ltac:(lia)). reflexivity.
Qed.

From Coq Require Import String.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string_scope.
Local Open Scope Z_scope.
(* Transparent active variable resources. Every included fraction is known;
   inactive positions are emp and can remain in the caller's exact frame. *)
Definition simplex_solve_var_slot (s cols:Z) (hl hu vn vd ln ld un ud:list Z) (j:Z) : Assertion :=
 if j <? cols then
 ((&(s # "SxState" ->ₛ "has_lower") + j*sizeof(INT)) # Int |-> Znth j hl 0 **
  (&(s # "SxState" ->ₛ "has_upper") + j*sizeof(INT)) # Int |-> Znth j hu 0) **
 simplex_scan_rat_memory s "value" j true (Znth j vn 0) (Znth j vd 0) **
 simplex_scan_rat_memory s "lower" j true (Znth j ln 0) (Znth j ld 0) **
 simplex_scan_rat_memory s "upper" j true (Znth j un 0) (Znth j ud 0)
 else emp.
Definition simplex_solve_variables (s cols:Z) (hl hu vn vd ln ld un ud:list Z) : Assertion :=
 iter_sepcon (map (simplex_solve_var_slot s cols hl hu vn vd ln ld un ud) (Zrange 0 24)).
Definition simplex_solve_read_rest_slot (s cols:Z) (basis hl hu vn vd ln ld un ud:list Z) (j:Z) : Assertion :=
 if j <? cols then
 let active:=existsb (Z.eqb j) basis in
 let low:=(active && negb (Z.eqb (Znth j hl 0) 0))%bool in
 let high:=(active && negb (Z.eqb (Znth j hu 0) 0))%bool in
 (if active then emp else
 ((&(s # "SxState" ->ₛ "has_lower") + j*sizeof(INT)) # Int |-> Znth j hl 0 **
  (&(s # "SxState" ->ₛ "has_upper") + j*sizeof(INT)) # Int |-> Znth j hu 0)) **
 (if (low || high)%bool then emp else simplex_scan_rat_memory s "value" j true (Znth j vn 0) (Znth j vd 0)) **
 (if low then emp else simplex_scan_rat_memory s "lower" j true (Znth j ln 0) (Znth j ld 0)) **
 (if high then emp else simplex_scan_rat_memory s "upper" j true (Znth j un 0) (Znth j ud 0))
 else emp.
Definition simplex_solve_read_rest (s cols:Z) (basis hl hu vn vd ln ld un ud:list Z) : Assertion :=
 iter_sepcon (map (simplex_solve_read_rest_slot s cols basis hl hu vn vd ln ld un ud) (Zrange 0 24)).

Lemma solve_iter_split : forall (xs:list Z) (P Q R:Z->Assertion),
 (forall j,In j xs -> P j |-- Q j ** R j) ->
 iter_sepcon (map P xs) |-- iter_sepcon (map Q xs) ** iter_sepcon (map R xs).
Proof.
 induction xs as [|x xs IH]; intros P Q R H; cbn [map iter_sepcon].
 - rewrite !logic_equiv_iter_sepcon_nil. elim_emp; reflexivity.
 - rewrite !logic_equiv_iter_sepcon_cons. sep_apply_l_atomic (H x (or_introl eq_refl)).
   sep_apply_l_atomic (IH P Q R ltac:(intros; apply H; right; auto)). cancel; try reflexivity.
Qed.
Lemma solve_iter_merge : forall (xs:list Z) (P Q R:Z->Assertion),
 (forall j,In j xs -> Q j ** R j |-- P j) ->
 iter_sepcon (map Q xs) ** iter_sepcon (map R xs) |-- iter_sepcon (map P xs).
Proof.
 induction xs as [|x xs IH]; intros P Q R H; cbn [map iter_sepcon].
 - rewrite !logic_equiv_iter_sepcon_nil. elim_emp; reflexivity.
 - rewrite !logic_equiv_iter_sepcon_cons. sep_apply_r_atomic (IH P Q R ltac:(intros; apply H; right; auto)).
   sep_apply_r_atomic (H x (or_introl eq_refl)). csimpl. sepcon_right_assoc.
   cancel (Q x). cancel (R x). reflexivity.
Qed.
Local Open Scope Z_scope.
Lemma solve_read_slot_split : forall s cols basis hl hu vn vd ln ld un ud j,
 (forall k,In k basis -> 0<=k<cols) ->
 simplex_solve_var_slot s cols hl hu vn vd ln ld un ud j |--
 simplex_scan_read_slot s basis hl hu vn vd ln ld un ud j **
 simplex_solve_read_rest_slot s cols basis hl hu vn vd ln ld un ud j.
Proof.
 intros. unfold simplex_solve_var_slot, simplex_solve_read_rest_slot, simplex_scan_read_slot.
 destruct (Z.ltb j cols) eqn:EJ.
 - destruct (existsb (Z.eqb j) basis); destruct (Z.eqb (Znth j hl 0) 0);
   destruct (Z.eqb (Znth j hu 0) 0); cbn [negb andb orb];
   try change (simplex_find_violation_retry_lib.simplex_scan_rat_memory s "value" j true (Znth j vn 0) (Znth j vd 0)) with (simplex_scan_rat_memory s "value" j true (Znth j vn 0) (Znth j vd 0));
   try change (simplex_find_violation_retry_lib.simplex_scan_rat_memory s "lower" j true (Znth j ln 0) (Znth j ld 0)) with (simplex_scan_rat_memory s "lower" j true (Znth j ln 0) (Znth j ld 0));
   try change (simplex_find_violation_retry_lib.simplex_scan_rat_memory s "upper" j true (Znth j un 0) (Znth j ud 0)) with (simplex_scan_rat_memory s "upper" j true (Znth j un 0) (Znth j ud 0));
   elim_emp; sepcon_right_assoc; cancel; try reflexivity.
 - assert (HE:existsb (Z.eqb j) basis=false).
   { apply Bool.not_true_is_false. intros HB. apply existsb_exists in HB.
     destruct HB as [k [HK HE]]. apply Z.eqb_eq in HE. subst k.
     apply Z.ltb_ge in EJ. specialize (H j HK). lia. }
   rewrite HE. cbn [negb andb orb]. elim_emp; reflexivity.
Qed.
Lemma solve_read_slot_merge : forall s cols basis hl hu vn vd ln ld un ud j,
 (forall k,In k basis -> 0<=k<cols) ->
 simplex_scan_read_slot s basis hl hu vn vd ln ld un ud j **
 simplex_solve_read_rest_slot s cols basis hl hu vn vd ln ld un ud j |--
 simplex_solve_var_slot s cols hl hu vn vd ln ld un ud j.
Proof.
 intros. unfold simplex_solve_var_slot, simplex_solve_read_rest_slot, simplex_scan_read_slot.
 destruct (Z.ltb j cols) eqn:EJ.
 - destruct (existsb (Z.eqb j) basis); destruct (Z.eqb (Znth j hl 0) 0);
   destruct (Z.eqb (Znth j hu 0) 0); cbn [negb andb orb];
   try change (simplex_find_violation_retry_lib.simplex_scan_rat_memory s "value" j true (Znth j vn 0) (Znth j vd 0)) with (simplex_scan_rat_memory s "value" j true (Znth j vn 0) (Znth j vd 0));
   try change (simplex_find_violation_retry_lib.simplex_scan_rat_memory s "lower" j true (Znth j ln 0) (Znth j ld 0)) with (simplex_scan_rat_memory s "lower" j true (Znth j ln 0) (Znth j ld 0));
   try change (simplex_find_violation_retry_lib.simplex_scan_rat_memory s "upper" j true (Znth j un 0) (Znth j ud 0)) with (simplex_scan_rat_memory s "upper" j true (Znth j un 0) (Znth j ud 0));
   elim_emp; sepcon_right_assoc; cancel; try reflexivity.
 - assert (HE:existsb (Z.eqb j) basis=false).
   { apply Bool.not_true_is_false. intros HB. apply existsb_exists in HB.
     destruct HB as [k [HK HE]]. apply Z.eqb_eq in HE. subst k.
     apply Z.ltb_ge in EJ. specialize (H j HK). lia. }
   rewrite HE. cbn [negb andb orb]. elim_emp; reflexivity.
Qed.
Lemma solve_search_split : forall s cols basis hl hu vn vd ln ld un ud,
 (forall k,In k basis -> 0<=k<cols) ->
 simplex_solve_variables s cols hl hu vn vd ln ld un ud |--
 simplex_scan_read_memory s basis hl hu vn vd ln ld un ud **
 simplex_solve_read_rest s cols basis hl hu vn vd ln ld un ud.
Proof. intros. unfold simplex_solve_variables, simplex_scan_read_memory, simplex_solve_read_rest.
 apply solve_iter_split. intros. apply solve_read_slot_split; auto. Qed.
Lemma solve_search_merge : forall s cols basis hl hu vn vd ln ld un ud,
 (forall k,In k basis -> 0<=k<cols) ->
 simplex_scan_read_memory s basis hl hu vn vd ln ld un ud **
 simplex_solve_read_rest s cols basis hl hu vn vd ln ld un ud |--
 simplex_solve_variables s cols hl hu vn vd ln ld un ud.
Proof. intros. unfold simplex_solve_variables, simplex_scan_read_memory, simplex_solve_read_rest.
 apply solve_iter_merge. intros. apply solve_read_slot_merge; auto. Qed.

Definition simplex_solve_bound_slot (s:Z) (hl hu ln ld un ud:list Z) (j:Z) : Assertion :=
 ((&(s # "SxState" ->ₛ "has_lower") + j*sizeof(INT)) # Int |-> Znth j hl 0 **
  (&(s # "SxState" ->ₛ "has_upper") + j*sizeof(INT)) # Int |-> Znth j hu 0) **
 simplex_scan_rat_memory s "lower" j true (Znth j ln 0) (Znth j ld 0) **
 simplex_scan_rat_memory s "upper" j true (Znth j un 0) (Znth j ud 0).
Definition simplex_solve_bound_memory (s cols:Z) (hl hu ln ld un ud:list Z) : Assertion :=
 iter_sepcon (map (simplex_solve_bound_slot s hl hu ln ld un ud) (Zrange 0 cols)).
Lemma solve_iter_emp_drop : forall (xs:list Z) (F:Z->Assertion),
 (forall j,In j xs -> F j=emp) -> iter_sepcon (map F xs) |-- emp.
Proof.
 induction xs as [|x xs IH]; intros F H; cbn [map].
 - rewrite logic_equiv_iter_sepcon_nil. reflexivity.
 - rewrite logic_equiv_iter_sepcon_cons, (H x (or_introl eq_refl)).
   sep_apply_l_atomic (IH F ltac:(intros; apply H; right; auto)). elim_emp; reflexivity.
Qed.
Lemma solve_iter_emp_build : forall (xs:list Z) (F:Z->Assertion),
 (forall j,In j xs -> F j=emp) -> emp |-- iter_sepcon (map F xs).
Proof.
 induction xs as [|x xs IH]; intros F H; cbn [map].
 - rewrite logic_equiv_iter_sepcon_nil. reflexivity.
 - rewrite logic_equiv_iter_sepcon_cons, (H x (or_introl eq_refl)).
   sep_apply_r_atomic (IH F ltac:(intros; apply H; right; auto)). elim_emp; reflexivity.
Qed.

Lemma solve_variables_split : forall s cols hl hu vn vd ln ld un ud,
 0<=cols<=24 -> simplex_solve_variables s cols hl hu vn vd ln ld un ud |--
 simplex_solve_bound_memory s cols hl hu ln ld un ud ** simplex_recompute_values s cols vn vd.
Proof.
 intros s cols hl hu vn vd ln ld un ud HC.
 unfold simplex_solve_variables. rewrite (range_split__failure_rhs 0 cols 24 ltac:(lia)).
 rewrite map_app, logic_equiv_iter_sepcon_app.
 sep_apply_l_atomic (solve_iter_emp_drop (Zrange cols 24)
  (simplex_solve_var_slot s cols hl hu vn vd ln ld un ud)
  ltac:(intros j HJ; apply In_Zrange in HJ; unfold simplex_solve_var_slot;
    rewrite (proj2 (Z.ltb_ge j cols) ltac:(lia)); reflexivity)).
 csimpl. elim_emp. unfold simplex_solve_bound_memory, simplex_recompute_values.
 apply solve_iter_split. intros j HJ. apply In_Zrange in HJ.
 unfold simplex_solve_var_slot, simplex_solve_bound_slot.
 rewrite (proj2 (Z.ltb_lt j cols) ltac:(lia)).
 csimpl. sepcon_right_assoc.
 cancel (simplex_scan_rat_memory s "value" j true (Znth j vn 0) (Znth j vd 0)).
 cancel; try reflexivity.
Qed.
Lemma solve_variables_merge : forall s cols hl hu vn vd ln ld un ud,
 0<=cols<=24 ->
 simplex_solve_bound_memory s cols hl hu ln ld un ud ** simplex_recompute_values s cols vn vd |--
 simplex_solve_variables s cols hl hu vn vd ln ld un ud.
Proof.
 intros s cols hl hu vn vd ln ld un ud HC.
 unfold simplex_solve_variables. rewrite (range_split__failure_rhs 0 cols 24 ltac:(lia)).
 rewrite map_app, logic_equiv_iter_sepcon_app.
 sep_apply_r_atomic (solve_iter_emp_build (Zrange cols 24)
  (simplex_solve_var_slot s cols hl hu vn vd ln ld un ud)
  ltac:(intros j HJ; apply In_Zrange in HJ; unfold simplex_solve_var_slot;
    rewrite (proj2 (Z.ltb_ge j cols) ltac:(lia)); reflexivity)).
 csimpl. elim_emp. unfold simplex_solve_bound_memory, simplex_recompute_values.
 apply solve_iter_merge. intros j HJ. apply In_Zrange in HJ.
 unfold simplex_solve_var_slot, simplex_solve_bound_slot.
 rewrite (proj2 (Z.ltb_lt j cols) ltac:(lia)).
 csimpl. sepcon_right_assoc.
 cancel (simplex_scan_rat_memory s "value" j true (Znth j vn 0) (Znth j vd 0)).
 cancel; try reflexivity.
Qed.

(* Complements retain exact known stores. Selected numerators are removed
   while their denominators remain owned, with the native row stride. *)
Definition simplex_solve_den_cell (s r:Z) (d:list Z) (j:Z) : Assertion :=
 (&((((&(s # "SxState" ->ₛ "a") + r*(sizeof("SxRat")*24)) + j*sizeof("SxRat"))) # "SxRat" ->ₛ "den")) # Int |-> Znth (16+r*24+j) d 1.
Definition simplex_solve_enter_rest (s rows cols:Z) (n d:list Z) (r:Z) : Assertion :=
 simplex_recompute_rhs s rows (simplex_solve_rhs n rows) (simplex_solve_rhs d rows) **
 iter_sepcon (remove_Znth r (map (fun i=>iter_sepcon
   (map (simplex_recompute_cell s (simplex_solve_matrix 0 n rows cols) (simplex_solve_matrix 1 d rows cols) i)
     (Zrange 0 cols))) (Zrange 0 rows))) **
 iter_sepcon (map (simplex_solve_den_cell s r d) (Zrange 0 cols)).
Definition simplex_solve_bound_except (s cols:Z) (hl hu ln ld un ud:list Z) (j:Z) : Assertion :=
 iter_sepcon (remove_Znth j (map (simplex_solve_bound_slot s hl hu ln ld un ud) (Zrange 0 cols))).
Definition simplex_solve_repair (lower upper value:list Z) (leaving direction:Z) : list Z :=
 replace_Znth leaving (if Z.ltb 0 direction then Znth leaving lower 0 else Znth leaving upper 0) value.

Lemma solve_iter_equiv : forall (xs:list Z) (P Q:Z->Assertion),
 (forall j,In j xs -> P j --||-- Q j) -> iter_sepcon (map P xs) --||-- iter_sepcon (map Q xs).
Proof.
 induction xs as [|x xs IH]; intros P Q H; cbn [map]; [reflexivity|].
 rewrite !logic_equiv_iter_sepcon_cons, (H x (or_introl eq_refl)).
 rewrite (IH P Q ltac:(intros; apply H; right; auto)). reflexivity.
Qed.
Lemma solve_iter_flat : forall (xs:list Z) (G:Z->list Z) (F:Z->Assertion),
 iter_sepcon (map F (flat_map G xs)) --||--
 iter_sepcon (map (fun x=>iter_sepcon (map F (G x))) xs).
Proof.
 induction xs as [|x xs IH]; intros G F; cbn [flat_map map]; [rewrite logic_equiv_iter_sepcon_nil; reflexivity|].
 rewrite map_app, logic_equiv_iter_sepcon_app, logic_equiv_iter_sepcon_cons, IH. reflexivity.
Qed.
Lemma solve_pivot_recompute_rhs_cell : forall s rows n d i,
 Zlength d=400 -> 0<=rows<=16 -> 0<=i<rows ->
 simplex_pivot_memory_cell s i (Znth i n 0) (Znth i d 1) =
 simplex_scan_rat_memory s "rhs" i true (Znth i (simplex_solve_rhs n rows) 0) (Znth i (simplex_solve_rhs d rows) 0).
Proof.
 intros. rewrite !solve_rhs_nth by auto. rewrite (solve_den_default d i) by (auto; lia).
 apply cell_rhs__entry_focus. lia.
Qed.
Lemma solve_pivot_recompute_matrix_cell : forall s rows cols n d i j,
 Zlength n=400 -> Zlength d=400 -> 0<=rows<=16 -> 0<=cols<=24 -> 0<=i<rows -> 0<=j<cols ->
 simplex_pivot_memory_cell s (16+i*24+j) (Znth (16+i*24+j) n 0) (Znth (16+i*24+j) d 1) =
 simplex_recompute_cell s (simplex_solve_matrix 0 n rows cols) (simplex_solve_matrix 1 d rows cols) i j.
Proof.
 intros. unfold simplex_recompute_cell. rewrite !solve_matrix_nth by auto.
 rewrite (solve_den_default d (16+i*24+j)) by (auto; lia).
 apply cell_a__entry_focus; lia.
Qed.
Theorem solve_pivot_recompute_memory : forall s rows cols n d,
 Zlength n=400 -> Zlength d=400 -> 0<=rows<=16 -> 0<=cols<=24 ->
 simplex_pivot_memory s rows cols n d --||--
 simplex_recompute_rhs s rows (simplex_solve_rhs n rows) (simplex_solve_rhs d rows) **
 simplex_recompute_matrix s rows cols (simplex_solve_matrix 0 n rows cols) (simplex_solve_matrix 1 d rows cols).
Proof.
 intros s rows cols n d HN HD HR HC.
 assert (HRHS:iter_sepcon (map (fun k=>simplex_pivot_memory_cell s k (Znth k n 0) (Znth k d 1)) (Zrange 0 rows)) --||--
   simplex_recompute_rhs s rows (simplex_solve_rhs n rows) (simplex_solve_rhs d rows)).
 { unfold simplex_recompute_rhs. apply solve_iter_equiv. intros i HI. apply In_Zrange in HI.
   rewrite (solve_pivot_recompute_rhs_cell s rows n d) by auto. reflexivity. }
 assert (HMAT:iter_sepcon (map (fun i=>iter_sepcon
    (map (fun k=>simplex_pivot_memory_cell s k (Znth k n 0) (Znth k d 1))
      (map (fun j=>16+i*24+j) (Zrange 0 cols)))) (Zrange 0 rows)) --||--
   simplex_recompute_matrix s rows cols (simplex_solve_matrix 0 n rows cols) (simplex_solve_matrix 1 d rows cols)).
 { unfold simplex_recompute_matrix. apply solve_iter_equiv. intros i HI. apply In_Zrange in HI.
   rewrite map_map. apply solve_iter_equiv. intros j HJ. apply In_Zrange in HJ.
   rewrite (solve_pivot_recompute_matrix_cell s rows cols n d) by auto. reflexivity. }
 unfold simplex_pivot_memory, simplex_pivot_slots.
 rewrite map_app, logic_equiv_iter_sepcon_app, solve_iter_flat, HRHS, HMAT. reflexivity.
Qed.

Lemma solve_row_nth : forall n r cols j,
 0<=j<cols -> Znth j (simplex_solve_row n r cols) 0=Znth (16+r*24+j) n 0.
Proof. intros. unfold simplex_solve_row. rewrite (Znth_map _ _ _ 0 0) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity. Qed.
Lemma solve_enter_cell : forall s rows cols n d r j,
 Zlength n=400 -> Zlength d=400 -> 0<=rows<=16 -> 0<=cols<=24 -> 0<=r<rows -> 0<=j<cols ->
 simplex_recompute_cell s (simplex_solve_matrix 0 n rows cols) (simplex_solve_matrix 1 d rows cols) r j =
 simplex_enter_num_cell s r (simplex_solve_row n r cols) j ** simplex_solve_den_cell s r d j.
Proof.
 intros. unfold simplex_recompute_cell, simplex_enter_num_cell, simplex_solve_den_cell.
 rewrite !solve_matrix_nth by auto. rewrite solve_row_nth by auto.
 rewrite (solve_den_default d (16+r*24+j)) by (auto; lia). reflexivity.
Qed.
Lemma solve_enter_row_equiv : forall s rows cols n d r,
 Zlength n=400 -> Zlength d=400 -> 0<=rows<=16 -> 0<=cols<=24 -> 0<=r<rows ->
 iter_sepcon (map (simplex_recompute_cell s (simplex_solve_matrix 0 n rows cols)
   (simplex_solve_matrix 1 d rows cols) r) (Zrange 0 cols)) --||--
 simplex_enter_num_memory s r cols (simplex_solve_row n r cols) **
 iter_sepcon (map (simplex_solve_den_cell s r d) (Zrange 0 cols)).
Proof.
 intros s rows cols n d r HN HD HR HC HRI. unfold simplex_enter_num_memory. split.
 - apply solve_iter_split. intros j HJ. apply In_Zrange in HJ.
   rewrite solve_enter_cell by auto. reflexivity.
 - apply solve_iter_merge. intros j HJ. apply In_Zrange in HJ.
   rewrite solve_enter_cell by auto. reflexivity.
Qed.
Theorem solve_enter_memory_split : forall s rows cols n d r,
 Zlength n=400 -> Zlength d=400 -> 0<=rows<=16 -> 0<=cols<=24 -> 0<=r<rows ->
 simplex_pivot_memory s rows cols n d |--
 simplex_enter_num_memory s r cols (simplex_solve_row n r cols) ** simplex_solve_enter_rest s rows cols n d r.
Proof.
 intros s rows cols n d r HN HD HR HC HRI.
 rewrite solve_pivot_recompute_memory by auto.
 unfold simplex_solve_enter_rest, simplex_recompute_matrix.
 set (F:=fun i=>iter_sepcon (map (simplex_recompute_cell s
   (simplex_solve_matrix 0 n rows cols) (simplex_solve_matrix 1 d rows cols) i) (Zrange 0 cols))).
 assert (HNTH:@Znth expr r (map F (Zrange 0 rows)) emp=F r).
 { rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
   rewrite simplex_scan_range_nth by lia. reflexivity. }
 pose proof (iter_sepcon_split_remove_Znth r (map F (Zrange 0 rows)) emp
   ltac:(rewrite Zlength_map, simplex_scan_range_length; lia)) as HS.
 rewrite HNTH in HS. sep_apply_l_atomic HS.
 unfold F. rewrite solve_enter_row_equiv by auto.
 csimpl. sepcon_right_assoc. cancel (simplex_enter_num_memory s r cols (simplex_solve_row n r cols)).
 cancel; try reflexivity.
Qed.
Theorem solve_enter_memory_merge : forall s rows cols n d r,
 Zlength n=400 -> Zlength d=400 -> 0<=rows<=16 -> 0<=cols<=24 -> 0<=r<rows ->
 simplex_enter_num_memory s r cols (simplex_solve_row n r cols) ** simplex_solve_enter_rest s rows cols n d r |--
 simplex_pivot_memory s rows cols n d.
Proof.
 intros s rows cols n d r HN HD HR HC HRI.
 rewrite solve_pivot_recompute_memory by auto.
 unfold simplex_solve_enter_rest, simplex_recompute_matrix.
 set (F:=fun i=>iter_sepcon (map (simplex_recompute_cell s
   (simplex_solve_matrix 0 n rows cols) (simplex_solve_matrix 1 d rows cols) i) (Zrange 0 cols))).
 assert (HNTH:@Znth expr r (map F (Zrange 0 rows)) emp=F r).
 { rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
   rewrite simplex_scan_range_nth by lia. reflexivity. }
 pose proof (iter_sepcon_merge_remove_Znth r (map F (Zrange 0 rows)) (F r)
   ltac:(rewrite Zlength_map, simplex_scan_range_length; lia)) as HS.
 rewrite <- HNTH, replace_Znth_Znth in HS. rewrite HNTH in HS.
 sep_apply_r_atomic HS. unfold F. rewrite solve_enter_row_equiv by auto.
 csimpl. sepcon_right_assoc. cancel (simplex_enter_num_memory s r cols (simplex_solve_row n r cols)).
 cancel; try reflexivity.
Qed.

Lemma solve_bound_focus : forall s cols hl hu ln ld un ud j,
 0<=j<cols -> simplex_solve_bound_memory s cols hl hu ln ld un ud |--
 simplex_solve_bound_slot s hl hu ln ld un ud j **
 simplex_solve_bound_except s cols hl hu ln ld un ud j.
Proof.
 intros. unfold simplex_solve_bound_memory, simplex_solve_bound_except.
 pose proof (iter_sepcon_split_remove_Znth j
   (map (simplex_solve_bound_slot s hl hu ln ld un ud) (Zrange 0 cols)) emp
   ltac:(rewrite Zlength_map, simplex_scan_range_length; lia)) as HS.
 rewrite (Znth_map _ _ _ 0 emp) in HS by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth in HS by lia. exact HS.
Qed.
Lemma solve_bound_merge : forall s cols hl hu ln ld un ud j,
 0<=j<cols ->
 simplex_solve_bound_slot s hl hu ln ld un ud j **
 simplex_solve_bound_except s cols hl hu ln ld un ud j |--
 simplex_solve_bound_memory s cols hl hu ln ld un ud.
Proof.
 intros. unfold simplex_solve_bound_memory, simplex_solve_bound_except.
 apply range_merge__failure_exit; auto.
Qed.


Lemma solve_success_normal__iteration :
 forall a hl hu ln ld un ud n d b ib vn vd pn pd on od rows inputs r e direction,
 0<=rows<=16 -> 0<=inputs<=8 ->
 simplex_solve_normal a hl hu ln ld un ud rows inputs (simplex_solve_pack n d b ib vn vd) ->
 0<=r<rows -> 0<=e<inputs+rows ->
 simplex_find_violation_spec b hl hu vn vd ln ld un ud (inputs+rows) rows 1 r direction ->
 Znth e ib 0=0 ->
 simplex_pivot_closed n d pn pd rows (inputs+rows) r e (Znth r b 0) ->
 simplex_pivot_equiv n d pn pd b rows (inputs+rows) r e ->
 Zlength pn=400 -> Zlength pd=400 ->
 (forall k, In k (simplex_pivot_slots rows (inputs+rows)) -> simplex_solve_rat (Znth k pn 0) (Znth k pd 1)) ->
 Zlength on=inputs+rows -> Zlength od=inputs+rows ->
 (forall j,0<=j<inputs+rows -> -2147483647<=Znth j on 0<=2147483647 /\ 1<=Znth j od 0<=2147483647) ->
 simplex_recompute_compute (replace_Znth e 1 (replace_Znth (Znth r b 0) 0 ib))
 (simplex_solve_matrix 0 pn rows (inputs+rows)) (simplex_solve_matrix 1 pd rows (inputs+rows))
 (simplex_solve_rhs pn rows) (simplex_solve_rhs pd rows) (replace_Znth r e b)
 (simplex_solve_repair ln un vn (Znth r b 0) direction)
 (simplex_solve_repair ld ud vd (Znth r b 0) direction) rows (inputs+rows)=(1,(on,od)) ->
 simplex_solve_normal a hl hu ln ld un ud rows inputs
 (simplex_solve_pack pn pd (replace_Znth r e b)
 (replace_Znth e 1 (replace_Znth (Znth r b 0) 0 ib)) on od).
Proof.
 intros a hl hu ln ld un ud n d b ib vn vd pn pd on od rows inputs r e direction
 HR HI HNORMAL HRI HE HSEARCH HENT HC HEQV HPN HPD HACTIVE HON HOD HOUT HCOMP.
 unfold simplex_solve_normal, simplex_solve_pack in HNORMAL |- *; cbn zeta in HNORMAL |- *.
 destruct HNORMAL as [HN [HD [HBL [HIL [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HB [HV [HA [HZ [HEQ HS]]]]]]]]]]]]]]]]]].
 assert (HBE:forall k,0<=k<rows -> 0<=Znth k b 0<inputs+rows /\ Znth k b 0<>e).
 { intros k HK. destruct (HB k HK) as [HBR HM]. split; auto. intro E; rewrite E,HENT in HM; discriminate. }
 destruct (HB r HRI) as [HLR HLM].
 assert (HNE:Znth r b 0<>e) by (exact (proj2 (HBE r HRI))).
 destruct (solve_pivot_basis_properties b rows (inputs+rows) r e HBL HRI HE HND HBE)
 as [HNBL [HNND HNB]].
 destruct (solve_pivot_mark_consistency b ib rows (inputs+rows) r e HBL HIL HRI HE HND HB
 ltac:(intros j HJ; destruct (HV j HJ) as [H1 [H2 [H3 [H4 H5]]]]; auto) HENT)
 as [HNM HNMV].
 assert (HDIR:direction=1 \/ direction= -1).
 { destruct (solve_violation_selected_row b hl hu vn vd ln ld un ud (inputs+rows) rows r direction HSEARCH ltac:(lia)) as [_ [HH _]]. exact HH. }
 assert (HREPAIR:forall j,0<=j<inputs+rows ->
 simplex_solve_rat (Znth j (simplex_solve_repair ln un vn (Znth r b 0) direction) 0)
 (Znth j (simplex_solve_repair ld ud vd (Znth r b 0) direction) 0)).
 { intros j HJ. unfold simplex_solve_repair. destruct (Z.eq_dec (Znth r b 0) j) as [E|E].
   - subst j. rewrite !Znth_replace_Znth_Same by lia.
     destruct (Z.ltb 0 direction); destruct (HV (Znth r b 0) HLR) as [_ [_ [_ [_ [_ [HL [HU _]]]]]]]; assumption.
   - rewrite !Znth_replace_Znth_Diff by lia. destruct (HV j HJ) as [_ [_ [_ [_ [HH _]]]]]. exact HH. }
 assert (HVRN:Zlength (simplex_solve_repair ln un vn (Znth r b 0) direction)=inputs+rows)
 by (unfold simplex_solve_repair; rewrite Zlength_replace_Znth; auto).
 assert (HVRD:Zlength (simplex_solve_repair ld ud vd (Znth r b 0) direction)=inputs+rows)
 by (unfold simplex_solve_repair; rewrite Zlength_replace_Znth; auto).
 assert (HROWS:forall i,0<=i<rows ->
 0<=Znth i (replace_Znth r e b) 0<inputs+rows /\
 0<Znth i (simplex_solve_rhs pd rows) 0 /\
 Z.gcd (Z.abs (Znth i (simplex_solve_rhs pn rows) 0)) (Znth i (simplex_solve_rhs pd rows) 0)=1 /\
 forall j,0<=j<inputs+rows -> 0<Znth (i*24+j) (simplex_solve_matrix 1 pd rows (inputs+rows)) 0).
 { intros i HII. rewrite !solve_rhs_nth by auto. rewrite (solve_den_default pd i HPD ltac:(lia)).
   pose proof (HACTIVE i (simplex_pivot_rhs_active rows (inputs+rows) i HII)) as HH.
   unfold simplex_solve_rat in HH. split; [apply HNB; auto|]. split; [lia|]. split; [tauto|].
   intros j HJ. rewrite solve_matrix_nth by (auto; lia).
   rewrite (solve_den_default pd (16+i*24+j) HPD ltac:(lia)).
   pose proof (HACTIVE _ (simplex_pivot_a_active rows (inputs+rows) i j HII HJ)) as HHH.
   unfold simplex_solve_rat in HHH; lia. }
 destruct (solve_recompute_normal_fractions _ _ _ _ _ _ _ _ rows (inputs+rows)
 ltac:(lia) ltac:(lia) HVRN HVRD
 ltac:(intros; specialize (HREPAIR _ H); unfold simplex_solve_rat in HREPAIR; intuition lia)
 HROWS 1 on od HCOMP) as [_ [_ [_ HFRAC]]].
 destruct (solve_recompute_reconstruction _ _ _ _ _ _ _ _ rows (inputs+rows)
 ltac:(lia) ltac:(lia) HVRN HVRD
 ltac:(intros i HII; split; [apply HNB; auto|]; rewrite HNM by auto; discriminate)
 ltac:(intros; apply (proj1 (solve_nodup_indexed _) HNND); lia) 1 on od HCOMP)
 as [_ [_ [_ [HUNCH _]]]].
 do 3 (split; [assumption|]). split; [rewrite !Zlength_replace_Znth; auto|].
 do 8 (split; [assumption|]). split; [exact HNND|]. split.
 - intros k HK. split; [apply HNB; auto|apply HNM; auto].
 - split.
   + intros j HJ. destruct (HV j HJ) as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]].
     destruct (HNMV j HJ) as [HM1 HM2].
     do 4 (split; [assumption|]). split.
     * unfold simplex_solve_rat. destruct (HOUT j HJ), (HFRAC j HJ); intuition lia.
     * split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
       intro HM. destruct (HUNCH j HJ HM) as [E1 E2]. rewrite E1,E2.
       unfold simplex_solve_repair. destruct (Z.eq_dec j (Znth r b 0)) as [E|E].
       -- subst j. rewrite !Znth_replace_Znth_Same by lia.
          destruct (solve_violation_selected_row b hl hu vn vd ln ld un ud (inputs+rows) rows r direction HSEARCH ltac:(lia)) as [_ [_ OBS]].
          unfold simplex_scan_rows in OBS.
          destruct HDIR as [DD|DD]; subst direction; cbn [Z.ltb].
          ++ assert (HL:Znth (Znth r b 0) hl 0<>0).
             { eapply (proj1 (solve_scan_row_lower (Znth (Znth r b 0) hl 0) (Znth (Znth r b 0) hu 0) (Znth (Znth r b 0) vn 0) (Znth (Znth r b 0) vd 0) (Znth (Znth r b 0) ln 0) (Znth (Znth r b 0) ld 0) (Znth (Znth r b 0) un 0) (Znth (Znth r b 0) ud 0) ltac:(unfold simplex_solve_rat in H5; lia) ltac:(unfold simplex_solve_rat in H6; lia) OBS)). }
             split; intros; [apply Qcle_refl|apply H8; auto].
          ++ assert (HU:Znth (Znth r b 0) hu 0<>0).
             { eapply (proj1 (solve_scan_row_upper (Znth (Znth r b 0) hl 0) (Znth (Znth r b 0) hu 0) (Znth (Znth r b 0) vn 0) (Znth (Znth r b 0) vd 0) (Znth (Znth r b 0) ln 0) (Znth (Znth r b 0) ld 0) (Znth (Znth r b 0) un 0) (Znth (Znth r b 0) ud 0) ltac:(unfold simplex_solve_rat in H5; lia) ltac:(unfold simplex_solve_rat in H7; lia) OBS)). }
             split; intros; [apply H8; auto|apply Qcle_refl].
       -- rewrite !Znth_replace_Znth_Diff by lia.
          rewrite (solve_pivot_marks_at ib (inputs+rows)) in HM by auto.
          destruct (Z.eq_dec j e); [discriminate|]. destruct (Z.eq_dec j (Znth r b 0)); [contradiction|].
          exact (H9 HM).
   + split; [exact HACTIVE|].
     assert (HNEWZERO:forall i k,0<=i<rows -> 0<=k<rows ->
      simplex_pivot_value pn pd (16+i*24+Znth k (replace_Znth r e b) 0)=0%Qc).
     { eapply solve_pivot_zero_basic_columns; eauto.
       - intros; apply (proj1 (solve_nodup_indexed b) HND); lia.
       - intros i k HII HK. unfold simplex_pivot_value. rewrite HZ by auto.
         apply pivot_fraction_zero__success_math.
         pose proof (HA _ (simplex_pivot_a_active rows (inputs+rows) i (Znth k b 0) HII (proj1 (HB k HK)))).
         unfold simplex_solve_rat in H; lia. }
     assert (HRAW:forall i k,0<=i<rows -> 0<=k<rows ->
      Znth (16+i*24+Znth k (replace_Znth r e b) 0) pn 0=0).
     { intros i k HII HK. destruct (Z.eq_dec (Znth (16+i*24+Znth k (replace_Znth r e b) 0) pn 0) 0) as [E|E]; auto.
       exfalso. assert (HPOS:0<Znth (16+i*24+Znth k (replace_Znth r e b) 0) pd 1).
       { pose proof (HACTIVE _ (simplex_pivot_a_active rows (inputs+rows) i
        (Znth k (replace_Znth r e b) 0) HII (HNB k HK))) as HH.
       unfold simplex_solve_rat in HH; lia. }
       exact (pivot_fraction_nonzero__success_math _ _ HPOS E (HNEWZERO i k HII HK)). }
     split.
     * exact HRAW.
     * split.
       -- eapply (solve_recompute_pivot_equations pn pd (replace_Znth r e b)
 (replace_Znth e 1 (replace_Znth (Znth r b 0) 0 ib))
 (simplex_solve_repair ln un vn (Znth r b 0) direction)
 (simplex_solve_repair ld ud vd (Znth r b 0) direction) on od rows (inputs+rows)); eauto; try lia.
          ++ intros i HII. split; [apply HNB; auto|]. rewrite HNM by auto; discriminate.
          ++ intros i HII. split.
             ** pose proof (HACTIVE i (simplex_pivot_rhs_active rows (inputs+rows) i HII)).
                unfold simplex_solve_rat in H; lia.
             ** intros j HJ. split.
                --- pose proof (HACTIVE _ (simplex_pivot_a_active rows (inputs+rows) i j HII HJ)).
                    unfold simplex_solve_rat in H; lia.
                --- intro HM. destruct (HNMV j HJ) as [HRANGE HH].
                    assert (HMONE:Znth j (replace_Znth e 1 (replace_Znth (Znth r b 0) 0 ib)) 0=1) by lia.
                    apply HH in HMONE. destruct HMONE as [k [HK EK]]. subst j.
                    specialize (HNEWZERO i k HII HK).
                    (* supplied by the preceding zero proof *)
                    apply HRAW; auto.
          ++ intros; destruct (HOUT _ H); lia.
       -- eapply solve_pivot_source_preserved; eauto.
Qed.
Lemma solve_recompute_code__iteration : forall ib an ad rn rd b vn vd rows cols q on od,
 simplex_recompute_compute ib an ad rn rd b vn vd rows cols=(q,(on,od)) -> q=0 \/ q=1.
Proof.
 intros ib an ad rn rd b vn vd rows cols.
 unfold simplex_recompute_compute.
 generalize (Zrange 0 rows). intros xs.
 assert (HH:forall xs q vn vd, q=0 \/ q=1 ->
  let '(oq,_) := fold_left (simplex_recompute_commit ib an ad rn rd b cols) xs (q,(vn,vd))
  in oq=0 \/ oq=1).
 { intro ys. induction ys as [|x ys IH]; intros q cn cd HQ; cbn [fold_left]; [exact HQ|].
   destruct HQ as [EQ|EQ]; subst q; cbn [simplex_recompute_commit].
   - apply IH; auto.
   - destruct (simplex_recompute_row ib an ad cn cd rn rd x cols) as [[u v]|]; apply IH; auto. }
 intros q on od HE. specialize (HH xs 1 vn vd ltac:(auto)). rewrite HE in HH. exact HH.
Qed.
Lemma solve_enter_nonbasic__iteration : forall ib coeff hl hu vn vd ln ld un ud direction cols e,
 0<=e -> simplex_find_entering_spec ib coeff hl hu vn vd ln ld un ud direction cols 1 e ->
 Znth e ib 0=0.
Proof.
 intros ib coeff hl hu vn vd ln ld un ud direction cols e HE HS.
 unfold simplex_find_entering_spec, simplex_enter_result in HS.
 destruct HS as [[_ [HH _]]|[k [HK [HP [[_ [EE HO]]|[HF _]]]]]]; try lia.
 subst k. unfold simplex_enter_observations, simplex_enter_column in HO.
 destruct (negb (Z.eqb (Znth e ib 0) 0) || Z.eqb (Znth e coeff 0) 0)%bool eqn:HB; [discriminate|].
 apply Bool.orb_false_iff in HB. destruct HB as [HB _].
 apply Bool.negb_false_iff in HB. apply Z.eqb_eq in HB. exact HB.
Qed.
Lemma solve_forall_nth__iteration : forall (P:Z->Prop) xs j,
 Forall P xs -> 0<=j<Zlength xs -> P (Znth j xs 0).
Proof.
 intros P xs j HH HJ. rewrite Forall_forall in HH. apply HH.
 unfold Znth. apply nth_In. rewrite Zlength_correct in HJ. lia.
Qed.
Lemma solve_no_candidate_unsat__unsat : forall a hl hu ln ld un ud rows inputs n d b ib vn vd r dir e,
 0<=rows -> 0<=inputs ->
 simplex_solve_normal a hl hu ln ld un ud rows inputs (simplex_solve_pack n d b ib vn vd) ->
 simplex_find_violation_spec b hl hu vn vd ln ld un ud (inputs+rows) rows 1 r dir ->
 0<=r -> (dir=1 \/ dir= -1) ->
 simplex_find_entering_spec ib (simplex_solve_row n r (inputs+rows)) hl hu vn vd ln ld un ud dir (inputs+rows) 1 e ->
 e<0 -> simplex_solve_unsat a rows inputs.
Proof.
 intros a hl hu ln ld un ud rows inputs n d b ib vn vd r dir e HR HI HN HV HRI HD HE HEN.
 unfold simplex_solve_normal, simplex_solve_pack in HN.
 do 12 destruct HN as [_ HN].
 destruct HN as [HND [HBR [HC [HS [HZ [HQ HEQ]]]]]].
 pose proof (solve_violation_selected_row _ _ _ _ _ _ _ _ _ _ _ _ _ HV HRI) as [HRB [_ HSCAN]].
 pose proof (HBR r HRB) as [HBC HBASIC].
 pose proof (solve_no_entering_columns _ _ _ _ _ _ _ _ _ _ _ _ _ HE HEN) as HSKIP.
 set (ad:=map (fun j=>Znth (16+r*24+j) d 1) (Zrange 0%Z (inputs+rows))).
 assert (HAD:forall j,0<=j<inputs+rows -> Znth j ad 0%Z=Znth (16+r*24+j) d 1).
 { intros j HJ. unfold ad. rewrite (Znth_map _ _ _ 0 0) by (rewrite simplex_scan_range_length; lia).
   rewrite simplex_scan_range_nth by lia. reflexivity. }
 assert (HP:forall j,0<=j<inputs+rows -> 0<Znth j ad 0%Z /\ 0<Znth j vd 0 /\
   0<Znth j ld 0 /\ 0<Znth j ud 0 /\ (Znth j ib 0<>0 -> Znth j (simplex_solve_row n r (inputs+rows)) 0%Z=0)).
 { intros j HJ. rewrite HAD, solve_row_nth by auto.
   pose proof (HS _ (simplex_pivot_a_active rows (inputs+rows) r j HRB HJ)) as HA.
   destruct (HC j HJ) as [HJB [_ [_ [HJE [HVJ [HLJ [HUJ _]]]]]]].
   unfold simplex_solve_rat in HA,HVJ,HLJ,HUJ. repeat split; try lia.
   intros HNZ. assert (E:Znth j ib 0=1) by lia.
   destruct (proj1 HJE E) as [k [HK HKJ]]. rewrite <-HKJ. apply HZ; auto. }
 assert (HROW:forall z, simplex_pivot_equations n d b rows (inputs+rows) z ->
 z (Znth r b 0%Z)=(simplex_pivot_fraction (Znth r n 0%Z) (Znth r d 1%Z)+
 simplex_pivot_linear (Zrange 0%Z (inputs+rows)) (fun j=>
 simplex_pivot_fraction (Znth j (simplex_solve_row n r (inputs+rows)) 0%Z) (Znth j ad 0%Z)*z j))%Qc).
 { intros z HZQ. rewrite (HZQ r HRB). unfold simplex_pivot_value. f_equal.
   apply simplex_pivot_linear_ext. intros j HJ. apply In_Zrange in HJ.
   rewrite HAD,solve_row_nth by auto. reflexivity. }
 pose proof (HROW _ HQ) as HCUR.
 unfold simplex_scan_rows in HSCAN.
 destruct (HC (Znth r b 0%Z) HBC) as [_ [_ [_ [_ [HVR [HLR [HUR _]]]]]]].
 unfold simplex_solve_rat in HVR,HLR,HUR.
 unfold simplex_solve_unsat. intros x HX.
 destruct (solve_source_extension a rows inputs x HI HX) as [z [_ HSRC]].
 destruct (proj2 (HEQ z) HSRC) as [HZE HZB].
 destruct HD as [HD|HD]; subst dir.
 - destruct (solve_scan_row_lower (Znth (Znth r b 0%Z) hl 0%Z) (Znth (Znth r b 0%Z) hu 0%Z) (Znth (Znth r b 0%Z) vn 0%Z) (Znth (Znth r b 0%Z) vd 0%Z) (Znth (Znth r b 0%Z) ln 0%Z) (Znth (Znth r b 0%Z) ld 0%Z) (Znth (Znth r b 0%Z) un 0%Z) (Znth (Znth r b 0%Z) ud 0%Z) ltac:(lia) ltac:(lia) HSCAN) as [HLOW HVIOL].
   eapply (solve_no_entering_row_conflict_plus ib (simplex_solve_row n r (inputs+rows)) ad hl hu vn vd ln ld un ud (inputs+rows) (Znth r b 0%Z)
     (simplex_pivot_fraction (Znth r n 0%Z) (Znth r d 1%Z)));
     [lia|exact HBC|exact HP|exact HSKIP|exact HCUR|exact HLOW|exact HVIOL|exact HZB|apply HROW; exact HZE].
 - destruct (solve_scan_row_upper (Znth (Znth r b 0%Z) hl 0%Z) (Znth (Znth r b 0%Z) hu 0%Z) (Znth (Znth r b 0%Z) vn 0%Z) (Znth (Znth r b 0%Z) vd 0%Z) (Znth (Znth r b 0%Z) ln 0%Z) (Znth (Znth r b 0%Z) ld 0%Z) (Znth (Znth r b 0%Z) un 0%Z) (Znth (Znth r b 0%Z) ud 0%Z) ltac:(lia) ltac:(lia) HSCAN) as [HUP HVIOL].
   eapply (solve_no_entering_row_conflict_minus ib (simplex_solve_row n r (inputs+rows)) ad hl hu vn vd ln ld un ud (inputs+rows) (Znth r b 0%Z)
     (simplex_pivot_fraction (Znth r n 0%Z) (Znth r d 1%Z)));
     [lia|exact HBC|exact HP|exact HSKIP|exact HCUR|exact HUP|exact HVIOL|exact HZB|apply HROW; exact HZE].
Qed.
Lemma solve_terminal_result__unsat : forall a hl hu ln ld un ud rows inputs cols limit count n d b ib vn vd cn cd cb cib cvn cvd r dir e,
 cols=inputs+rows -> 0<=rows -> 0<=inputs -> 0<=limit -> 0<=count<=limit ->
 simplex_solve_normal a hl hu ln ld un ud rows inputs (simplex_solve_pack cn cd cb cib cvn cvd) ->
 simplex_solve_progress hl hu ln ld un ud rows cols limit count n d b ib vn vd cn cd cb cib cvn cvd ->
 simplex_find_violation_spec cb hl hu cvn cvd ln ld un ud cols rows 1 r dir -> 0<=r ->
 simplex_find_entering_spec cib (simplex_solve_row cn r cols) hl hu cvn cvd ln ld un ud dir cols 1 e -> e<0 ->
 simplex_solve_result hl hu ln ld un ud rows cols limit n d b ib vn vd 1 cn cd cb cib cvn cvd.
Proof.
 intros a hl hu ln ld un ud rows inputs cols limit count n d b ib vn vd cn cd cb cib cvn cvd r dir e EC HR HI HL HCOUNT HN HP HV HRI HE HEN.
 assert (HB:forall j,0<=j<rows -> Znth j cb 0<cols).
 { unfold simplex_solve_normal,simplex_solve_pack in HN.
   do 13 destruct HN as [_ HN]. destruct HN as [HB _].
   intros j HJ. specialize (HB j HJ). lia. }
 destruct (proj1 (simplex_find_violation_compute_iff (fun i=>Znth i cb 0)
   (simplex_scan_rows cb hl hu cvn cvd ln ld un ud) cols rows 1 r dir HR HB) HV) as [best HVC].
 pose proof (proj1 (simplex_enter_preserve_compute_iff cib (simplex_solve_row cn r cols) hl hu cvn cvd ln ld un ud dir cols 1 e ltac:(lia)) HE) as HEC.
 unfold simplex_solve_result. eapply solve_terminal_complete with (count:=count); [exact HL|exact HCOUNT|lia|].
 unfold simplex_solve_progress in HP.
 unfold simplex_solve_tick. rewrite HP.
 change (simplex_solve_iteration hl hu ln ld un ud rows cols limit count
   (simplex_solve_pack cn cd cb cib cvn cvd)=(1,simplex_solve_pack cn cd cb cib cvn cvd)).
 unfold simplex_solve_iteration, simplex_solve_pack.
 rewrite HVC.
 rewrite (proj2 (Z.ltb_ge r 0) HRI), HEC.
 rewrite (proj2 (Z.ltb_lt e 0) HEN). reflexivity.
Qed.
Lemma indexed_forall__recompute_preconditions : forall (P:Z->Prop) l,
 (forall i,0<=i<Zlength l -> P (Znth i l 0)) -> Forall P l.
Proof.
 intros P l. induction l as [|a l IH]; intros H; [constructor|].
 rewrite Zlength_cons in H. constructor.
 - specialize (H 0 ltac:(pose proof (Zlength_nonneg l); lia)). rewrite Znth0_cons in H. exact H.
 - apply IH. intros i Hi. specialize (H (i+1) ltac:(lia)). rewrite Znth_cons in H by lia.
   replace (i+1-1) with i in H by lia. exact H.
Qed.
Lemma matrix_prop__recompute_preconditions : forall (P:Z->Prop) filler n rows cols,
 0<=rows<=16 -> 0<=cols<=24 -> P filler ->
 (forall k, In k (simplex_pivot_slots rows cols) -> P (Znth k n filler)) ->
 Forall P (simplex_solve_matrix filler n rows cols).
Proof.
 intros P filler n rows cols HR HC HF HA.
 apply indexed_forall__recompute_preconditions. intros i HI.
 unfold simplex_solve_matrix in *. rewrite Zlength_sublist in HI by (rewrite simplex_pivot_pad_length; lia).
 rewrite Znth_sublist by lia.
 unfold simplex_pivot_pad. rewrite (Znth_map _ _ _ 0 0) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia.
 destruct (existsb (Z.eqb (i+16)) (simplex_pivot_slots rows cols)) eqn:E; [|exact HF].
 apply existsb_exists in E. destruct E as [k [HK HE]]. apply Z.eqb_eq in HE. subst k. apply HA. exact HK.
Qed.
Lemma rhs_prop__recompute_preconditions : forall (P:Z->Prop) n rows,
 Zlength n=400 -> 0<=rows<=16 ->
 (forall k,0<=k<rows -> P (Znth k n 0)) -> Forall P (simplex_solve_rhs n rows).
Proof.
 intros P n rows HN HR HA. apply indexed_forall__recompute_preconditions. intros k HK.
 rewrite solve_rhs_length in HK by auto. rewrite solve_rhs_nth by auto. auto.
Qed.
Lemma repair_prop__recompute_preconditions : forall (P:Z->Prop) ln un vn cols leaving direction,
 Zlength vn=cols -> 0<=leaving<cols ->
 (forall j,0<=j<cols -> P (Znth j vn 0)) -> P (Znth leaving ln 0) -> P (Znth leaving un 0) ->
 Forall P (simplex_solve_repair ln un vn leaving direction).
Proof.
 intros P ln un vn cols leaving direction HV HL HA HB HC.
 unfold simplex_solve_repair. apply indexed_forall__recompute_preconditions. intros j HJ.
 rewrite Zlength_replace_Znth, HV in HJ.
 destruct (Z.eq_dec j leaving) as [E|E].
 - subst j. rewrite Znth_replace_Znth_Same by lia. destruct (Z.ltb 0 direction); auto.
 - rewrite Znth_replace_Znth_Diff by lia. apply HA; auto.
Qed.
Lemma pivot_lengths__repair_memory : forall n d rows cols r e b q on od,
 Zlength n=400 -> Zlength d=400 ->
 simplex_pivot_result n d rows cols r e b q on od ->
 Zlength on=400 /\ Zlength od=400.
Proof.
 intros n d rows cols r e b q on od HN HD HE.
 unfold simplex_pivot_result, simplex_pivot_compute in HE.
 set (P:=fun s:simplex_pivot_state=>Zlength(fst(snd s))=400 /\ Zlength(snd(snd s))=400).
 assert (DV:forall a c k neg s,P s -> P(simplex_pivot_div a c k neg s)).
 { intros a c k neg [t[nt dt]] [A B]. unfold P.
   destruct (pivot_div_lengths__success_math a c k neg t nt dt) as [C D]. rewrite C,D. exact (conj A B). }
 assert (RC:forall a c k s,P s -> P(simplex_pivot_recip a c k s)).
 { intros a c k [t[nt dt]] [A B]. unfold P.
   destruct (pivot_recip_lengths__success_math a c k t nt dt) as [C D]. rewrite C,D. exact (conj A B). }
 assert (ZR:forall k s,P s -> P(simplex_pivot_zero k s)).
 { intros k [t[nt dt]] [A B]. unfold P.
   destruct (pivot_zero_lengths__success_math k t nt dt) as [C D]. rewrite C,D. exact (conj A B). }
 assert (RW:forall a c s,P s -> P(simplex_pivot_row_prefix a c r e cols s)).
 { intros a c [t[nt dt]] [A B]. unfold P.
   apply pivot_row_lengths__success_math; assumption. }
 assert (OT:forall s i,P s -> P(simplex_pivot_other_row r e cols s i)).
 { intros [t[nt dt]] i [A B]. apply pivot_other_row_lengths__success_math; assumption. }
 assert (OUT:P(simplex_pivot_compute n d rows cols r e b)).
 { unfold simplex_pivot_compute, simplex_pivot_rows_prefix.
   apply (pivot_fold_invariant__success_math _ P).
   - intros; apply OT; assumption.
   - apply ZR, RC, RW, DV. split; assumption. }
 unfold simplex_pivot_result in HE.
 change (simplex_pivot_compute n d rows cols r e b=(q,(on,od))) in HE.
 rewrite HE in OUT. exact OUT.
Qed.
Lemma values_cells_store__repair_memory : forall s v cn cd b n d,
 Zlength cn=v -> Zlength cd=v -> 0<=b<v ->
 &( &(s # "SxState" ->ₛ "value" [b]) ->ₛ "num") # Int |-> n **
 &( &(s # "SxState" ->ₛ "value" [b]) ->ₛ "den") # Int |-> d **
 simplex_recompute_values_except s v cn cd b |--
 simplex_recompute_values s v (replace_Znth b n cn) (replace_Znth b d cd).
Proof.
 intros s v cn cd b n d HN HD HB.
 sep_apply_r_atomic (values_store__row_commit s v cn cd b n d HN HD HB).
 unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
 repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress (cancel P) end end. reflexivity.
Qed.
Lemma normal_basis__search_memory : forall a hl hu ln ld un ud m i n d b ib vn vd,
 simplex_solve_normal a hl hu ln ld un ud m i (simplex_solve_pack n d b ib vn vd) ->
 forall k, In k b -> 0<=k<m+i.
Proof.
 intros a hl hu ln ld un ud m i n d b ib vn vd H k HK.
 unfold simplex_solve_normal, simplex_solve_pack in H.
 destruct H as [HN [HD [HB [HIB [HVN [HVD [HHL [HHU [HLN [HLD [HUN [HUD [HND [HBAS REST]]]]]]]]]]]]]].
 apply In_nth with (d:=0) in HK. destruct HK as [j [HJ HE]].
 specialize (HBAS (Z.of_nat j)).
 apply Nat2Z.inj_lt in HJ.
 assert (HZ:0<=Z.of_nat j<m) by (rewrite Zlength_correct in HB; lia).
 specialize (HBAS HZ).
 unfold Znth in HBAS. rewrite Nat2Z.id in HBAS. rewrite HE in HBAS. lia.
Qed.
Lemma in_index__search_preconditions : forall (l:list Z) x,
 In x l -> exists k, 0<=k<Zlength l /\ Znth k l 0=x.
Proof.
 intros l x H. destruct (In_nth l x 0 H) as [k [Hk E]].
 exists (Z.of_nat k). rewrite Zlength_correct. split; [lia|].
 unfold Znth. rewrite Nat2Z.id. exact E.
Qed.
Lemma solve_scan_normal__rejection_results : forall a hl hu ln ld un ud rows inputs n d b ib vn vd r direction,
 0<=rows ->
 simplex_solve_normal a hl hu ln ld un ud rows inputs (simplex_solve_pack n d b ib vn vd) ->
 simplex_find_violation_spec b hl hu vn vd ln ld un ud (rows+inputs) rows 1 r direction ->
 exists best, simplex_scan_compute (fun j=>Znth j b 0)
 (simplex_scan_rows b hl hu vn vd ln ld un ud) (rows+inputs) rows=(1,(best,(r,direction))).
Proof.
 intros a hl hu ln ld un ud rows inputs n d b ib vn vd r direction HR HN HS.
 assert (HB:forall j,0<=j<rows -> Znth j b 0<rows+inputs).
 { intros j HJ. unfold simplex_solve_normal, simplex_solve_pack in HN.
   cbn zeta in HN.
   assert (HB:forall k,0<=k<rows -> 0<=Znth k b 0<inputs+rows /\ Znth (Znth k b 0) ib 0=1) by tauto.
   specialize (HB j HJ). lia. }
 apply (proj1 (simplex_find_violation_compute_iff _ _ _ _ _ _ _ HR HB)).
 exact HS.
Qed.
