From Coq Require Import ZArith List Lia.
From SimpleC.EE.Applications_human.simplex_find_entering Require Export simplex_find_entering_lib.
From SimpleC.EE.Applications_human.simplex_rat_add Require Export simplex_rat_add_lib.
Import ListNotations.
Local Open Scope Z_scope.
(* Exact checked rational arithmetic, ordered by column. None is arithmetic
   rejection, not mathematical infeasibility. A skipped zero coefficient
   performs no arithmetic and keeps the original fraction representation. *)
Definition simplex_recompute_column (ib an ad vn vd : list Z) (i : Z)
    (acc : option (Z*Z)) (j : Z) : option (Z*Z) :=
  match acc with
  | None => None
  | Some (n,d) =>
    if (negb (Z.eqb (Znth j ib 0) 0) || Z.eqb (Znth (i*24+j) an 0) 0)%bool
    then acc else
    let a := Znth (i*24+j) an 0 in let b := Znth (i*24+j) ad 0 in
    let c := Znth j vn 0 in let e := Znth j vd 0 in
    if Z.eqb (simplex_rat_mul_flag a b c e) 1 then
      let g := Z.gcd (Z.abs (a*c)) (b*e) in
      let p := Z.quot (a*c) g in let t := Z.quot (b*e) g in
      if Z.eqb (simplex_rat_add_flag n d p t) 1 then
        let h := Z.gcd (Z.abs (n*t+p*d)) (d*t) in
        Some (Z.quot (n*t+p*d) h, Z.quot (d*t) h)
      else None
    else None
  end.
Definition simplex_recompute_row (ib an ad vn vd rn rd : list Z) (i cols : Z) :=
  fold_left (simplex_recompute_column ib an ad vn vd i) (Zrange 0 cols)
    (Some (Znth i rn 0, Znth i rd 0)).
(* Row commit is atomic in the public state: rejection retains all previous
   commits. No basic-mark consistency or distinctness is assumed. Thus a later
   row reads the actual values written by earlier rows when indices overlap. *)
Definition simplex_recompute_commit (ib an ad rn rd basic : list Z) (cols : Z)
    (acc : Z*(list Z*list Z)) (i : Z) : Z*(list Z*list Z) :=
  let '(flag,(vn,vd)) := acc in
  if Z.eqb flag 1 then
    match simplex_recompute_row ib an ad vn vd rn rd i cols with
    | None => (0,(vn,vd))
    | Some (n,d) => (1,(replace_Znth (Znth i basic 0) n vn,
                         replace_Znth (Znth i basic 0) d vd))
    end
  else acc.
Definition simplex_recompute_compute (ib an ad rn rd basic vn vd : list Z) (rows cols : Z) :=
  fold_left (simplex_recompute_commit ib an ad rn rd basic cols) (Zrange 0 rows) (1,(vn,vd)).
Lemma simplex_recompute_row_step : forall ib an ad vn vd rn rd i j,
  0 <= j -> simplex_recompute_row ib an ad vn vd rn rd i (j+1) =
  simplex_recompute_column ib an ad vn vd i
    (simplex_recompute_row ib an ad vn vd rn rd i j) j.
Proof. intros. unfold simplex_recompute_row. rewrite simplex_scan_range_snoc by auto.
 rewrite fold_left_app. reflexivity. Qed.
Lemma simplex_recompute_compute_step : forall ib an ad rn rd basic vn vd i cols,
  0 <= i -> simplex_recompute_compute ib an ad rn rd basic vn vd (i+1) cols =
  simplex_recompute_commit ib an ad rn rd basic cols
    (simplex_recompute_compute ib an ad rn rd basic vn vd i cols) i.
Proof. intros. unfold simplex_recompute_compute. rewrite simplex_scan_range_snoc by auto.
 rewrite fold_left_app. reflexivity. Qed.
Lemma simplex_recompute_failed_fixed : forall ib an ad rn rd basic cols vn vd i,
 simplex_recompute_commit ib an ad rn rd basic cols (0,(vn,vd)) i = (0,(vn,vd)).
Proof. reflexivity. Qed.
Lemma simplex_recompute_empty : forall ib an ad rn rd basic vn vd cols,
 simplex_recompute_compute ib an ad rn rd basic vn vd 0 cols = (1,(vn,vd)).
Proof. reflexivity. Qed.
(* Active rational fields only: callers may frame every unused field and
   inactive array cell, including its exact prior initialization status. *)
From Coq Require Import String.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string_scope.
(* QCP emits this public name for local uninitialized SxRat objects. It is
   exactly the two writable member permissions used by the C annotations;
   no initialized values or assumptions about their prior bytes are added. *)
Definition UndefStructPredSxRat (p : Z) : Assertion :=
  &(p # "SxRat" ->ₛ "num") # Int |->_ **
  &(p # "SxRat" ->ₛ "den") # Int |->_ .
Lemma simplex_recompute_undef_rat_fields : forall p,
  UndefStructPredSxRat p =
  (&(p # "SxRat" ->ₛ "num") # Int |->_ **
   &(p # "SxRat" ->ₛ "den") # Int |->_).
Proof. reflexivity. Qed.

Definition simplex_recompute_values (s vars : Z) (vn vd : list Z) : Assertion :=
 iter_sepcon (map (fun j => simplex_scan_rat_memory s "value" j true
   (Znth j vn 0) (Znth j vd 0)) (Zrange 0 vars)).
Definition simplex_recompute_rhs (s rows : Z) (rn rd : list Z) : Assertion :=
 iter_sepcon (map (fun i => simplex_scan_rat_memory s "rhs" i true
   (Znth i rn 0) (Znth i rd 0)) (Zrange 0 rows)).
Definition simplex_recompute_cell (s : Z) (an ad : list Z) (i j : Z) : Assertion :=
 (&((((&((s) # "SxState" ->ₛ "a") + (i * (sizeof("SxRat") * 24))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> Znth (i*24+j) an 0 **
 (&((((&((s) # "SxState" ->ₛ "a") + (i * (sizeof("SxRat") * 24))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> Znth (i*24+j) ad 0.
Definition simplex_recompute_matrix (s rows vars : Z) (an ad : list Z) : Assertion :=
 iter_sepcon (map (fun i => iter_sepcon (map (simplex_recompute_cell s an ad i)
   (Zrange 0 vars))) (Zrange 0 rows)).

Local Open Scope Z_scope.
Definition simplex_recompute_prefix (ib an ad rn rd basic vn vd : list Z) (rows cols q : Z) (on od : list Z) : Prop :=
 simplex_recompute_compute ib an ad rn rd basic vn vd rows cols = (q,(on,od)).
Definition simplex_recompute_sum (ib an ad vn vd rn rd : list Z) (i cols n d : Z) : Prop :=
 simplex_recompute_row ib an ad vn vd rn rd i cols = Some (n,d).
Local Open Scope sac.
Definition simplex_recompute_values_except (s vars : Z) (vn vd : list Z) (j : Z) : Assertion :=
 iter_sepcon (remove_Znth j (map (fun k => simplex_scan_rat_memory s "value" k true
   (Znth k vn 0) (Znth k vd 0)) (Zrange 0 vars))).
Definition simplex_recompute_rhs_except (s rows : Z) (rn rd : list Z) (i : Z) : Assertion :=
 iter_sepcon (remove_Znth i (map (fun k => simplex_scan_rat_memory s "rhs" k true
   (Znth k rn 0) (Znth k rd 0)) (Zrange 0 rows))).
Definition simplex_recompute_matrix_except (s rows vars : Z) (an ad : list Z) (i j : Z) : Assertion :=
 iter_sepcon (remove_Znth i (map (fun k => iter_sepcon (map (simplex_recompute_cell s an ad k)
   (Zrange 0 vars))) (Zrange 0 rows))) **
 iter_sepcon (remove_Znth j (map (simplex_recompute_cell s an ad i) (Zrange 0 vars))).

Local Open Scope Z_scope.
(* Initialization calls use integer coefficients/RHS and all nonbasic values
   (0,1). This is a derived guarantee, never an extra public entry restriction. *)
Lemma simplex_recompute_column_integer_zero : forall ib an ad vn vd i j n,
 -2147483647 <= n <= 2147483647 ->
 -2147483647 <= Znth (i*24+j) an 0 <= 2147483647 ->
 Znth (i*24+j) ad 0 = 1 ->
 (Znth j ib 0 = 0 -> Znth j vn 0 = 0 /\ Znth j vd 0 = 1) ->
 simplex_recompute_column ib an ad vn vd i (Some(n,1)) j = Some(n,1).
Proof.
 intros ib an ad vn vd i j n Hn Ha Hd Hv.
 unfold simplex_recompute_column.
 destruct (Z.eqb (Znth j ib 0) 0) eqn:EB; simpl; [|reflexivity].
 destruct (Z.eqb (Znth (i*24+j) an 0) 0) eqn:EA; simpl; [reflexivity|].
 apply Z.eqb_eq in EB. destruct (Hv EB) as [HN HD].
 rewrite Hd, HN, HD.
 destruct (simplex_rat_mul_integer_zero _ Ha) as [HF _].
 rewrite HF. cbn [Z.eqb].
 replace (Znth (i*24+j) an 0 * 0) with 0 by ring.
 cbn. destruct (simplex_rat_add_integer_zero n Hn) as [HG _].
 rewrite HG. cbn [Z.eqb].
 rewrite Z.mul_1_r, Z.add_0_r, Z.gcd_1_r, !Z.quot_1_r. reflexivity.
Qed.
Lemma simplex_recompute_row_integer_zero : forall ib an ad vn vd rn rd i cols,
 0 <= cols -> -2147483647 <= Znth i rn 0 <= 2147483647 ->
 Znth i rd 0 = 1 ->
 (forall j, 0 <= j < cols ->
   -2147483647 <= Znth (i*24+j) an 0 <= 2147483647 /\
   Znth (i*24+j) ad 0 = 1 /\
   (Znth j ib 0 = 0 -> Znth j vn 0 = 0 /\ Znth j vd 0 = 1)) ->
 simplex_recompute_row ib an ad vn vd rn rd i cols = Some(Znth i rn 0,1).
Proof.
 intros ib an ad vn vd rn rd i cols HC HN HD HV.
 revert cols HC HV. refine (natlike_ind (fun cols => _) _ _).
 - intros. unfold simplex_recompute_row. simpl. rewrite HD. reflexivity.
 - intros k HK IH HV. replace (Z.succ k) with (k+1) by lia.
   rewrite simplex_recompute_row_step by auto.
   rewrite IH by (intros; apply HV; lia).
   destruct (HV k ltac:(lia)) as [HA [HAD HVAL]].
   apply simplex_recompute_column_integer_zero; auto.
Qed.

(* Complete initialization call: basic writes cannot disturb nonbasic zeros.
   Duplicated basic indices are allowed, but all written indices are flagged. *)
Theorem simplex_recompute_initialization_success : forall ib an ad rn rd basic vn vd rows cols,
 0 <= rows -> 0 <= cols -> Zlength vn = cols -> Zlength vd = cols ->
 (forall j, 0 <= j < cols -> Znth j ib 0 = 0 ->
    Znth j vn 0 = 0 /\ Znth j vd 0 = 1) ->
 (forall i, 0 <= i < rows ->
    0 <= Znth i basic 0 < cols /\ Znth (Znth i basic 0) ib 0 <> 0 /\
    -2147483647 <= Znth i rn 0 <= 2147483647 /\ Znth i rd 0 = 1 /\
    forall j, 0 <= j < cols ->
      -2147483647 <= Znth (i*24+j) an 0 <= 2147483647 /\ Znth (i*24+j) ad 0 = 1) ->
 exists on od, simplex_recompute_compute ib an ad rn rd basic vn vd rows cols = (1,(on,od)) /\
    Zlength on = cols /\ Zlength od = cols /\
    forall j, 0 <= j < cols -> Znth j ib 0 = 0 -> Znth j on 0 = 0 /\ Znth j od 0 = 1.
Proof.
 intros ib an ad rn rd basic vn vd rows cols HR HC HN HD HZERO.
 revert rows HR. refine (natlike_ind (fun rows => _) _ _).
 - intros. exists vn, vd. split; [reflexivity|]. split; [exact HN|]. split; [exact HD|exact HZERO].
 - intros k HK IH HROWS.
   destruct (IH ltac:(intros; apply HROWS; lia)) as [cn [cd [HE [HN' [HD' HZ]]]]].
   destruct (HROWS k ltac:(lia)) as [HB [HIB [HRN [HRD HA]]]].
   assert (HS : simplex_recompute_row ib an ad cn cd rn rd k cols = Some(Znth k rn 0,1)).
   { apply simplex_recompute_row_integer_zero; auto. intros j HJ.
     destruct (HA j HJ) as [H1 H2]. split; [exact H1|]. split; [exact H2|]. apply HZ; auto. }
   exists (replace_Znth (Znth k basic 0) (Znth k rn 0) cn),
          (replace_Znth (Znth k basic 0) 1 cd).
   split.
   + replace (Z.succ k) with (k+1) by lia.
     rewrite simplex_recompute_compute_step by auto.
     rewrite HE. unfold simplex_recompute_commit. rewrite HS. reflexivity.
   + rewrite !Zlength_replace_Znth. split; [exact HN'|]. split; [exact HD'|].
     intros j HJ HJIB. assert (HNE : Znth k basic 0 <> j) by (intros E; rewrite E in HIB; contradiction).
     rewrite !Znth_replace_Znth_Diff by lia. apply HZ; auto.
Qed.

(* Independent unchecked fraction sum: (N,D) denotes N/D. This fold uses
   only rational addition/multiplication, with no machine check or reduction. *)
Definition simplex_recompute_math_column (ib an ad vn vd:list Z) (i:Z) (acc:Z*Z) (j:Z) : Z*Z :=
 let '(N,D):=acc in
 if (negb (Z.eqb (Znth j ib 0) 0) || Z.eqb (Znth (i*24+j) an 0) 0)%bool then acc else
 let P:=Znth (i*24+j) an 0 * Znth j vn 0 in
 let E:=Znth (i*24+j) ad 0 * Znth j vd 0 in
 (N*E+P*D,D*E).
Definition simplex_recompute_math_row (ib an ad vn vd rn rd:list Z) (i cols:Z) :=
 fold_left (simplex_recompute_math_column ib an ad vn vd i) (Zrange 0 cols) (Znth i rn 0,Znth i rd 0).
Lemma simplex_recompute_math_row_step : forall ib an ad vn vd rn rd i j,
 0<=j -> simplex_recompute_math_row ib an ad vn vd rn rd i (j+1)=
 simplex_recompute_math_column ib an ad vn vd i (simplex_recompute_math_row ib an ad vn vd rn rd i j) j.
Proof. intros. unfold simplex_recompute_math_row. rewrite simplex_scan_range_snoc by auto. rewrite fold_left_app. reflexivity. Qed.
Lemma simplex_fraction_add_cross : forall n d N D p t P E r q : Z,
  0<d -> 0<t -> n*D=N*d -> p*E=P*t ->
  (n*t+p*d)*q=r*(d*t) ->
  (N*E+P*D)*q=r*(D*E).
Proof.
 intros n d N D p t P E r q Hd Ht Hn Hp Hsum.
 apply Z.mul_reg_r with (p:=d*t); [nia|].
 transitivity (((n*t+p*d)*q)*(D*E)).
 - replace (((N*E+P*D)*q)*(d*t)) with
     ((N*d)*E*q*t+(P*t)*D*q*d) by ring.
   rewrite <- Hn, <- Hp. ring.
 - rewrite Hsum. ring.
Qed.
Lemma simplex_recompute_column_math : forall ib an ad vn vd i j n d N D r q,
 0<d -> 0<D -> 0<Znth (i*24+j) ad 0 -> 0<Znth j vd 0 ->
 n*D=N*d -> simplex_recompute_column ib an ad vn vd i (Some(n,d)) j=Some(r,q) ->
 let '(rr,dd):=simplex_recompute_math_column ib an ad vn vd i (N,D) j in
 0<q /\ 0<dd /\ r*dd=rr*q.
Proof.
 intros ib an ad vn vd i j n d N D r q Hd HD Hb He Hcross Hstep.
 unfold simplex_recompute_column in Hstep.
 unfold simplex_recompute_math_column.
 destruct (negb (Z.eqb (Znth j ib 0) 0) || Z.eqb (Znth (i*24+j) an 0) 0)%bool eqn:HS.
 - inversion Hstep; subst. simpl. repeat split; auto.
 - cbn zeta in *.
   set (a:=Znth (i*24+j) an 0) in *.
   set (b:=Znth (i*24+j) ad 0) in *.
   set (c:=Znth j vn 0) in *.
   set (e:=Znth j vd 0) in *.
   destruct (Z.eqb (simplex_rat_mul_flag a b c e) 1) eqn:HM; [|discriminate].
   set (p:=Z.quot (a*c) (Z.gcd (Z.abs (a*c)) (b*e))) in *.
   set (t:=Z.quot (b*e) (Z.gcd (Z.abs (a*c)) (b*e))) in *.
   destruct (Z.eqb (simplex_rat_add_flag n d p t) 1) eqn:HA; [|discriminate].
   set (r0:=Z.quot (n*t+p*d) (Z.gcd (Z.abs (n*t+p*d)) (d*t))) in *.
   set (q0:=Z.quot (d*t) (Z.gcd (Z.abs (n*t+p*d)) (d*t))) in *.
   inversion Hstep; subst r q.
   assert (HRM:simplex_rat_mul_result a b c e p t) by (split; reflexivity).
   destruct (simplex_rat_mul_value a b c e p t Hb He HRM) as [Ht HVm].
   assert (HRA:simplex_rat_add_result n d p t r0 q0) by (split; reflexivity).
   destruct (simplex_rat_add_value n d p t r0 q0 Hd Ht HRA) as [Hq HVa].
   split; [exact Hq|]. split; [nia|].
   symmetry. apply (simplex_fraction_add_cross n d N D p t (a*c) (b*e) r0 q0 Hd Ht Hcross).
   + symmetry; exact HVm.
   + exact HVa.
Qed.

Theorem simplex_recompute_row_math : forall ib an ad vn vd rn rd i cols,
 0<=cols -> 0<Znth i rd 0 ->
 (forall j, 0<=j<cols -> 0<Znth (i*24+j) ad 0 /\ 0<Znth j vd 0) ->
 forall n d, simplex_recompute_row ib an ad vn vd rn rd i cols=Some(n,d) ->
 let '(nn,dd):=simplex_recompute_math_row ib an ad vn vd rn rd i cols in
 0<d /\ 0<dd /\ n*dd=nn*d.
Proof.
 intros ib an ad vn vd rn rd i cols HC HRD.
 revert cols HC. refine (natlike_ind (fun cols=>_) _ _).
 - intros HV n d HE. unfold simplex_recompute_row in HE. simpl in HE.
   inversion HE; subst. unfold simplex_recompute_math_row. simpl.
   repeat split; auto.
 - intros k HK IH HV n d HE.
   replace (Z.succ k) with (k+1) in HE by lia.
   rewrite simplex_recompute_row_step in HE by auto.
   destruct (simplex_recompute_row ib an ad vn vd rn rd i k) as [[nk dk]|] eqn:ER; [|discriminate].
   destruct (simplex_recompute_math_row ib an ad vn vd rn rd i k) as [Nk Dk] eqn:EM.
   assert (HVI:forall j,0<=j<k -> 0<Znth (i*24+j) ad 0 /\ 0<Znth j vd 0).
   { intros j HJ. apply HV. lia. }
   specialize (IH HVI nk dk eq_refl).
   destruct IH as [HD [HDK HCROSS]].
   replace (Z.succ k) with (k+1) by lia.
   rewrite simplex_recompute_math_row_step by auto. rewrite EM.
   destruct (HV k ltac:(lia)) as [HA HB].
   exact (simplex_recompute_column_math ib an ad vn vd i k nk dk Nk Dk n d HD HDK HA HB HCROSS HE).
Qed.


Lemma values_nth__row_commit : forall s v cn cd b,
 0 <= b < v -> Znth b (map (fun j => simplex_scan_rat_memory s "value" j true (Znth j cn 0) (Znth j cd 0)) (Zrange 0 v)) emp =
 simplex_scan_rat_memory s "value" b true (Znth b cn 0) (Znth b cd 0).
Proof. intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity. Qed.
Lemma values_focus__row_commit : forall s v cn cd b,
 0 <= b < v -> simplex_recompute_values s v cn cd |--
 simplex_scan_rat_memory s "value" b true (Znth b cn 0) (Znth b cd 0) ** simplex_recompute_values_except s v cn cd b.
Proof. intros. unfold simplex_recompute_values, simplex_recompute_values_except.
 pose proof (iter_sepcon_split_remove_Znth b (map (fun j => simplex_scan_rat_memory s "value" j true (Znth j cn 0) (Znth j cd 0)) (Zrange 0 v)) emp) as HS.
 rewrite values_nth__row_commit in HS by auto. apply HS. rewrite Zlength_map, simplex_scan_range_length; lia. Qed.
Lemma values_store__row_commit : forall s v cn cd b n d,
 Zlength cn = v -> Zlength cd = v -> 0 <= b < v ->
 simplex_scan_rat_memory s "value" b true n d ** simplex_recompute_values_except s v cn cd b |--
 simplex_recompute_values s v (replace_Znth b n cn) (replace_Znth b d cd).
Proof.
 intros s v cn cd b n d HN HD HB. unfold simplex_recompute_values, simplex_recompute_values_except.
 pose proof (iter_sepcon_merge_remove_Znth b (map (fun j => simplex_scan_rat_memory s "value" j true (Znth j cn 0) (Znth j cd 0)) (Zrange 0 v)) (simplex_scan_rat_memory s "value" b true n d)) as HM.
 assert (HE : map (fun j => simplex_scan_rat_memory s "value" j true (Znth j (replace_Znth b n cn) 0) (Znth j (replace_Znth b d cd) 0)) (Zrange 0 v) = replace_Znth b (simplex_scan_rat_memory s "value" b true n d) (map (fun j => simplex_scan_rat_memory s "value" j true (Znth j cn 0) (Znth j cd 0)) (Zrange 0 v))).
 { apply (proj2 (list_eq_ext _ _ emp)). rewrite !Zlength_map, Zlength_replace_Znth, Zlength_map. split; [reflexivity|].
   intros k HK. rewrite simplex_scan_range_length in HK by lia.
   destruct (Z.eq_dec b k) as [E|E].
   - subst k. rewrite Znth_replace_Znth_Same by (rewrite Zlength_map, simplex_scan_range_length; lia).
     rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
     rewrite simplex_scan_range_nth by lia. rewrite !Znth_replace_Znth_Same by lia. reflexivity.
   - rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_map, ?simplex_scan_range_length; lia).
     rewrite !(Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
     rewrite !simplex_scan_range_nth by lia. rewrite !Znth_replace_Znth_Diff by lia. reflexivity.
   all: try (rewrite simplex_scan_range_length; lia).
 }
 rewrite HE. apply HM. rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma forall_replace__row_commit : forall (P:Z->Prop) l b n,
 Forall P l -> P n -> Forall P (replace_Znth b n l).
Proof. intros P l b n H HN. unfold replace_Znth. remember (Z.to_nat b) as k. clear Heqk b. revert k. induction H; intros k; destruct k; simpl; constructor; auto. Qed.
Lemma values_nth__entry_focus : forall s v cn cd b,
 0 <= b < v -> Znth b (map (fun j => simplex_scan_rat_memory s "value" j true (Znth j cn 0) (Znth j cd 0)) (Zrange 0 v)) emp =
 simplex_scan_rat_memory s "value" b true (Znth b cn 0) (Znth b cd 0).
Proof. intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity. Qed.
Lemma values_focus__entry_focus : forall s v cn cd b,
 0 <= b < v -> simplex_recompute_values s v cn cd |--
 simplex_scan_rat_memory s "value" b true (Znth b cn 0) (Znth b cd 0) ** simplex_recompute_values_except s v cn cd b.
Proof. intros. unfold simplex_recompute_values, simplex_recompute_values_except.
 pose proof (iter_sepcon_split_remove_Znth b (map (fun j => simplex_scan_rat_memory s "value" j true (Znth j cn 0) (Znth j cd 0)) (Zrange 0 v)) emp) as HS.
 rewrite values_nth__entry_focus in HS by auto. apply HS. rewrite Zlength_map, simplex_scan_range_length; lia. Qed.
Lemma rhs_nth__entry_focus : forall s v cn cd b,
 0 <= b < v -> Znth b (map (fun j => simplex_scan_rat_memory s "rhs" j true (Znth j cn 0) (Znth j cd 0)) (Zrange 0 v)) emp =
 simplex_scan_rat_memory s "rhs" b true (Znth b cn 0) (Znth b cd 0).
Proof. intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity. Qed.
Lemma rhs_focus__entry_focus : forall s v cn cd b,
 0 <= b < v -> simplex_recompute_rhs s v cn cd |--
 simplex_scan_rat_memory s "rhs" b true (Znth b cn 0) (Znth b cd 0) ** simplex_recompute_rhs_except s v cn cd b.
Proof. intros. unfold simplex_recompute_rhs, simplex_recompute_rhs_except.
 pose proof (iter_sepcon_split_remove_Znth b (map (fun j => simplex_scan_rat_memory s "rhs" j true (Znth j cn 0) (Znth j cd 0)) (Zrange 0 v)) emp) as HS.
 rewrite rhs_nth__entry_focus in HS by auto. apply HS. rewrite Zlength_map, simplex_scan_range_length; lia. Qed.
Lemma rhs_merge__entry_focus : forall s v cn cd b,
 0 <= b < v ->
 simplex_scan_rat_memory s "rhs" b true (Znth b cn 0) (Znth b cd 0) ** simplex_recompute_rhs_except s v cn cd b |-- simplex_recompute_rhs s v cn cd.
Proof. intros. unfold simplex_recompute_rhs, simplex_recompute_rhs_except.
 pose proof (iter_sepcon_merge_remove_Znth b (map (fun j => simplex_scan_rat_memory s "rhs" j true (Znth j cn 0) (Znth j cd 0)) (Zrange 0 v)) (simplex_scan_rat_memory s "rhs" b true (Znth b cn 0) (Znth b cd 0))) as HM.
 rewrite <- (rhs_nth__entry_focus s v cn cd b H) in HM.
 rewrite replace_Znth_Znth in HM. rewrite (rhs_nth__entry_focus s v cn cd b H) in HM. apply HM. rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma forall_nth__entry_focus : forall (P:Z->Prop) l i,
 Forall P l -> 0 <= i < Zlength l -> P (Znth i l 0).
Proof. intros P l i HF. revert i. induction HF; intros i Hi.
 - rewrite Zlength_nil in Hi. lia.
 - rewrite Zlength_cons in Hi. destruct (Z.eq_dec i 0).
   + subst. rewrite Znth0_cons. assumption.
   + rewrite Znth_cons by lia. apply IHHF. lia.
Qed.
Lemma matrix_focus__entry_focus : forall s r v an ad i j,
 0 <= i < r -> 0 <= j < v ->
 simplex_recompute_matrix s r v an ad |--
 simplex_recompute_cell s an ad i j ** simplex_recompute_matrix_except s r v an ad i j.
Proof.
 intros s r v an ad i j HI HJ.
 unfold simplex_recompute_matrix, simplex_recompute_matrix_except.
 pose proof (iter_sepcon_split_remove_Znth i (map (fun k => iter_sepcon (map (simplex_recompute_cell s an ad k) (Zrange 0 v))) (Zrange 0 r)) emp) as HO.
 rewrite (Znth_map _ _ _ 0 emp) in HO by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth in HO by lia.
 sep_apply_l_atomic (HO ltac:(rewrite Zlength_map, simplex_scan_range_length; lia)).
 pose proof (iter_sepcon_split_remove_Znth j (map (simplex_recompute_cell s an ad i) (Zrange 0 v)) emp) as HC.
 rewrite (Znth_map _ _ _ 0 emp) in HC by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth in HC by lia.
 sep_apply_l_atomic (HC ltac:(rewrite Zlength_map, simplex_scan_range_length; lia)).
 cancel. reflexivity.
Qed.
Lemma range_merge__column_success : forall (f:Z->Assertion) v j,
 0<=j<v -> f j ** iter_sepcon (remove_Znth j (map f (Zrange 0 v))) |-- iter_sepcon (map f (Zrange 0 v)).
Proof.
 intros f v j H.
 assert (HN:Znth j (map f (Zrange 0 v)) emp=f j).
 { rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
   rewrite simplex_scan_range_nth by lia. reflexivity. }
 pose proof (iter_sepcon_merge_remove_Znth j (map f (Zrange 0 v)) (f j)) as HM.
 rewrite <- HN in HM. rewrite replace_Znth_Znth in HM. rewrite HN in HM.
 apply HM. rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma column_success_step__column_success : forall ib an ad cn cd rn rd i j n d p q x y,
 0<=j -> simplex_recompute_sum ib an ad cn cd rn rd i j n d ->
 Znth j ib 0=0 -> Znth (i*24+j) an 0<>0 ->
 simplex_rat_mul_flag (Znth (i*24+j) an 0) (Znth (i*24+j) ad 0) (Znth j cn 0) (Znth j cd 0)=1 ->
 simplex_rat_mul_result (Znth (i*24+j) an 0) (Znth (i*24+j) ad 0) (Znth j cn 0) (Znth j cd 0) p q ->
 simplex_rat_add_flag n d p q=1 -> simplex_rat_add_result n d p q x y ->
 simplex_recompute_sum ib an ad cn cd rn rd i (j+1) x y.
Proof.
 intros ib an ad cn cd rn rd i j n d p q x y HJ HR HI HA HM HP HF HX.
 unfold simplex_recompute_sum in *. rewrite simplex_recompute_row_step by auto.
 rewrite HR. unfold simplex_recompute_column. rewrite HI, Z.eqb_refl. simpl.
 rewrite (proj2 (Z.eqb_neq _ _) HA). simpl. rewrite HM. simpl.
 unfold simplex_rat_mul_result, simplex_rat_reduce_result in HP. destruct HP as [HP HQ].
 rewrite <- HP, <- HQ. rewrite HF. simpl.
 unfold simplex_rat_add_result, simplex_rat_reduce_result in HX. destruct HX as [HX HY].
 rewrite <- HX, <- HY. reflexivity.
Qed.
Lemma matrix_merge__column_success : forall s r v an ad i j,
 0<=i<r -> 0<=j<v ->
 simplex_recompute_cell s an ad i j ** simplex_recompute_matrix_except s r v an ad i j |-- simplex_recompute_matrix s r v an ad.
Proof.
 intros. unfold simplex_recompute_matrix_except, simplex_recompute_matrix.
 sep_apply (range_merge__column_success (simplex_recompute_cell s an ad i) v j H0).
 sep_apply (range_merge__column_success (fun k=>iter_sepcon (map (simplex_recompute_cell s an ad k) (Zrange 0 v))) r i H).
 reflexivity.
Qed.
Lemma values_merge__column_success : forall s v cn cd j,
 0<=j<v -> simplex_scan_rat_memory s "value" j true (Znth j cn 0) (Znth j cd 0) **
 simplex_recompute_values_except s v cn cd j |-- simplex_recompute_values s v cn cd.
Proof.
 intros. unfold simplex_recompute_values_except, simplex_recompute_values.
 exact (range_merge__column_success (fun k=>simplex_scan_rat_memory s "value" k true (Znth k cn 0) (Znth k cd 0)) v j H).
Qed.
Lemma range_merge__skip_bounds : forall (f:Z->Assertion) n i,
  0 <= i < n ->
  f i ** iter_sepcon (remove_Znth i (map f (Zrange 0 n))) |--
  iter_sepcon (map f (Zrange 0 n)).
Proof.
 intros f n i HI.
 pose proof (iter_sepcon_merge_remove_Znth i (map f (Zrange 0 n)) (f i)) as HM.
 assert (HE:Znth i (map f (Zrange 0 n)) emp = f i).
 { rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
   rewrite simplex_scan_range_nth by lia. reflexivity. }
 rewrite <- HE in HM. rewrite replace_Znth_Znth in HM by (rewrite Zlength_map, simplex_scan_range_length; lia).
 rewrite HE in HM. apply HM. rewrite Zlength_map, simplex_scan_range_length; lia.
Qed.
Lemma matrix_merge__skip_bounds : forall s r v an ad i j,
 0<=i<r -> 0<=j<v ->
 simplex_recompute_cell s an ad i j ** simplex_recompute_matrix_except s r v an ad i j |--
 simplex_recompute_matrix s r v an ad.
Proof.
 intros s r v an ad i j HI HJ.
 unfold simplex_recompute_matrix, simplex_recompute_matrix_except.
 sep_apply_r_atomic (range_merge__skip_bounds
 (fun k=>iter_sepcon(map (simplex_recompute_cell s an ad k) (Zrange 0 v))) r i HI).
 sep_apply_r_atomic (range_merge__skip_bounds (simplex_recompute_cell s an ad i) v j HJ).
 sepcon_right_assoc. cancel. reflexivity.
Qed.
Lemma values_merge__skip_bounds : forall s v cn cd j,
 0<=j<v ->
 simplex_scan_rat_memory s "value" j true (Znth j cn 0) (Znth j cd 0) **
 simplex_recompute_values_except s v cn cd j |-- simplex_recompute_values s v cn cd.
Proof.
 intros. unfold simplex_recompute_values, simplex_recompute_values_except.
 exact (range_merge__skip_bounds (fun k=>simplex_scan_rat_memory s "value" k true (Znth k cn 0) (Znth k cd 0)) v j H).
Qed.
Lemma forall_nth__skip_bounds : forall (P:Z->Prop) l i,
 Forall P l -> 0<=i<Zlength l -> P (Znth i l 0).
Proof.
 intros P l i HF HI. apply Forall_forall with (x:=Znth i l 0) in HF; auto.
 unfold Znth. apply nth_In. rewrite Zlength_correct in HI. lia.
Qed.
Lemma row_skip__skip_bounds : forall ib an ad cn cd rn rd i j n d,
 0<=j -> (Znth j ib 0 <> 0 \/ Znth (i*24+j) an 0=0) ->
 simplex_recompute_sum ib an ad cn cd rn rd i j n d ->
 simplex_recompute_sum ib an ad cn cd rn rd i (j+1) n d.
Proof.
 intros ib an ad cn cd rn rd i j n d HJ HS HH.
 unfold simplex_recompute_sum in *.
 rewrite simplex_recompute_row_step by auto. rewrite HH.
 unfold simplex_recompute_column.
 destruct HS as [HB|HA].
 - rewrite (proj2 (Z.eqb_neq _ _) HB). simpl. reflexivity.
 - rewrite HA, Z.eqb_refl. rewrite Bool.orb_true_r. reflexivity.
Qed.
Lemma row_none_extend__failure_exit : forall ib an ad cn cd rn rd i t,
 0<=t -> simplex_recompute_row ib an ad cn cd rn rd i t=None ->
 forall k, 0<=k -> simplex_recompute_row ib an ad cn cd rn rd i (t+k)=None.
Proof. intros ib an ad cn cd rn rd i t HT HE.
 refine (natlike_ind (fun k=>simplex_recompute_row ib an ad cn cd rn rd i (t+k)=None) _ _).
 - replace (t+0) with t by lia. exact HE.
 - intros k HK IH. replace (t+Z.succ k) with ((t+k)+1) by lia.
   rewrite simplex_recompute_row_step by lia. rewrite IH. reflexivity.
Qed.
Lemma row_failure_suffix__failure_exit : forall ib an ad cn cd rn rd i j v n d,
 0<=j<v -> simplex_recompute_row ib an ad cn cd rn rd i j=Some(n,d) ->
 simplex_recompute_column ib an ad cn cd i (Some(n,d)) j=None ->
 simplex_recompute_row ib an ad cn cd rn rd i v=None.
Proof. intros. assert (HE:simplex_recompute_row ib an ad cn cd rn rd i (j+1)=None).
 { rewrite simplex_recompute_row_step by lia. rewrite H0. exact H1. }
 replace v with ((j+1)+(v-(j+1))) by lia.
 apply row_none_extend__failure_exit; auto; lia.
Qed.
Lemma compute_zero_extend__failure_exit : forall ib an ad rn rd b vn vd t v cn cd,
 0<=t -> simplex_recompute_compute ib an ad rn rd b vn vd t v=(0,(cn,cd)) ->
 forall k,0<=k -> simplex_recompute_compute ib an ad rn rd b vn vd (t+k) v=(0,(cn,cd)).
Proof. intros ib an ad rn rd b vn vd t v cn cd HT HE.
 refine (natlike_ind (fun k=>simplex_recompute_compute ib an ad rn rd b vn vd (t+k) v=(0,(cn,cd))) _ _).
 - replace (t+0) with t by lia. exact HE.
 - intros k HK IH. replace (t+Z.succ k) with ((t+k)+1) by lia.
   rewrite simplex_recompute_compute_step by lia. rewrite IH. reflexivity.
Qed.
Lemma compute_failure_suffix__failure_exit : forall ib an ad rn rd b vn vd i r v cn cd,
 0<=i<r -> simplex_recompute_compute ib an ad rn rd b vn vd i v=(1,(cn,cd)) ->
 simplex_recompute_row ib an ad cn cd rn rd i v=None ->
 simplex_recompute_compute ib an ad rn rd b vn vd r v=(0,(cn,cd)).
Proof. intros. assert (HE:simplex_recompute_compute ib an ad rn rd b vn vd (i+1) v=(0,(cn,cd))).
 { rewrite simplex_recompute_compute_step by lia. rewrite H0.
   unfold simplex_recompute_commit. rewrite H1. reflexivity. }
 replace r with ((i+1)+(r-(i+1))) by lia.
 apply compute_zero_extend__failure_exit; auto; lia.
Qed.
Lemma range_merge__failure_exit : forall (f:Z->Assertion) len k,
 0<=k<len ->
 f k ** iter_sepcon (remove_Znth k (map f (Zrange 0 len))) |-- iter_sepcon (map f (Zrange 0 len)).
Proof.
 intros f len k HK.
 pose proof (iter_sepcon_merge_remove_Znth k (map f (Zrange 0 len)) (f k)) as HM.
 assert (HE:replace_Znth k (f k) (map f (Zrange 0 len))=map f (Zrange 0 len)).
 { apply (proj2 (list_eq_ext _ _ emp)). rewrite Zlength_replace_Znth. split;[reflexivity|].
   intros x HX. rewrite Zlength_map, simplex_scan_range_length in HX by lia.
   destruct (Z.eq_dec k x) as [E|E].
   - subst x. rewrite Znth_replace_Znth_Same by (rewrite Zlength_map, simplex_scan_range_length;lia).
     rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length;lia).
     rewrite simplex_scan_range_nth by lia. reflexivity.
   - rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_map, ?simplex_scan_range_length;lia). reflexivity. }
 rewrite <- HE at 2. apply HM. rewrite Zlength_map, simplex_scan_range_length;lia.
Qed.
Lemma matrix_merge__failure_exit : forall s r v an ad i j,
 0<=i<r -> 0<=j<v ->
 simplex_recompute_cell s an ad i j ** simplex_recompute_matrix_except s r v an ad i j |--
 simplex_recompute_matrix s r v an ad.
Proof.
 intros. unfold simplex_recompute_matrix, simplex_recompute_matrix_except.
 sep_apply_l_atomic (range_merge__failure_exit (simplex_recompute_cell s an ad i) v j H0).
 sep_apply_l_atomic (range_merge__failure_exit (fun k=>iter_sepcon (map (simplex_recompute_cell s an ad k) (Zrange 0 v))) r i H).
 reflexivity.
Qed.
Lemma values_merge__failure_exit : forall s v cn cd j,
 0<=j<v -> simplex_scan_rat_memory s "value" j true (Znth j cn 0) (Znth j cd 0) **
 simplex_recompute_values_except s v cn cd j |-- simplex_recompute_values s v cn cd.
Proof. intros. unfold simplex_recompute_values, simplex_recompute_values_except.
 apply (range_merge__failure_exit (fun k=>simplex_scan_rat_memory s "value" k true (Znth k cn 0) (Znth k cd 0)) v j H).
Qed.
Lemma column_mul_fail__failure_exit : forall ib an ad cn cd i j n d,
 Znth j ib 0=0 -> Znth (i*24+j) an 0<>0 ->
 simplex_rat_mul_flag (Znth (i*24+j) an 0) (Znth (i*24+j) ad 0) (Znth j cn 0) (Znth j cd 0)=0 ->
 simplex_recompute_column ib an ad cn cd i (Some(n,d)) j=None.
Proof. intros. unfold simplex_recompute_column. rewrite H, Z.eqb_refl.
 rewrite (proj2 (Z.eqb_neq _ _) H0). simpl. rewrite H1. reflexivity. Qed.
Lemma column_add_fail__failure_exit : forall ib an ad cn cd i j n d p t,
 Znth j ib 0=0 -> Znth (i*24+j) an 0<>0 ->
 simplex_rat_mul_flag (Znth (i*24+j) an 0) (Znth (i*24+j) ad 0) (Znth j cn 0) (Znth j cd 0)=1 ->
 simplex_rat_mul_result (Znth (i*24+j) an 0) (Znth (i*24+j) ad 0) (Znth j cn 0) (Znth j cd 0) p t ->
 simplex_rat_add_flag n d p t=0 ->
 simplex_recompute_column ib an ad cn cd i (Some(n,d)) j=None.
Proof. intros ib an ad cn cd i j n d p t HI HA HM HR HF.
 unfold simplex_rat_mul_result, simplex_rat_reduce_result in HR. destruct HR as [HP HT].
 unfold simplex_recompute_column. rewrite HI, Z.eqb_refl, (proj2 (Z.eqb_neq _ _) HA). simpl.
 rewrite HM. simpl. rewrite <- HP, <- HT, HF. reflexivity. Qed.
