From Coq Require Import ZArith List Lia.
From SimpleC.EE.Applications_human.simplex_recompute Require Export simplex_recompute_lib.
From SimpleC.EE.Applications_human.simplex_rat_div Require Export simplex_rat_div_lib.
Import ListNotations.
Local Open Scope Z_scope.
(* Public exact checked pivot semantics. Numerator/denominator lists address
   rhs slots 0..15 and matrix slots 16+24*i+j. Only active slots represent
   owned C fields; padding is logical scratch, never a claim to read bytes.
   Arithmetic order and failure commits are observable parts of this API. *)
Definition simplex_pivot_num (x:Z*Z) := fst x.
Definition simplex_pivot_den (x:Z*Z) := snd x.
Definition simplex_pivot_state := (Z*(list Z*list Z))%type.
Definition simplex_pivot_at (n d:list Z) (k:Z) : Z*Z := (Znth k n 0,Znth k d 1).
Definition simplex_pivot_put (k a b:Z) (s:simplex_pivot_state) : simplex_pivot_state :=
 let '(q,(n,d)):=s in (q,(replace_Znth k a n,replace_Znth k b d)).
Definition simplex_pivot_stop (s:simplex_pivot_state) : simplex_pivot_state :=
 let '(_,x):=s in (0,x).
Definition simplex_pivot_div (pn pd k:Z) (neg:bool) (s:simplex_pivot_state) :=
 let '(q,(n,d)):=s in if Z.eqb q 1 then
 let a:=Znth k n 0 in let b:=Znth k d 1 in
 if Z.eqb (simplex_rat_div_flag a b pn pd) 1 then
 let nn:=a*pd in let dd:=b*pn in
 let nn:=if Z.ltb dd 0 then -nn else nn in
 let dd:=Z.abs dd in let g:=Z.gcd (Z.abs nn) dd in
 let u:=Z.quot nn g in let v:=Z.quot dd g in
 simplex_pivot_put k (if neg then -u else u) v s
 else simplex_pivot_stop s else s.
Definition simplex_pivot_recip (pn pd k:Z) (s:simplex_pivot_state) :=
 let '(q,(n,d)):=s in if Z.eqb q 1 then
 if Z.eqb (simplex_rat_div_flag 1 1 pn pd) 1 then
 let nn:=if Z.ltb pn 0 then -pd else pd in
 let dd:=Z.abs pn in let g:=Z.gcd (Z.abs nn) dd in
 simplex_pivot_put k (Z.quot nn g) (Z.quot dd g) s
 else simplex_pivot_stop s else s.
Definition simplex_pivot_zero (k:Z) (s:simplex_pivot_state) :=
 if Z.eqb (fst s) 1 then simplex_pivot_put k 0 1 s else s.
(* term is local: a rejected product/addition cannot change its target. *)
Definition simplex_pivot_addmul (fnum fden src dst:Z) (s:simplex_pivot_state) :=
 let '(q,(n,d)):=s in if Z.eqb q 1 then
 let a:=Znth src n 0 in let b:=Znth src d 1 in
 if Z.eqb (simplex_rat_mul_flag fnum fden a b) 1 then
 let g:=Z.gcd (Z.abs (fnum*a)) (fden*b) in
 let p:=Z.quot (fnum*a) g in let t:=Z.quot (fden*b) g in
 let x:=Znth dst n 0 in let y:=Znth dst d 1 in
 if Z.eqb (simplex_rat_add_flag x y p t) 1 then
 let nn:=x*t+p*y in let dd:=y*t in let h:=Z.gcd (Z.abs nn) dd in
 simplex_pivot_put dst (Z.quot nn h) (Z.quot dd h) s
 else simplex_pivot_stop s else simplex_pivot_stop s else s.
Definition simplex_pivot_row_column (pn pd r e:Z) (s:simplex_pivot_state) (j:Z) :=
 if Z.eqb j e then s else simplex_pivot_div pn pd (16+r*24+j) true s.
Definition simplex_pivot_row_prefix (pn pd r e cols:Z) (s:simplex_pivot_state) :=
 fold_left (simplex_pivot_row_column pn pd r e) (Zrange 0 cols) s.
Definition simplex_pivot_other_column (fnum fden r i e:Z) (s:simplex_pivot_state) (j:Z) :=
 if Z.eqb j e then s else simplex_pivot_addmul fnum fden (16+r*24+j) (16+i*24+j) s.
Definition simplex_pivot_other_prefix (fnum fden r i e cols:Z) (s:simplex_pivot_state) :=
 fold_left (simplex_pivot_other_column fnum fden r i e) (Zrange 0 cols) s.
Definition simplex_pivot_other_row (r e cols:Z) (s:simplex_pivot_state) (i:Z) :=
 if Z.eqb i r then s else
 let '(q,(n,d)):=s in if Z.eqb q 1 then
 let fnum:=Znth (16+i*24+e) n 0 in let fden:=Znth (16+i*24+e) d 1 in
 let t:=if Z.eqb fnum 0 then s else
 simplex_pivot_other_prefix fnum fden r i e cols (simplex_pivot_addmul fnum fden r i s) in
 simplex_pivot_zero (16+i*24+e) t else s.
Definition simplex_pivot_rows_prefix (r e cols rows:Z) (s:simplex_pivot_state) :=
 fold_left (simplex_pivot_other_row r e cols) (Zrange 0 rows) s.
Definition simplex_pivot_compute (n d:list Z) (rows cols r e leaving:Z) :=
 let pn:=Znth (16+r*24+e) n 0 in let pd:=Znth (16+r*24+e) d 1 in
 let s:=(1,(n,d)) in
 let s:=simplex_pivot_div pn pd r true s in
 let s:=simplex_pivot_row_prefix pn pd r e cols s in
 let s:=simplex_pivot_recip pn pd (16+r*24+leaving) s in
 let s:=simplex_pivot_zero (16+r*24+e) s in
 simplex_pivot_rows_prefix r e cols rows s.
Definition simplex_pivot_result (n d:list Z) (rows cols r e leaving q:Z) (on od:list Z) : Prop :=
 simplex_pivot_compute n d rows cols r e leaving=(q,(on,od)).
Lemma simplex_pivot_div_failed : forall pn pd k neg n d,
 simplex_pivot_div pn pd k neg (0,(n,d))=(0,(n,d)).
Proof. reflexivity. Qed.
Lemma simplex_pivot_addmul_failed : forall fnum fden src dst n d,
 simplex_pivot_addmul fnum fden src dst (0,(n,d))=(0,(n,d)).
Proof. reflexivity. Qed.
Lemma simplex_pivot_row_step : forall pn pd r e j s, 0<=j ->
 simplex_pivot_row_prefix pn pd r e (j+1) s=
 simplex_pivot_row_column pn pd r e (simplex_pivot_row_prefix pn pd r e j s) j.
Proof. intros. unfold simplex_pivot_row_prefix. rewrite simplex_scan_range_snoc by auto.
 rewrite fold_left_app. reflexivity. Qed.
Lemma simplex_pivot_other_step : forall fnum fden r i e j s, 0<=j ->
 simplex_pivot_other_prefix fnum fden r i e (j+1) s=
 simplex_pivot_other_column fnum fden r i e (simplex_pivot_other_prefix fnum fden r i e j s) j.
Proof. intros. unfold simplex_pivot_other_prefix. rewrite simplex_scan_range_snoc by auto.
 rewrite fold_left_app. reflexivity. Qed.
Lemma simplex_pivot_rows_step : forall r e cols i s, 0<=i ->
 simplex_pivot_rows_prefix r e cols (i+1) s=
 simplex_pivot_other_row r e cols (simplex_pivot_rows_prefix r e cols i s) i.
Proof. intros. unfold simplex_pivot_rows_prefix. rewrite simplex_scan_range_snoc by auto.
 rewrite fold_left_app. reflexivity. Qed.

(* Logical slots enumerate actual footprint only. They do not flatten the
   physical rhs and a objects into one C array. *)
Definition simplex_pivot_slots (rows cols:Z) : list Z :=
 Zrange 0 rows ++ flat_map (fun i => map (fun j => 16+i*24+j) (Zrange 0 cols)) (Zrange 0 rows).
Definition simplex_pivot_pad (default:Z) (rows cols:Z) (n:list Z) : list Z :=
 map (fun k => if existsb (Z.eqb k) (simplex_pivot_slots rows cols)
               then Znth k n default else default) (Zrange 0 400).
Lemma simplex_pivot_pad_length : forall v rows cols n,
 Zlength (simplex_pivot_pad v rows cols n)=400.
Proof. intros. unfold simplex_pivot_pad. rewrite Zlength_map, simplex_scan_range_length by lia. lia. Qed.
Lemma simplex_pivot_slots_bounds : forall rows cols k,
 0<=rows<=16 -> 0<=cols<=24 -> In k (simplex_pivot_slots rows cols) -> 0<=k<400.
Proof.
 intros rows cols k Hr Hc H. unfold simplex_pivot_slots in H.
 apply in_app_or in H. destruct H as [H|H].
 - apply In_Zrange in H. lia.
 - apply in_flat_map in H. destruct H as [i [Hi Hk]].
   apply in_map_iff in Hk. destruct Hk as [j [<- Hj]].
   apply In_Zrange in Hi. apply In_Zrange in Hj. nia.
Qed.
Lemma simplex_pivot_pad_active : forall v rows cols n k,
 0<=rows<=16 -> 0<=cols<=24 -> In k (simplex_pivot_slots rows cols) ->
 Znth k (simplex_pivot_pad v rows cols n) v=Znth k n v.
Proof.
 intros v rows cols n k Hr Hc Hk.
 pose proof (simplex_pivot_slots_bounds rows cols k Hr Hc Hk) as Hbound.
 unfold simplex_pivot_pad. rewrite (Znth_map _ _ _ 0 v) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia.
 assert (E:existsb (Z.eqb k) (simplex_pivot_slots rows cols)=true).
 { apply existsb_exists. exists k. split; auto. apply Z.eqb_refl. }
 rewrite E. reflexivity.
Qed.
(* Stage interfaces expose only actual changed arrays and fixed entry pivot.
   A failed state is absorbing in every later phase. *)
Definition simplex_pivot_start (n d:list Z) (r e:Z) :=
 simplex_pivot_div (Znth (16+r*24+e) n 0) (Znth (16+r*24+e) d 1) r true (1,(n,d)).
Definition simplex_pivot_before_rows (n d:list Z) (cols r e leaving:Z) :=
 let pn:=Znth (16+r*24+e) n 0 in let pd:=Znth (16+r*24+e) d 1 in
 simplex_pivot_zero (16+r*24+e)
  (simplex_pivot_recip pn pd (16+r*24+leaving)
   (simplex_pivot_row_prefix pn pd r e cols (simplex_pivot_start n d r e))).
Definition simplex_pivot_row_progress (n d:list Z) (r e j:Z) (cn cd:list Z) : Prop :=
 simplex_pivot_row_prefix (Znth (16+r*24+e) n 0) (Znth (16+r*24+e) d 1) r e j
  (simplex_pivot_start n d r e)=(1,(cn,cd)).
Definition simplex_pivot_rows_progress (n d:list Z) (cols r e leaving i:Z) (cn cd:list Z) : Prop :=
 simplex_pivot_rows_prefix r e cols i (simplex_pivot_before_rows n d cols r e leaving)=(1,(cn,cd)).
Definition simplex_pivot_columns_progress (n d:list Z) (cols r e leaving i j fnum fden:Z)
 (cn cd:list Z) : Prop :=
 simplex_pivot_other_prefix fnum fden r i e j
  (simplex_pivot_addmul fnum fden r i
   (simplex_pivot_rows_prefix r e cols i (simplex_pivot_before_rows n d cols r e leaving)))=(1,(cn,cd)).
From Coq Require Import String.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string_scope.
(* Physical native cell addresses; rhs and a remain distinct named fields. *)
Definition simplex_pivot_memory_cell (s k n d:Z) : Assertion :=
 if Z.ltb k 16 then simplex_scan_rat_memory s "rhs" k true n d else
 let i:=(k-16)/24 in let j:=(k-16) mod 24 in
 (&((((&((s) # "SxState" ->ₛ "a") + (i * (sizeof("SxRat") * 24))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> n **
 (&((((&((s) # "SxState" ->ₛ "a") + (i * (sizeof("SxRat") * 24))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> d.
Definition simplex_pivot_memory (s rows cols:Z) (n d:list Z) : Assertion :=
 iter_sepcon (map (fun k => simplex_pivot_memory_cell s k (Znth k n 0) (Znth k d 1))
  (simplex_pivot_slots rows cols)).
Definition simplex_pivot_except (s rows cols:Z) (n d:list Z) (k1 k2:Z) : Assertion :=
 iter_sepcon (map (fun k => simplex_pivot_memory_cell s k (Znth k n 0) (Znth k d 1))
  (filter (fun k => negb (Z.eqb k k1 || Z.eqb k k2)) (simplex_pivot_slots rows cols))).

Local Open Scope Z_scope.
Definition simplex_pivot_basis (b:list Z) (r e q:Z) := if Z.eqb q 1 then replace_Znth r e b else b.
Definition simplex_pivot_marks (ib:list Z) (leaving e q:Z) := if Z.eqb q 1 then replace_Znth e 1 (replace_Znth leaving 0 ib) else ib.
Lemma simplex_pivot_rhs_active : forall rows cols i, 0<=i<rows -> In i (simplex_pivot_slots rows cols).
Proof. intros. unfold simplex_pivot_slots. apply in_or_app. left. apply In_Zrange. lia. Qed.
Lemma simplex_pivot_a_active : forall rows cols i j, 0<=i<rows -> 0<=j<cols -> In (16+i*24+j) (simplex_pivot_slots rows cols).
Proof. intros. unfold simplex_pivot_slots. apply in_or_app. right. apply in_flat_map. exists i.
 split; [apply In_Zrange;lia|]. apply in_map_iff. exists j. split; [reflexivity|apply In_Zrange;lia]. Qed.

Local Open Scope Z_scope.
Definition simplex_pivot_ready_zero (n d:list Z) (cols r e leaving:Z) (cn cd:list Z) : Prop :=
 simplex_pivot_recip (Znth(16+r*24+e)n 0) (Znth(16+r*24+e)d 1) (16+r*24+leaving)
 (simplex_pivot_row_prefix (Znth(16+r*24+e)n 0) (Znth(16+r*24+e)d 1) r e cols
 (simplex_pivot_start n d r e))=(1,(cn,cd)).
Definition simplex_pivot_factor (n d:list Z) (cols r e leaving i fnum fden:Z) : Prop :=
 exists a b, simplex_pivot_rows_progress n d cols r e leaving i a b /\
 fnum=Znth(16+i*24+e)a 0 /\ fden=Znth(16+i*24+e)b 1.
Definition simplex_pivot_other_ready (n d:list Z) (cols r e leaving i fnum fden:Z) (cn cd:list Z) : Prop :=
 (if Z.eqb fnum 0 then simplex_pivot_rows_prefix r e cols i (simplex_pivot_before_rows n d cols r e leaving)
 else simplex_pivot_other_prefix fnum fden r i e cols
 (simplex_pivot_addmul fnum fden r i (simplex_pivot_rows_prefix r e cols i (simplex_pivot_before_rows n d cols r e leaving))))=(1,(cn,cd)).

Local Open Scope sac.
Definition simplex_pivot_flags_except (s cols:Z) (ib:list Z) (b e:Z) : Assertion :=
 iter_sepcon (map (fun k => ((&((s) # "SxState" ->ₛ "is_basic")) + k*sizeof(INT)) # Int |-> Znth k ib 0)
 (filter (fun k => negb(Z.eqb k b || Z.eqb k e)) (Zrange 0 cols))).

(* Mathematical solution-set layer. SumLib's available sum codomain is Z,
   not Qc; this finite linear form uses the standard fold over an existing
   index list. It is not an alternative checked-arithmetic execution model. *)
From Coq Require Import QArith.Qcanon setoid_ring.Field.
Local Open Scope Qc_scope.
Definition simplex_pivot_fraction (n d:Z) : Qc := Q2Qc (QArith_base.Qmake n (Z.to_pos d)).
Lemma simplex_pivot_fraction_cross : forall a b p q,
 (0<b)%Z -> (0<q)%Z -> (a*q=p*b)%Z ->
 simplex_pivot_fraction a b = simplex_pivot_fraction p q.
Proof. intros a b p q Hb Hq H. unfold simplex_pivot_fraction.
 apply Q2Qc_eq_iff. unfold QArith_base.Qeq. simpl. rewrite !Z2Pos.id by lia. exact H. Qed.
Lemma simplex_pivot_row_algebra (p zb ze d u:Qc) : p<>0 ->
 (zb=d+p*ze+u <-> ze= -d/p+zb/p-u/p).
Proof. intro Hp. split; intro H; rewrite H; field; exact Hp. Qed.
Lemma simplex_pivot_other_algebra (zi d f ze r w v:Qc) : ze=r+w ->
 (zi=d+f*ze+v <-> zi=(d+f*r)+(v+f*w)).
Proof. intro H. rewrite H.
 assert(K:d+f*(r+w)+v=(d+f*r)+(v+f*w)) by ring. rewrite K. tauto. Qed.
Lemma simplex_pivot_quotient_zero (x p:Qc) : p<>0 -> -x/p=0 -> x=0.
Proof. intros Hp H. assert(K:p*(-x/p)= -x) by (field;exact Hp).
 rewrite H in K. assert(Hopp:-x=0) by (rewrite <-K;ring).
 replace x with (-(-x)) by ring. rewrite Hopp. ring. Qed.
Lemma simplex_pivot_residuals_iff (rows r:Z) (p:Qc) (old new coef:Z->Qc) :
 (0<=r<rows)%Z -> p<>0 -> new r= -old r/p ->
 (forall i,(0<=i<rows)%Z -> i<>r -> new i=old i+coef i*new r) ->
 ((forall i,(0<=i<rows)%Z -> old i=0) <-> (forall i,(0<=i<rows)%Z -> new i=0)).
Proof.
 intros Hr Hp Hrow Hother. split;intro H.
 - assert(HF:new r=0) by (rewrite Hrow,(H r Hr);field;exact Hp).
   intros i Hi. destruct(Z.eq_dec i r) as [->|Hne];[exact HF|].
   rewrite(Hother i Hi Hne),(H i Hi),HF. ring.
 - assert(HE:old r=0).
   { apply(simplex_pivot_quotient_zero (old r) p Hp). rewrite <-Hrow. apply H. exact Hr. }
   intros i Hi. destruct(Z.eq_dec i r) as [->|Hne];[exact HE|].
   pose proof(Hother i Hi Hne) as K. rewrite(H i Hi),(H r Hr) in K.
   replace(old i+coef i*0) with (old i) in K by ring. symmetry. exact K.
Qed.
Definition simplex_pivot_linear (j:list Z) (f:Z->Qc) : Qc := fold_right (fun k acc=>f k+acc) 0 j.
Lemma simplex_pivot_linear_ext : forall j f g,
 (forall k,In k j -> f k=g k) -> simplex_pivot_linear j f=simplex_pivot_linear j g.
Proof. induction j as [|a j IH];intros f g H;[reflexivity|].
 change(f a+simplex_pivot_linear j f=g a+simplex_pivot_linear j g).
 assert (HT: simplex_pivot_linear j f=simplex_pivot_linear j g). { apply IH. intros k Hk. apply H. right. exact Hk. } rewrite (H a (or_introl eq_refl)),HT. reflexivity. Qed.
Lemma simplex_pivot_linear_zero : forall j, simplex_pivot_linear j (fun _=>0)=0.
Proof. induction j as [|a j IH];[reflexivity|].
 change(0+simplex_pivot_linear j(fun _=>0)=0). rewrite IH. ring. Qed.
Lemma simplex_pivot_linear_add : forall j f g,
 simplex_pivot_linear j(fun k=>f k+g k)=simplex_pivot_linear j f+simplex_pivot_linear j g.
Proof. induction j as [|a j IH];intros;[unfold simplex_pivot_linear;simpl;ring|].
 change((f a+g a)+simplex_pivot_linear j(fun k=>f k+g k)=
 (f a+simplex_pivot_linear j f)+(g a+simplex_pivot_linear j g)). rewrite IH. ring. Qed.
Lemma simplex_pivot_linear_scale : forall j c f,
 simplex_pivot_linear j(fun k=>c*f k)=c*simplex_pivot_linear j f.
Proof. induction j as [|a j IH];intros;[unfold simplex_pivot_linear;simpl;ring|].
 change(c*f a+simplex_pivot_linear j(fun k=>c*f k)=c*(f a+simplex_pivot_linear j f)). rewrite IH. ring. Qed.
Lemma simplex_pivot_linear_absent : forall j k x,
 ~In k j -> simplex_pivot_linear j(fun i=>if Z.eq_dec i k then x else 0)=0.
Proof. intros j k x H. transitivity(simplex_pivot_linear j(fun _=>0)).
 - apply simplex_pivot_linear_ext. intros i Hi. destruct(Z.eq_dec i k) as [->|Hne];[contradiction|reflexivity].
 - apply simplex_pivot_linear_zero. Qed.
Lemma simplex_pivot_linear_single : forall j k x,
 NoDup j -> In k j -> simplex_pivot_linear j(fun i=>if Z.eq_dec i k then x else 0)=x.
Proof. induction j as [|a j IH];intros k x Hnd Hin;[contradiction|].
 inversion Hnd as [|a' j' Hnot Htail];subst.
 change((if Z.eq_dec a k then x else 0)+simplex_pivot_linear j(fun i=>if Z.eq_dec i k then x else 0)=x).
 destruct(Z.eq_dec a k) as [Heq|Hne].
 - subst a. rewrite simplex_pivot_linear_absent by exact Hnot. ring.
 - assert(Hk:In k j) by (destruct Hin as [Hbad|Hk];[contradiction|exact Hk]).
   rewrite(IH k x Htail Hk). ring. Qed.
Lemma simplex_pivot_linear_split : forall j f k, NoDup j -> In k j ->
 simplex_pivot_linear j f=f k+simplex_pivot_linear j(fun i=>if Z.eq_dec i k then 0 else f i).
Proof. intros j f k Hnd Hin.
 transitivity(simplex_pivot_linear j(fun i=>
 (if Z.eq_dec i k then f k else 0)+(if Z.eq_dec i k then 0 else f i))).
 - apply simplex_pivot_linear_ext. intros i Hi. destruct(Z.eq_dec i k) as [->|Hne];ring.
 - rewrite simplex_pivot_linear_add,simplex_pivot_linear_single by assumption. reflexivity. Qed.
Local Close Scope Qc_scope.

Local Open Scope Z_scope.
Definition simplex_pivot_observe (s:simplex_pivot_state) (k:Z) :=
 simplex_pivot_at (fst(snd s)) (snd(snd s)) k.
Lemma simplex_pivot_put_here : forall k a b q n d,
 Zlength n=400 -> Zlength d=400 -> 0<=k<400 ->
 simplex_pivot_observe (simplex_pivot_put k a b (q,(n,d))) k=(a,b).
Proof. intros. change ((Znth k (replace_Znth k a n) 0,Znth k (replace_Znth k b d) 1)=(a,b)).
 rewrite !Znth_replace_Znth_Same by lia. reflexivity. Qed.
Lemma simplex_pivot_put_other : forall k j a b q n d,
 Zlength n=400 -> Zlength d=400 -> 0<=k<400 -> 0<=j<400 -> k<>j ->
 simplex_pivot_observe (simplex_pivot_put k a b (q,(n,d))) j=simplex_pivot_observe (q,(n,d)) j.
Proof. intros. change ((Znth j (replace_Znth k a n) 0,Znth j (replace_Znth k b d) 1)=(Znth j n 0,Znth j d 1)).
 rewrite !Znth_replace_Znth_Diff by lia. reflexivity. Qed.
Lemma simplex_pivot_fold_fixed : forall {A B:Type} (f:A->B->A) s xs,
 (forall x,f s x=s) -> fold_left f xs s=s.
Proof. intros A B f s xs H. induction xs;[reflexivity|]. cbn. rewrite H. exact IHxs. Qed.
Lemma simplex_pivot_row_failed : forall pn pd r e cols n d,
 simplex_pivot_row_prefix pn pd r e cols (0,(n,d))=(0,(n,d)).
Proof. intros. unfold simplex_pivot_row_prefix. apply simplex_pivot_fold_fixed.
 intros j. unfold simplex_pivot_row_column. destruct(Z.eqb j e);reflexivity. Qed.
Lemma simplex_pivot_other_failed : forall a b r i e cols n d,
 simplex_pivot_other_prefix a b r i e cols (0,(n,d))=(0,(n,d)).
Proof. intros. unfold simplex_pivot_other_prefix. apply simplex_pivot_fold_fixed.
 intros j. unfold simplex_pivot_other_column. destruct(Z.eqb j e);reflexivity. Qed.
Lemma simplex_pivot_rows_failed : forall r e cols rows n d,
 simplex_pivot_rows_prefix r e cols rows (0,(n,d))=(0,(n,d)).
Proof. intros. unfold simplex_pivot_rows_prefix. apply simplex_pivot_fold_fixed.
 intros i. unfold simplex_pivot_other_row. destruct(Z.eqb i r);reflexivity. Qed.
Lemma simplex_pivot_zero_rejected : forall n d rows cols r e leaving,
 Znth(16+r*24+e)n 0=0 ->
 simplex_pivot_compute n d rows cols r e leaving=(0,(n,d)).
Proof. intros n d rows cols r e leaving H. unfold simplex_pivot_compute.
 rewrite H. change(simplex_pivot_rows_prefix r e cols rows
 (simplex_pivot_zero(16+r*24+e)
 (simplex_pivot_recip 0 (Znth(16+r*24+e)d 1) (16+r*24+leaving)
 (simplex_pivot_row_prefix 0 (Znth(16+r*24+e)d 1) r e cols (0,(n,d)))))=(0,(n,d))).
 rewrite simplex_pivot_row_failed. cbn [simplex_pivot_recip simplex_pivot_zero].
 apply simplex_pivot_rows_failed. Qed.
(* Success-only mathematical outputs. These are actual C postconditions,
   not assumptions of the checked computation. Deep composition proofs are
   generated return obligations; the seed algebra above supplies their field layer. *)
Local Open Scope Qc_scope.
Definition simplex_pivot_value (n d:list Z) (k:Z) : Qc :=
 simplex_pivot_fraction (Znth k n 0%Z) (Znth k d 1%Z).
Definition simplex_pivot_closed (n d on od:list Z) (rows cols r e b:Z) : Prop :=
 let p:=simplex_pivot_value n d (16+r*24+e)%Z in
 p<>0 /\
 simplex_pivot_value on od r= -simplex_pivot_value n d r/p /\
 (forall j,(0<=j<cols)%Z -> simplex_pivot_value on od (16+r*24+j)%Z=
  if Z.eq_dec j e then 0 else if Z.eq_dec j b then 1/p
  else -simplex_pivot_value n d (16+r*24+j)%Z/p) /\
 (forall i,(0<=i<rows)%Z -> i<>r -> simplex_pivot_value on od i=
  simplex_pivot_value n d i+simplex_pivot_value n d (16+i*24+e)%Z*simplex_pivot_value on od r) /\
 (forall i j,(0<=i<rows)%Z -> i<>r -> (0<=j<cols)%Z ->
  simplex_pivot_value on od (16+i*24+j)%Z=
  if Z.eq_dec j e then 0 else simplex_pivot_value n d (16+i*24+j)%Z+
   simplex_pivot_value n d (16+i*24+e)%Z*simplex_pivot_value on od (16+r*24+j)%Z).
Definition simplex_pivot_equations (n d b:list Z) (rows cols:Z) (z:Z->Qc) : Prop :=
 forall i,(0<=i<rows)%Z -> z(Znth i b 0%Z)=simplex_pivot_value n d i+
 simplex_pivot_linear (Zrange 0%Z cols) (fun j=>simplex_pivot_value n d (16+i*24+j)%Z*z j).
Definition simplex_pivot_equiv (n d on od b:list Z) (rows cols r e:Z) : Prop :=
 forall z, simplex_pivot_equations n d b rows cols z <->
 simplex_pivot_equations on od (replace_Znth r e b) rows cols z.
Local Close Scope Qc_scope.

Local Open Scope Z_scope.
(* Nonvacuity arithmetic example: one row, two variables, old basic=1,
   entering=0, rhs=0, coefficients [1,0], all denominators one. *)
Example simplex_pivot_nonzero_example :
 simplex_pivot_compute (replace_Znth 16 1 (repeat 0 400)) (repeat 1 400) 1 2 0 0 1 =
 (1,(replace_Znth 17 1 (repeat 0 400),repeat 1 400)).
Proof. vm_compute. reflexivity. Qed.


Lemma pivot_put_lengths__success_math : forall k a b q n d,
 Zlength (fst (snd (simplex_pivot_put k a b (q,(n,d)))))=Zlength n /\
 Zlength (snd (snd (simplex_pivot_put k a b (q,(n,d)))))=Zlength d.
Proof. intros. change (Zlength(replace_Znth k a n)=Zlength n /\ Zlength(replace_Znth k b d)=Zlength d). rewrite !Zlength_replace_Znth. auto. Qed.
Lemma pivot_div_back__success_math : forall pn pd k neg q n d,
 fst(simplex_pivot_div pn pd k neg (q,(n,d)))=1 -> q=1.
Proof. intros pn pd k neg q n d. unfold simplex_pivot_div.
 destruct(Z.eqb q 1) eqn:H;[apply Z.eqb_eq in H;auto|]. cbn. auto. Qed.
Lemma pivot_recip_back__success_math : forall pn pd k q n d,
 fst(simplex_pivot_recip pn pd k (q,(n,d)))=1 -> q=1.
Proof. intros pn pd k q n d. unfold simplex_pivot_recip.
 destruct(Z.eqb q 1) eqn:H;[apply Z.eqb_eq in H;auto|]. cbn. auto. Qed.
Lemma pivot_zero_back__success_math : forall k s,
 fst(simplex_pivot_zero k s)=1 -> fst s=1.
Proof. intros k [q [n d]]. unfold simplex_pivot_zero. cbn.
 destruct(Z.eqb q 1) eqn:H;[apply Z.eqb_eq in H;auto|]. cbn. auto. Qed.
Lemma pivot_addmul_back__success_math : forall a b src dst q n d,
 fst(simplex_pivot_addmul a b src dst (q,(n,d)))=1 -> q=1.
Proof. intros a b src dst q n d. unfold simplex_pivot_addmul.
 destruct(Z.eqb q 1) eqn:H;[apply Z.eqb_eq in H;auto|]. cbn. auto. Qed.
Lemma pivot_fold_back__success_math : forall {A:Type} (f:simplex_pivot_state->A->simplex_pivot_state),
 (forall s x, fst(f s x)=1 -> fst s=1) ->
 forall xs s, fst(fold_left f xs s)=1 -> fst s=1.
Proof. intros A f H xs. induction xs as [|a xs IH];intros s Hs;[exact Hs|].
 cbn in Hs. apply(H s a). apply(IH (f s a)). exact Hs. Qed.
Lemma pivot_row_back__success_math : forall pn pd r e cols s,
 fst(simplex_pivot_row_prefix pn pd r e cols s)=1 -> fst s=1.
Proof. intros. eapply pivot_fold_back__success_math;[|exact H].
 intros [q [n d]] j. unfold simplex_pivot_row_column.
 destruct(Z.eqb j e);[auto|]. apply pivot_div_back__success_math. Qed.
Lemma pivot_other_back__success_math : forall a b r i e cols s,
 fst(simplex_pivot_other_prefix a b r i e cols s)=1 -> fst s=1.
Proof. intros. eapply pivot_fold_back__success_math;[|exact H].
 intros [q [n d]] j. unfold simplex_pivot_other_column.
 destruct(Z.eqb j e);[auto|]. apply pivot_addmul_back__success_math. Qed.
Lemma pivot_rows_back__success_math : forall r e cols rows s,
 fst(simplex_pivot_rows_prefix r e cols rows s)=1 -> fst s=1.
Proof. intros. eapply pivot_fold_back__success_math;[|exact H].
 intros [q [n d]] i. unfold simplex_pivot_other_row.
 destruct(Z.eqb i r);[auto|]. destruct(Z.eqb q 1) eqn:E;[apply Z.eqb_eq in E;auto|]. auto. Qed.
Lemma pivot_compute_nonzero__success_math : forall n d rows cols r e b on od,
 simplex_pivot_compute n d rows cols r e b=(1,(on,od)) -> Znth(16+r*24+e)n 0<>0.
Proof. intros n d rows cols r e b on od H Hz.
 rewrite(simplex_pivot_zero_rejected n d rows cols r e b Hz) in H. discriminate. Qed.
Lemma pivot_fraction_neg__success_math : forall a b, (0<b)%Z ->
 simplex_pivot_fraction (-a) b=(-simplex_pivot_fraction a b)%Qc.
Proof. intros. unfold simplex_pivot_fraction, Qcopp. apply Q2Qc_eq_iff.
 change (QArith_base.Qeq (QArith_base.Qmake (-a) (Z.to_pos b)) (QArith_base.Qopp (Qreduction.Qred (QArith_base.Qmake a (Z.to_pos b))))). setoid_rewrite Qreduction.Qred_correct. unfold QArith_base.Qeq. simpl. repeat rewrite Pos2Z.inj_mul. rewrite !Z2Pos.id by lia. ring. Qed.
Lemma pivot_fraction_mult__success_math : forall a b c d p q,
 (0<b)%Z -> (0<d)%Z -> (0<q)%Z -> (a*c*q=p*(b*d))%Z ->
 simplex_pivot_fraction p q=(simplex_pivot_fraction a b*simplex_pivot_fraction c d)%Qc.
Proof. intros. unfold simplex_pivot_fraction, Qcmult. apply Q2Qc_eq_iff.
 change (QArith_base.Qeq (QArith_base.Qmake p (Z.to_pos q)) (QArith_base.Qmult (Qreduction.Qred (QArith_base.Qmake a (Z.to_pos b))) (Qreduction.Qred (QArith_base.Qmake c (Z.to_pos d))))). setoid_rewrite Qreduction.Qred_correct. unfold QArith_base.Qeq. simpl. repeat rewrite Pos2Z.inj_mul. rewrite !Z2Pos.id by lia. nia. Qed.
Lemma pivot_fraction_add__success_math : forall a b c d p q,
 (0<b)%Z -> (0<d)%Z -> (0<q)%Z -> ((a*d+c*b)*q=p*(b*d))%Z ->
 simplex_pivot_fraction p q=(simplex_pivot_fraction a b+simplex_pivot_fraction c d)%Qc.
Proof. intros. unfold simplex_pivot_fraction, Qcplus. apply Q2Qc_eq_iff.
 change (QArith_base.Qeq (QArith_base.Qmake p (Z.to_pos q)) (QArith_base.Qplus (Qreduction.Qred (QArith_base.Qmake a (Z.to_pos b))) (Qreduction.Qred (QArith_base.Qmake c (Z.to_pos d))))). setoid_rewrite Qreduction.Qred_correct. unfold QArith_base.Qeq. simpl. repeat rewrite Pos2Z.inj_mul. rewrite !Z2Pos.id by lia. nia. Qed.
Lemma pivot_fraction_nonzero__success_math : forall c d, (0<d)%Z -> c<>0%Z -> simplex_pivot_fraction c d<>0%Qc.
Proof. intros c d Hd Hc Hz. unfold simplex_pivot_fraction in Hz.
 change (Q2Qc (QArith_base.Qmake c (Z.to_pos d))=Q2Qc (QArith_base.Qmake 0 1)) in Hz.
 apply Q2Qc_eq_iff in Hz. unfold QArith_base.Qeq in Hz. simpl in Hz. lia. Qed.
Lemma pivot_fraction_div__success_math : forall a b c d p q,
 (0<b)%Z -> (0<d)%Z -> (0<q)%Z -> c<>0%Z -> ((a*d)*q=p*(b*c))%Z ->
 simplex_pivot_fraction p q=(simplex_pivot_fraction a b/simplex_pivot_fraction c d)%Qc.
Proof. intros a b c d p q Hb Hd Hq Hc Hcross.
 assert(Hnz:simplex_pivot_fraction c d<>0%Qc) by (apply pivot_fraction_nonzero__success_math;assumption).
 assert(Hm:(simplex_pivot_fraction p q*simplex_pivot_fraction c d)%Qc=simplex_pivot_fraction a b).
 { symmetry. apply pivot_fraction_mult__success_math;try assumption;nia. }
 replace (simplex_pivot_fraction p q) with
  ((simplex_pivot_fraction p q*simplex_pivot_fraction c d)/simplex_pivot_fraction c d)%Qc by (field;exact Hnz).
 rewrite Hm. reflexivity. Qed.
Lemma pivot_div_quotients__success_math : forall a b c d,
 (1<=b)%Z -> (1<=d)%Z -> simplex_rat_div_flag a b c d=1%Z ->
 let nn:=(if Z.ltb (b*c) 0 then -(a*d) else a*d)%Z in
 let dd:=Z.abs(b*c) in let g:=Z.gcd(Z.abs nn)dd in
 (0<Z.quot dd g)%Z /\ simplex_pivot_fraction (Z.quot nn g) (Z.quot dd g)=
 (simplex_pivot_fraction a b/simplex_pivot_fraction c d)%Qc.
Proof. intros a b c d Hb Hd HF. cbn zeta.
 assert(HR:simplex_rat_div_result a b c d
  (Z.quot (if Z.ltb (b*c) 0 then -(a*d) else a*d) (Z.gcd (Z.abs(if Z.ltb(b*c)0 then -(a*d) else a*d)) (Z.abs(b*c))))
  (Z.quot (Z.abs(b*c)) (Z.gcd (Z.abs(if Z.ltb(b*c)0 then -(a*d) else a*d)) (Z.abs(b*c))))).
 { unfold simplex_rat_div_result,simplex_rat_reduce_result. auto. }
 pose proof(simplex_rat_div_flag_success a b c d) as HS. apply HS in HF. destruct HF as [Hc HF].
 pose proof(simplex_rat_div_normalized_bridge a b c d _ _ ltac:(lia) Hc HR) as [HQ HV].
 split;[exact HQ|]. apply pivot_fraction_div__success_math;assumption||lia.
Qed.
Lemma pivot_normalize_value__success_math : forall n d, (0<d)%Z ->
 let g:=Z.gcd(Z.abs n)d in (0<Z.quot d g)%Z /\
 simplex_pivot_fraction (Z.quot n g) (Z.quot d g)=simplex_pivot_fraction n d.
Proof. intros n d HD. cbn zeta.
 pose proof(simplex_rat_reduce_den_bounds n d HD) as HQ.
 pose proof(simplex_rat_reduce_value n d HD) as HV.
 split;[lia|]. apply simplex_pivot_fraction_cross;lia. Qed.
Lemma pivot_mul_quotients__success_math : forall a b c d,
 (0<b)%Z -> (0<d)%Z -> let g:=Z.gcd(Z.abs(a*c))(b*d) in
 (0<Z.quot (b*d) g)%Z /\ simplex_pivot_fraction (Z.quot(a*c)g)(Z.quot(b*d)g)=
 (simplex_pivot_fraction a b*simplex_pivot_fraction c d)%Qc.
Proof. intros a b c d Hb Hd. cbn zeta.
 destruct(pivot_normalize_value__success_math (a*c)(b*d) ltac:(nia)) as [HP HV].
 split;[exact HP|]. rewrite HV. apply pivot_fraction_mult__success_math;try nia. Qed.
Lemma pivot_add_quotients__success_math : forall a b c d,
 (0<b)%Z -> (0<d)%Z -> let nn:=(a*d+c*b)%Z in let dd:=(b*d)%Z in
 let g:=Z.gcd(Z.abs nn)dd in (0<Z.quot dd g)%Z /\
 simplex_pivot_fraction(Z.quot nn g)(Z.quot dd g)=
 (simplex_pivot_fraction a b+simplex_pivot_fraction c d)%Qc.
Proof. intros a b c d Hb Hd. cbn zeta.
 destruct(pivot_normalize_value__success_math (a*d+c*b)(b*d) ltac:(nia)) as [HP HV].
 split;[exact HP|]. rewrite HV. apply pivot_fraction_add__success_math;try nia. Qed.
Lemma pivot_fraction_zero__success_math : forall d, (0<d)%Z -> simplex_pivot_fraction 0 d=0%Qc.
Proof. intros d Hd. change(simplex_pivot_fraction 0 d=simplex_pivot_fraction 0 1).
 apply simplex_pivot_fraction_cross;lia. Qed.
Lemma pivot_div_frame__success_math : forall pn pd k neg q n d j,
 Zlength n=400 -> Zlength d=400 -> 0<=k<400 -> 0<=j<400 -> k<>j ->
 simplex_pivot_observe (simplex_pivot_div pn pd k neg (q,(n,d))) j=simplex_pivot_observe(q,(n,d))j.
Proof. intros. unfold simplex_pivot_div. destruct(Z.eqb q 1);[|reflexivity].
 destruct(Z.eqb(simplex_rat_div_flag _ _ _ _)1);[apply simplex_pivot_put_other;assumption|reflexivity]. Qed.
Lemma pivot_recip_frame__success_math : forall pn pd k q n d j,
 Zlength n=400 -> Zlength d=400 -> 0<=k<400 -> 0<=j<400 -> k<>j ->
 simplex_pivot_observe (simplex_pivot_recip pn pd k (q,(n,d))) j=simplex_pivot_observe(q,(n,d))j.
Proof. intros. unfold simplex_pivot_recip. destruct(Z.eqb q 1);[|reflexivity].
 destruct(Z.eqb(simplex_rat_div_flag _ _ _ _)1);[apply simplex_pivot_put_other;assumption|reflexivity]. Qed.
Lemma pivot_zero_frame__success_math : forall k q n d j,
 Zlength n=400 -> Zlength d=400 -> 0<=k<400 -> 0<=j<400 -> k<>j ->
 simplex_pivot_observe(simplex_pivot_zero k(q,(n,d)))j=simplex_pivot_observe(q,(n,d))j.
Proof. intros. unfold simplex_pivot_zero. cbn [fst]. destruct(Z.eqb q 1);[apply simplex_pivot_put_other;assumption|reflexivity]. Qed.
Lemma pivot_addmul_frame__success_math : forall a b src dst q n d j,
 Zlength n=400 -> Zlength d=400 -> 0<=dst<400 -> 0<=j<400 -> dst<>j ->
 simplex_pivot_observe(simplex_pivot_addmul a b src dst(q,(n,d)))j=simplex_pivot_observe(q,(n,d))j.
Proof. intros. unfold simplex_pivot_addmul. destruct(Z.eqb q 1);[|reflexivity].
 destruct(Z.eqb(simplex_rat_mul_flag _ _ _ _)1);[|reflexivity].
 destruct(Z.eqb(simplex_rat_add_flag _ _ _ _)1);[apply simplex_pivot_put_other;assumption|reflexivity]. Qed.
Lemma pivot_div_lengths__success_math : forall pn pd k neg q n d,
 Zlength(fst(snd(simplex_pivot_div pn pd k neg(q,(n,d)))))=Zlength n /\
 Zlength(snd(snd(simplex_pivot_div pn pd k neg(q,(n,d)))))=Zlength d.
Proof. intros. unfold simplex_pivot_div. destruct(Z.eqb q 1);[|cbn;auto].
 destruct(Z.eqb(simplex_rat_div_flag _ _ _ _)1);[apply pivot_put_lengths__success_math|cbn;auto]. Qed.
Lemma pivot_recip_lengths__success_math : forall pn pd k q n d,
 Zlength(fst(snd(simplex_pivot_recip pn pd k(q,(n,d)))))=Zlength n /\
 Zlength(snd(snd(simplex_pivot_recip pn pd k(q,(n,d)))))=Zlength d.
Proof. intros. unfold simplex_pivot_recip. destruct(Z.eqb q 1);[|cbn;auto].
 destruct(Z.eqb(simplex_rat_div_flag _ _ _ _)1);[apply pivot_put_lengths__success_math|cbn;auto]. Qed.
Lemma pivot_zero_lengths__success_math : forall k q n d,
 Zlength(fst(snd(simplex_pivot_zero k(q,(n,d)))))=Zlength n /\
 Zlength(snd(snd(simplex_pivot_zero k(q,(n,d)))))=Zlength d.
Proof. intros. unfold simplex_pivot_zero. cbn [fst]. destruct(Z.eqb q 1);[apply pivot_put_lengths__success_math|cbn;auto]. Qed.
Lemma pivot_addmul_lengths__success_math : forall a b src dst q n d,
 Zlength(fst(snd(simplex_pivot_addmul a b src dst(q,(n,d)))))=Zlength n /\
 Zlength(snd(snd(simplex_pivot_addmul a b src dst(q,(n,d)))))=Zlength d.
Proof. intros. unfold simplex_pivot_addmul. destruct(Z.eqb q 1);[|cbn;auto].
 destruct(Z.eqb(simplex_rat_mul_flag _ _ _ _)1);[|cbn;auto].
 destruct(Z.eqb(simplex_rat_add_flag _ _ _ _)1);[apply pivot_put_lengths__success_math|cbn;auto]. Qed.
Lemma pivot_div_value__success_math : forall pn pd k neg n d on od,
 Zlength n=400 -> Zlength d=400 -> 0<=k<400 ->
 1<=Znth k d 1 -> 1<=pd ->
 simplex_pivot_div pn pd k neg (1,(n,d))=(1,(on,od)) ->
 0<Znth k od 1 /\ simplex_pivot_value on od k=
 (if neg then -(simplex_pivot_value n d k/simplex_pivot_fraction pn pd)
 else simplex_pivot_value n d k/simplex_pivot_fraction pn pd)%Qc.
Proof. intros pn pd k neg n d on od Hn Hd Hk Hb Hpd HS.
 unfold simplex_pivot_div in HS. rewrite Z.eqb_refl in HS.
 destruct(Z.eqb(simplex_rat_div_flag (Znth k n 0)(Znth k d 1)pn pd)1)eqn:HF;[|discriminate].
 apply Z.eqb_eq in HF.
 pose proof(pivot_div_quotients__success_math (Znth k n 0)(Znth k d 1)pn pd Hb Hpd HF) as [HQ HV].
 unfold simplex_pivot_put in HS. injection HS as H1 H2. subst on od.
 unfold simplex_pivot_value. rewrite !Znth_replace_Znth_Same by lia.
 split;[exact HQ|]. destruct neg;[rewrite pivot_fraction_neg__success_math by exact HQ;rewrite HV;reflexivity|exact HV]. Qed.
Lemma pivot_range_induction__success_math : forall (f:simplex_pivot_state->Z->simplex_pivot_state)
 (P:Z->simplex_pivot_state->Prop) v s,
 0<=v -> P 0 s ->
 (forall j t,0<=j<v -> P j t -> P (j+1)(f t j)) ->
 P v (fold_left f (Zrange 0 v)s).
Proof. intros f P v s Hv H0 Hstep.
 assert(H:forall n,(Z.of_nat n<=v)%Z -> P(Z.of_nat n)(fold_left f(Zrange 0(Z.of_nat n))s)).
 { induction n as [|n IH];intro Hbound.
   - exact H0.
   - rewrite Nat2Z.inj_succ. change(P (Z.of_nat n+1)(fold_left f(Zrange 0(Z.of_nat n+1))s)). rewrite simplex_scan_range_snoc by lia. rewrite fold_left_app. cbn.
     apply Hstep;[lia|apply IH;lia]. }
 replace v with (Z.of_nat(Z.to_nat v)) by (rewrite Z2Nat.id;lia). apply H. rewrite Z2Nat.id;lia.
Qed.
Lemma pivot_recip_value__success_math : forall pn pd k n d on od,
 Zlength n=400 -> Zlength d=400 -> 0<=k<400 -> 1<=pd ->
 simplex_pivot_recip pn pd k (1,(n,d))=(1,(on,od)) ->
 0<Znth k od 1 /\ simplex_pivot_value on od k=(1/simplex_pivot_fraction pn pd)%Qc.
Proof. intros pn pd k n d on od Hn Hd Hk Hpd HS.
 unfold simplex_pivot_recip in HS. rewrite Z.eqb_refl in HS.
 destruct(Z.eqb(simplex_rat_div_flag 1 1 pn pd)1)eqn:HF;[|discriminate]. apply Z.eqb_eq in HF.
 pose proof(pivot_div_quotients__success_math 1 1 pn pd ltac:(lia) Hpd HF) as [HQ HV].
 rewrite !Z.mul_1_l in HQ,HV.
 unfold simplex_pivot_put in HS. injection HS as H1 H2. subst on od.
 unfold simplex_pivot_value. rewrite !Znth_replace_Znth_Same by lia.
 split;[exact HQ|]. exact HV. Qed.
Lemma pivot_zero_value__success_math : forall k n d,
 Zlength n=400 -> Zlength d=400 -> 0<=k<400 ->
 simplex_pivot_observe(simplex_pivot_zero k(1,(n,d)))k=(0,1).
Proof. intros. apply simplex_pivot_put_here;assumption. Qed.
Lemma pivot_addmul_value__success_math : forall a b src dst n d on od,
 Zlength n=400 -> Zlength d=400 -> 0<=dst<400 ->
 0<b -> 0<Znth src d 1 -> 0<Znth dst d 1 ->
 simplex_pivot_addmul a b src dst(1,(n,d))=(1,(on,od)) ->
 0<Znth dst od 1 /\ simplex_pivot_value on od dst=
 (simplex_pivot_value n d dst+simplex_pivot_fraction a b*simplex_pivot_value n d src)%Qc.
Proof. intros a b src dst n d on od Hn Hd Hdst Hb Hsrc Hden HS.
 unfold simplex_pivot_addmul in HS. rewrite Z.eqb_refl in HS.
 destruct(Z.eqb(simplex_rat_mul_flag a b(Znth src n 0)(Znth src d 1))1)eqn:HF;[|discriminate].
 cbn beta iota zeta in HS.
 set(g:=Z.gcd(Z.abs(a*Znth src n 0))(b*Znth src d 1)) in *.
 set(p:=Z.quot(a*Znth src n 0)g) in *.
 set(t:=Z.quot(b*Znth src d 1)g) in *.
 destruct(Z.eqb(simplex_rat_add_flag (Znth dst n 0)(Znth dst d 1)p t)1)eqn:HA;[|discriminate].
 pose proof(pivot_mul_quotients__success_math a b(Znth src n 0)(Znth src d 1)Hb Hsrc) as [HT HV].
 change(0<t) in HT. change(simplex_pivot_fraction p t=(simplex_pivot_fraction a b*simplex_pivot_value n d src)%Qc) in HV.
 pose proof(pivot_add_quotients__success_math (Znth dst n 0)(Znth dst d 1)p t Hden HT) as [HQ HW].
 unfold simplex_pivot_put in HS. injection HS as H1 H2. subst on od.
 unfold simplex_pivot_value. rewrite !Znth_replace_Znth_Same by lia.
 split;[exact HQ|]. rewrite HW,HV. reflexivity. Qed.
Lemma pivot_fold_invariant__success_math : forall {A:Type}(f:simplex_pivot_state->A->simplex_pivot_state)
 (P:simplex_pivot_state->Prop) xs,
 (forall s x, In x xs -> P s -> P(f s x)) -> forall s,P s -> P(fold_left f xs s).
Proof. intros A f P xs. induction xs as [|a xs IH];intros H s HP;[exact HP|].
 cbn. apply IH.
 - intros t x Hx Ht. apply H;[right;exact Hx|exact Ht].
 - apply H;[left;reflexivity|exact HP]. Qed.
Lemma pivot_row_lengths__success_math : forall pn pd r e cols q n d,
 Zlength n=400 -> Zlength d=400 ->
 Zlength(fst(snd(simplex_pivot_row_prefix pn pd r e cols(q,(n,d)))))=400 /\
 Zlength(snd(snd(simplex_pivot_row_prefix pn pd r e cols(q,(n,d)))))=400.
Proof. intros pn pd r e cols q n d Hn Hd. unfold simplex_pivot_row_prefix.
 apply(pivot_fold_invariant__success_math _
  (fun s=>Zlength(fst(snd s))=400 /\ Zlength(snd(snd s))=400)).
 - intros [qt [nt dt]] j Hj [HN HD]. unfold simplex_pivot_row_column.
   destruct(Z.eqb j e);[split;assumption|].
   destruct(pivot_div_lengths__success_math pn pd (16+r*24+j) true qt nt dt) as [A B].
   rewrite A,B. split;assumption.
 - split;assumption. Qed.
Lemma pivot_row_frame__success_math : forall pn pd r e cols q n d k,
 Zlength n=400 -> Zlength d=400 -> 0<=r<16 -> 0<=cols<=24 -> 0<=k<400 ->
 (forall j,0<=j<cols -> j<>e -> (16+r*24+j)<>k) ->
 simplex_pivot_observe(simplex_pivot_row_prefix pn pd r e cols(q,(n,d)))k=
 simplex_pivot_observe(q,(n,d))k.
Proof. intros pn pd r e cols q n d k Hn Hd Hr Hcols Hk Hother.
 assert(HP:forall s,Zlength(fst(snd s))=400 /\ Zlength(snd(snd s))=400 /\
 simplex_pivot_observe s k=simplex_pivot_observe(q,(n,d))k ->
 forall j,In j(Zrange 0 cols) ->
 Zlength(fst(snd(simplex_pivot_row_column pn pd r e s j)))=400 /\
 Zlength(snd(snd(simplex_pivot_row_column pn pd r e s j)))=400 /\
 simplex_pivot_observe(simplex_pivot_row_column pn pd r e s j)k=simplex_pivot_observe(q,(n,d))k).
 { intros [qt [nt dt]] [HN [HD HK]] j Hj. apply In_Zrange in Hj.
   unfold simplex_pivot_row_column. destruct(Z.eqb j e)eqn:He;[auto|].
   apply Z.eqb_neq in He. destruct(pivot_div_lengths__success_math pn pd(16+r*24+j)true qt nt dt)as[A B].
   rewrite A,B. split;[exact HN|]. split;[exact HD|].
   rewrite (pivot_div_frame__success_math pn pd (16+r*24+j) true qt nt dt k HN HD ltac:(lia) Hk (Hother j Hj He)). exact HK. }
 unfold simplex_pivot_row_prefix.
 pose proof(pivot_fold_invariant__success_math (simplex_pivot_row_column pn pd r e)
 (fun s=>Zlength(fst(snd s))=400 /\ Zlength(snd(snd s))=400 /\
 simplex_pivot_observe s k=simplex_pivot_observe(q,(n,d))k)(Zrange 0 cols)) as HI.
 specialize(HI (fun s j Hj HS=>HP s HS j Hj)(q,(n,d)) ltac:(cbn;auto)). exact (proj2(proj2 HI)).
Qed.
Lemma pivot_obs_value__success_math : forall q n d qt nt dt k,
 simplex_pivot_observe(q,(n,d))k=simplex_pivot_observe(qt,(nt,dt))k ->
 simplex_pivot_value n d k=simplex_pivot_value nt dt k.
Proof. intros. change ((Znth k n 0,Znth k d 1)=(Znth k nt 0,Znth k dt 1)) in H.
 injection H as HN HD. unfold simplex_pivot_value. rewrite HN,HD. reflexivity. Qed.
Lemma pivot_obs_den__success_math : forall q n d qt nt dt k,
 simplex_pivot_observe(q,(n,d))k=simplex_pivot_observe(qt,(nt,dt))k -> Znth k d 1=Znth k dt 1.
Proof. intros. change ((Znth k n 0,Znth k d 1)=(Znth k nt 0,Znth k dt 1)) in H. congruence. Qed.
Lemma pivot_row_values__success_math : forall pn pd r e cols n d on od,
 Zlength n=400 -> Zlength d=400 -> 0<=r<16 -> 0<=cols<=24 -> 1<=pd ->
 (forall j,0<=j<cols -> 0<Znth(16+r*24+j)d 1) ->
 simplex_pivot_row_prefix pn pd r e cols(1,(n,d))=(1,(on,od)) ->
 forall j,0<=j<cols -> j<>e ->
 0<Znth(16+r*24+j)od 1 /\ simplex_pivot_value on od(16+r*24+j)=
 (-(simplex_pivot_value n d(16+r*24+j)/simplex_pivot_fraction pn pd))%Qc.
Proof.
 intros pn pd r e cols n d on od Hn Hd Hr Hcols Hpd HD HE.
 set(P:=fun t (s:simplex_pivot_state)=>
 Zlength(fst(snd s))=400 /\ Zlength(snd(snd s))=400 /\
 (fst s=1 ->
 (forall l,0<=l<t -> l<>e ->
  0<Znth(16+r*24+l)(snd(snd s))1 /\
  simplex_pivot_value(fst(snd s))(snd(snd s))(16+r*24+l)=
    (-(simplex_pivot_value n d(16+r*24+l)/simplex_pivot_fraction pn pd))%Qc) /\
 (forall k,0<=k<400 -> k<16+r*24 \/ 16+r*24+t<=k \/ k=16+r*24+e ->
  simplex_pivot_observe s k=simplex_pivot_observe(1,(n,d))k))).
 assert(Hbase:P 0(1,(n,d))).
 { unfold P. cbn [fst snd]. split;[exact Hn|]. split;[exact Hd|]. intros _. split.
   - intros l Hl Hle. lia.
   - intros k Hk Hmask. reflexivity. }
 assert(Hstep:forall t s,0<=t<cols -> P t s -> P(t+1)(simplex_pivot_row_column pn pd r e s t)).
 { intros t [q [cn cd]] Ht [HN [HC HP]]. cbn [fst snd] in HN,HC,HP. unfold simplex_pivot_row_column.
   destruct(Z.eqb t e)eqn:Et.
   - apply Z.eqb_eq in Et. unfold P. cbn [fst snd]. split;[exact HN|]. split;[exact HC|].
     intro Hq. destruct(HP Hq) as [HV HF]. split.
     + intros l Hl Hle. apply HV;[lia|exact Hle].
     + intros k Hk Hframe. apply HF;[exact Hk|lia].
   - apply Z.eqb_neq in Et.
     destruct(simplex_pivot_div pn pd(16+r*24+t)true(q,(cn,cd)))as[oq [nn dd]]eqn:ES.
     pose proof(pivot_div_lengths__success_math pn pd(16+r*24+t)true q cn cd)as[LN LD].
     rewrite ES in LN,LD. cbn [fst snd] in LN,LD.
     unfold P. cbn [fst snd]. split;[lia|]. split;[lia|]. intro Ho. subst oq.
     assert(Hq:q=1) by (apply(pivot_div_back__success_math pn pd(16+r*24+t)true q cn cd);rewrite ES;reflexivity).
     subst q. destruct(HP eq_refl)as[HV HF].
     assert(Hslot:0<=16+r*24+t<400)by lia.
     assert(Hold:simplex_pivot_observe(1,(cn,cd))(16+r*24+t)=simplex_pivot_observe(1,(n,d))(16+r*24+t)).
     { apply HF;[exact Hslot|right;left;lia]. }
     assert(Hden:1<=Znth(16+r*24+t)cd 1).
     { rewrite(pivot_obs_den__success_math 1 cn cd 1 n d _ Hold). specialize(HD t Ht). lia. }
     pose proof(pivot_div_value__success_math pn pd(16+r*24+t)true cn cd nn dd HN HC Hslot Hden Hpd ES)as[HDnew HVnew].
     split.
     + intros l Hl Hle. destruct(Z.eq_dec l t)as[->|Hlt].
       * split;[exact HDnew|]. change (simplex_pivot_value nn dd (16+r*24+t)= (-(simplex_pivot_value cn cd (16+r*24+t)/simplex_pivot_fraction pn pd))%Qc) in HVnew. etransitivity;[exact HVnew|].
         rewrite(pivot_obs_value__success_math 1 cn cd 1 n d _ Hold). reflexivity.
       * assert(Hlold:0<=l<t)by lia. destruct(HV l Hlold Hle)as[HLden HLval].
         assert(Hframe:simplex_pivot_observe(1,(nn,dd))(16+r*24+l)=simplex_pivot_observe(1,(cn,cd))(16+r*24+l)).
         { rewrite <-ES. apply pivot_div_frame__success_math;try assumption;lia. }
         split.
         -- rewrite(pivot_obs_den__success_math 1 nn dd 1 cn cd _ Hframe). exact HLden.
         -- rewrite(pivot_obs_value__success_math 1 nn dd 1 cn cd _ Hframe). exact HLval.
     + intros k Hk Hframe.
       assert(Hne:(16+r*24+t)<>k)by lia.
       rewrite <-ES. rewrite(pivot_div_frame__success_math pn pd(16+r*24+t)true 1 cn cd k HN HC Hslot Hk Hne).
       apply HF;[exact Hk|lia]. }
 pose proof(pivot_range_induction__success_math (simplex_pivot_row_column pn pd r e) P cols(1,(n,d)) ltac:(lia)Hbase Hstep)as HI.
 change(P cols(simplex_pivot_row_prefix pn pd r e cols(1,(n,d)))) in HI.
 rewrite HE in HI. destruct HI as[_ [_ HH]]. exact(proj1(HH eq_refl)).
Qed.
Lemma pivot_other_lengths__success_math : forall fnum fden r i e cols q n d,
 Zlength n=400 -> Zlength d=400 ->
 Zlength(fst(snd(simplex_pivot_other_prefix fnum fden r i e cols(q,(n,d)))))=400 /\
 Zlength(snd(snd(simplex_pivot_other_prefix fnum fden r i e cols(q,(n,d)))))=400.
Proof. intros fnum fden r i e cols q n d Hn Hd. unfold simplex_pivot_other_prefix.
 apply(pivot_fold_invariant__success_math _
  (fun s=>Zlength(fst(snd s))=400 /\ Zlength(snd(snd s))=400)).
 - intros [qt [nt dt]] j Hj [HN HD]. unfold simplex_pivot_other_column.
   destruct(Z.eqb j e);[split;assumption|].
   destruct(pivot_addmul_lengths__success_math fnum fden (16+r*24+j) (16+i*24+j) qt nt dt) as [A B].
   rewrite A,B. split;assumption.
 - split;assumption. Qed.
Lemma pivot_other_frame__success_math : forall fnum fden r i e cols q n d k,
 Zlength n=400 -> Zlength d=400 -> 0<=i<16 -> 0<=cols<=24 -> 0<=k<400 ->
 (forall j,0<=j<cols -> j<>e -> (16+i*24+j)<>k) ->
 simplex_pivot_observe(simplex_pivot_other_prefix fnum fden r i e cols(q,(n,d)))k=
 simplex_pivot_observe(q,(n,d))k.
Proof. intros fnum fden r i e cols q n d k Hn Hd Hr Hcols Hk Hother.
 assert(HP:forall s,Zlength(fst(snd s))=400 /\ Zlength(snd(snd s))=400 /\
 simplex_pivot_observe s k=simplex_pivot_observe(q,(n,d))k ->
 forall j,In j(Zrange 0 cols) ->
 Zlength(fst(snd(simplex_pivot_other_column fnum fden r i e s j)))=400 /\
 Zlength(snd(snd(simplex_pivot_other_column fnum fden r i e s j)))=400 /\
 simplex_pivot_observe(simplex_pivot_other_column fnum fden r i e s j)k=simplex_pivot_observe(q,(n,d))k).
 { intros [qt [nt dt]] [HN [HD HK]] j Hj. apply In_Zrange in Hj.
   unfold simplex_pivot_other_column. destruct(Z.eqb j e)eqn:He;[auto|].
   apply Z.eqb_neq in He. destruct(pivot_addmul_lengths__success_math fnum fden (16+r*24+j) (16+i*24+j) qt nt dt)as[A B].
   rewrite A,B. split;[exact HN|]. split;[exact HD|].
   rewrite (pivot_addmul_frame__success_math fnum fden (16+r*24+j) (16+i*24+j) qt nt dt k HN HD ltac:(lia) Hk (Hother j Hj He)). exact HK. }
 unfold simplex_pivot_other_prefix.
 pose proof(pivot_fold_invariant__success_math (simplex_pivot_other_column fnum fden r i e)
 (fun s=>Zlength(fst(snd s))=400 /\ Zlength(snd(snd s))=400 /\
 simplex_pivot_observe s k=simplex_pivot_observe(q,(n,d))k)(Zrange 0 cols)) as HI.
 specialize(HI (fun s j Hj HS=>HP s HS j Hj)(q,(n,d)) ltac:(cbn;auto)). exact (proj2(proj2 HI)).
Qed.
Lemma pivot_other_values__success_math : forall fnum fden r i e cols n d on od,
 Zlength n=400 -> Zlength d=400 -> 0<=r<16 -> 0<=i<16 -> r<>i -> 0<=cols<=24 -> 0<fden ->
 (forall j,0<=j<cols -> 0<Znth(16+r*24+j)d 1 /\ 0<Znth(16+i*24+j)d 1) ->
 simplex_pivot_other_prefix fnum fden r i e cols(1,(n,d))=(1,(on,od)) ->
 forall j,0<=j<cols -> j<>e ->
 0<Znth(16+i*24+j)od 1 /\ simplex_pivot_value on od(16+i*24+j)=
 (simplex_pivot_value n d(16+i*24+j)+simplex_pivot_fraction fnum fden*simplex_pivot_value n d(16+r*24+j))%Qc.
Proof.
 intros fnum fden r i e cols n d on od Hn Hd Hr Hi Hri Hcols Hfd HD HE.
 set(P:=fun t (s:simplex_pivot_state)=>
 Zlength(fst(snd s))=400 /\ Zlength(snd(snd s))=400 /\
 (fst s=1 ->
 (forall l,0<=l<t -> l<>e ->
  0<Znth(16+i*24+l)(snd(snd s))1 /\
  simplex_pivot_value(fst(snd s))(snd(snd s))(16+i*24+l)=
    (simplex_pivot_value n d(16+i*24+l)+simplex_pivot_fraction fnum fden*simplex_pivot_value n d(16+r*24+l))%Qc) /\
 (forall k,0<=k<400 -> k<16+i*24 \/ 16+i*24+t<=k \/ k=16+i*24+e ->
  simplex_pivot_observe s k=simplex_pivot_observe(1,(n,d))k))).
 assert(Hbase:P 0(1,(n,d))).
 { unfold P. cbn [fst snd]. split;[exact Hn|]. split;[exact Hd|]. intros _. split.
   - intros l Hl Hle. lia.
   - intros k Hk Hmask. reflexivity. }
 assert(Hstep:forall t s,0<=t<cols -> P t s -> P(t+1)(simplex_pivot_other_column fnum fden r i e s t)).
 { intros t [q [cn cd]] Ht [HN [HC HP]]. cbn [fst snd] in HN,HC,HP. unfold simplex_pivot_other_column.
   destruct(Z.eqb t e)eqn:Et.
   - apply Z.eqb_eq in Et. unfold P. cbn [fst snd]. split;[exact HN|]. split;[exact HC|].
     intro Hq. destruct(HP Hq) as [HV HF]. split.
     + intros l Hl Hle. apply HV;[lia|exact Hle].
     + intros k Hk Hframe. apply HF;[exact Hk|lia].
   - apply Z.eqb_neq in Et.
     destruct(simplex_pivot_addmul fnum fden (16+r*24+t)(16+i*24+t)(q,(cn,cd)))as[oq [nn dd]]eqn:ES.
     pose proof(pivot_addmul_lengths__success_math fnum fden (16+r*24+t)(16+i*24+t) q cn cd)as[LN LD].
     rewrite ES in LN,LD. cbn [fst snd] in LN,LD.
     unfold P. cbn [fst snd]. split;[lia|]. split;[lia|]. intro Ho. subst oq.
     assert(Hq:q=1) by (apply(pivot_addmul_back__success_math fnum fden (16+r*24+t)(16+i*24+t) q cn cd);rewrite ES;reflexivity).
     subst q. destruct(HP eq_refl)as[HV HF].
     assert(Hslot:0<=16+i*24+t<400)by lia.
     assert(Hold:simplex_pivot_observe(1,(cn,cd))(16+i*24+t)=simplex_pivot_observe(1,(n,d))(16+i*24+t)).
     { apply HF;[exact Hslot|right;left;lia]. }
     assert(Hsource:simplex_pivot_observe(1,(cn,cd))(16+r*24+t)=simplex_pivot_observe(1,(n,d))(16+r*24+t)).
     { apply HF;[lia|]. destruct(Z_lt_ge_dec r i);[left;lia|right;left;lia]. }
     assert(Hden:0<Znth(16+i*24+t)cd 1).
     { rewrite(pivot_obs_den__success_math 1 cn cd 1 n d _ Hold). exact(proj2(HD t Ht)). }
     assert(Hsrc:0<Znth(16+r*24+t)cd 1).
     { rewrite(pivot_obs_den__success_math 1 cn cd 1 n d _ Hsource). exact(proj1(HD t Ht)). }
     pose proof(pivot_addmul_value__success_math fnum fden (16+r*24+t)(16+i*24+t) cn cd nn dd HN HC Hslot Hfd Hsrc Hden ES)as[HDnew HVnew].
     split.
     + intros l Hl Hle. destruct(Z.eq_dec l t)as[->|Hlt].
       * split;[exact HDnew|]. etransitivity;[exact HVnew|].
         rewrite(pivot_obs_value__success_math 1 cn cd 1 n d _ Hold).
         rewrite(pivot_obs_value__success_math 1 cn cd 1 n d _ Hsource). reflexivity.
       * assert(Hlold:0<=l<t)by lia. destruct(HV l Hlold Hle)as[HLden HLval].
         assert(Hframe:simplex_pivot_observe(1,(nn,dd))(16+i*24+l)=simplex_pivot_observe(1,(cn,cd))(16+i*24+l)).
         { rewrite <-ES. apply pivot_addmul_frame__success_math;try assumption;lia. }
         split.
         -- rewrite(pivot_obs_den__success_math 1 nn dd 1 cn cd _ Hframe). exact HLden.
         -- rewrite(pivot_obs_value__success_math 1 nn dd 1 cn cd _ Hframe). exact HLval.
     + intros k Hk Hframe.
       assert(Hne:(16+i*24+t)<>k)by lia.
       rewrite <-ES. rewrite(pivot_addmul_frame__success_math fnum fden (16+r*24+t)(16+i*24+t) 1 cn cd k HN HC Hslot Hk Hne).
       apply HF;[exact Hk|lia]. }
 pose proof(pivot_range_induction__success_math (simplex_pivot_other_column fnum fden r i e) P cols(1,(n,d)) ltac:(lia)Hbase Hstep)as HI.
 change(P cols(simplex_pivot_other_prefix fnum fden r i e cols(1,(n,d)))) in HI.
 rewrite HE in HI. destruct HI as[_ [_ HH]]. exact(proj1(HH eq_refl)).
Qed.
Lemma pivot_before_values__success_math : forall n d cols r e b on od,
 Zlength n=400 -> Zlength d=400 -> 0<=r<16 -> 0<=cols<=24 ->
 0<=e<cols -> 0<=b<cols -> b<>e -> 0<Znth r d 1 ->
 (forall j,0<=j<cols -> 0<Znth(16+r*24+j)d 1) ->
 simplex_pivot_before_rows n d cols r e b=(1,(on,od)) ->
 Zlength on=400 /\ Zlength od=400 /\
 (0<Znth r od 1 /\ simplex_pivot_value on od r=
 (-(simplex_pivot_value n d r/simplex_pivot_value n d(16+r*24+e)))%Qc) /\
 (forall j,0<=j<cols -> 0<Znth(16+r*24+j)od 1 /\
 simplex_pivot_value on od(16+r*24+j)=
 (if Z.eq_dec j e then 0 else if Z.eq_dec j b then
  1/simplex_pivot_value n d(16+r*24+e) else
  -(simplex_pivot_value n d(16+r*24+j)/simplex_pivot_value n d(16+r*24+e)))%Qc) /\
 (forall k,0<=k<400 -> k<>r ->
  (forall j,0<=j<cols -> (16+r*24+j)<>k) ->
  simplex_pivot_observe(1,(on,od))k=simplex_pivot_observe(1,(n,d))k).
Proof.
 intros n d cols r e b on od Hn Hd Hr Hcols He Hb Hbe HDr HDA HE.
 set(pn:=Znth(16+r*24+e)n 0). set(pd:=Znth(16+r*24+e)d 1).
 assert(Hpd:1<=pd)by(unfold pd;specialize(HDA e He);lia).
 assert(Hrslot:0<=r<400)by lia.
 assert(Hbslot:0<=16+r*24+b<400)by lia.
 assert(Heslot:0<=16+r*24+e<400)by lia.
 unfold simplex_pivot_before_rows,simplex_pivot_start in HE. cbn beta iota zeta in HE. fold pn pd in HE.
 destruct(simplex_pivot_div pn pd r true(1,(n,d)))as[q0[n0 d0]]eqn:E0.
 destruct(simplex_pivot_row_prefix pn pd r e cols(q0,(n0,d0)))as[q1[n1 d1]]eqn:E1.
 destruct(simplex_pivot_recip pn pd(16+r*24+b)(q1,(n1,d1)))as[q2[n2 d2]]eqn:E2.
 assert(Q2:q2=1)by(pose proof(pivot_zero_back__success_math(16+r*24+e)(q2,(n2,d2)) ltac:(rewrite HE;reflexivity));exact H).
 subst q2.
 assert(Q1:q1=1)by(apply(pivot_recip_back__success_math pn pd(16+r*24+b)q1 n1 d1);rewrite E2;reflexivity).
 subst q1.
 assert(Q0:q0=1)by(pose proof(pivot_row_back__success_math pn pd r e cols(q0,(n0,d0))ltac:(rewrite E1;reflexivity));exact H).
 subst q0.
 pose proof(pivot_div_lengths__success_math pn pd r true 1 n d)as[N0 D0]. rewrite E0 in N0,D0. cbn [fst snd]in N0,D0.
 assert(HN0:Zlength n0=400)by lia. assert(HD0:Zlength d0=400)by lia.
 pose proof(pivot_row_lengths__success_math pn pd r e cols 1 n0 d0 HN0 HD0)as[N1 D1]. rewrite E1 in N1,D1. cbn [fst snd]in N1,D1.
 pose proof(pivot_recip_lengths__success_math pn pd(16+r*24+b)1 n1 d1)as[N2 D2]. rewrite E2 in N2,D2. cbn [fst snd]in N2,D2.
 assert(HN2:Zlength n2=400)by lia. assert(HD2:Zlength d2=400)by lia.
 pose proof(pivot_zero_lengths__success_math(16+r*24+e)1 n2 d2)as[N3 D3]. rewrite HE in N3,D3. cbn [fst snd]in N3,D3.
 assert(F0:forall k,0<=k<400 -> k<>r -> simplex_pivot_observe(1,(n0,d0))k=simplex_pivot_observe(1,(n,d))k).
 { intros k Hk Hkr. rewrite <-E0. apply pivot_div_frame__success_math;try assumption;lia. }
 assert(F1:forall k,0<=k<400 -> (forall j,0<=j<cols -> j<>e ->(16+r*24+j)<>k) -> simplex_pivot_observe(1,(n1,d1))k=simplex_pivot_observe(1,(n0,d0))k).
 { intros. rewrite <-E1. apply pivot_row_frame__success_math;assumption. }
 assert(F2:forall k,0<=k<400 ->(16+r*24+b)<>k -> simplex_pivot_observe(1,(n2,d2))k=simplex_pivot_observe(1,(n1,d1))k).
 { intros. rewrite <-E2. apply pivot_recip_frame__success_math;assumption. }
 assert(F3:forall k,0<=k<400 ->(16+r*24+e)<>k -> simplex_pivot_observe(1,(on,od))k=simplex_pivot_observe(1,(n2,d2))k).
 { intros. rewrite <-HE. apply pivot_zero_frame__success_math;assumption. }
 assert(DA0:forall j,0<=j<cols ->0<Znth(16+r*24+j)d0 1).
 { intros j Hj. rewrite(pivot_obs_den__success_math 1 n0 d0 1 n d _ (F0 (16+r*24+j) ltac:(lia)ltac:(lia))). apply HDA;assumption. }
 pose proof(pivot_row_values__success_math pn pd r e cols n0 d0 n1 d1 HN0 HD0 Hr Hcols Hpd DA0 E1)as RV.
 pose proof(pivot_div_value__success_math pn pd r true n d n0 d0 Hn Hd Hrslot ltac:(lia)Hpd E0)as[DR VR].
 assert(FR:simplex_pivot_observe(1,(on,od))r=simplex_pivot_observe(1,(n0,d0))r).
 { rewrite F3 by lia. rewrite F2 by lia. apply F1;[exact Hrslot|intros;lia]. }
 split;[lia|]. split;[lia|]. split.
 - split.
   + rewrite(pivot_obs_den__success_math 1 on od 1 n0 d0 r FR). exact DR.
   + rewrite(pivot_obs_value__success_math 1 on od 1 n0 d0 r FR). exact VR.
 - split.
   + intros j Hj. destruct(Z.eq_dec j e)as[->|Hje].
     * pose proof(pivot_zero_value__success_math(16+r*24+e)n2 d2 HN2 HD2 Heslot)as HZ. rewrite HE in HZ.
       change((Znth(16+r*24+e)on 0,Znth(16+r*24+e)od 1)=(0,1))in HZ. injection HZ as HZ1 HZ2.
       change(Znth(16+r*24+e)on 0=0)in HZ1. change(Znth(16+r*24+e)od 1=1)in HZ2.
       split;[rewrite HZ2;lia|]. unfold simplex_pivot_value. rewrite HZ1,HZ2. apply pivot_fraction_zero__success_math;lia.
     * destruct(Z.eq_dec j b)as[->|Hjb].
       -- pose proof(pivot_recip_value__success_math pn pd(16+r*24+b)n1 d1 n2 d2 N1 D1 Hbslot Hpd E2)as[DB VB].
          pose proof(F3(16+r*24+b)Hbslot ltac:(lia))as FB. split.
          ++ rewrite(pivot_obs_den__success_math 1 on od 1 n2 d2 _ FB). exact DB.
          ++ rewrite(pivot_obs_value__success_math 1 on od 1 n2 d2 _ FB). exact VB.
       -- destruct(RV j Hj Hje)as[DJ VJ].
          assert(FJ:simplex_pivot_observe(1,(on,od))(16+r*24+j)=simplex_pivot_observe(1,(n1,d1))(16+r*24+j)).
          { rewrite F3 by lia. apply F2;lia. }
          split.
          ++ rewrite(pivot_obs_den__success_math 1 on od 1 n1 d1 _ FJ). exact DJ.
          ++ rewrite(pivot_obs_value__success_math 1 on od 1 n1 d1 _ FJ). rewrite VJ.
             rewrite(pivot_obs_value__success_math 1 n0 d0 1 n d _ (F0 (16+r*24+j) ltac:(lia)ltac:(lia))). reflexivity.
   + intros k Hk Hkr Hkj. rewrite F3 by(auto;apply Hkj;exact He).
     rewrite F2 by(auto;apply Hkj;exact Hb).
     rewrite F1 by(auto;intros;apply Hkj;assumption). apply F0;assumption.
Qed.
Lemma pivot_other_row_lengths__success_math : forall r i e cols q n d,
 Zlength n=400 -> Zlength d=400 ->
 Zlength(fst(snd(simplex_pivot_other_row r e cols(q,(n,d))i)))=400 /\
 Zlength(snd(snd(simplex_pivot_other_row r e cols(q,(n,d))i)))=400.
Proof.
 intros r i e cols q n d HN HD. unfold simplex_pivot_other_row.
 destruct(Z.eqb i r);[cbn;auto|]. destruct(Z.eqb q 1);[|cbn;auto].
 destruct(Z.eqb(Znth(16+i*24+e)n 0)0).
 - pose proof(pivot_zero_lengths__success_math(16+i*24+e)q n d)as[A B]. rewrite A,B. auto.
 - destruct(simplex_pivot_addmul(Znth(16+i*24+e)n 0)(Znth(16+i*24+e)d 1)r i(q,(n,d)))as[t[nt dt]]eqn:ET.
   pose proof(pivot_addmul_lengths__success_math(Znth(16+i*24+e)n 0)(Znth(16+i*24+e)d 1)r i q n d)as[A B]. rewrite ET in A,B. cbn[fst snd]in A,B.
   assert(HNT:Zlength nt=400)by lia. assert(HDT:Zlength dt=400)by lia.
   destruct(simplex_pivot_other_prefix(Znth(16+i*24+e)n 0)(Znth(16+i*24+e)d 1)r i e cols(t,(nt,dt)))as[u[nu du]]eqn:EU.
   pose proof(pivot_other_lengths__success_math(Znth(16+i*24+e)n 0)(Znth(16+i*24+e)d 1)r i e cols t nt dt HNT HDT)as[C D]. rewrite EU in C,D. cbn[fst snd]in C,D.
   pose proof(pivot_zero_lengths__success_math(16+i*24+e)u nu du)as[E F]. rewrite E,F. auto.
Qed.
Lemma pivot_other_row_frame__success_math : forall r i e cols q n d k,
 Zlength n=400 -> Zlength d=400 -> 0<=i<16 -> 0<=cols<=24 -> 0<=e<cols ->
 0<=k<400 -> k<>i -> (forall j,0<=j<cols -> (16+i*24+j)<>k) ->
 simplex_pivot_observe(simplex_pivot_other_row r e cols(q,(n,d))i)k=simplex_pivot_observe(q,(n,d))k.
Proof.
 intros r i e cols q n d k HN HD Hi HC He Hk Hki Hother.
 set(P:=fun s:simplex_pivot_state=>Zlength(fst(snd s))=400 /\ Zlength(snd(snd s))=400 /\ simplex_pivot_observe s k=simplex_pivot_observe(q,(n,d))k).
 assert(HZ:forall s,P s -> P(simplex_pivot_zero(16+i*24+e)s)).
 { intros [t[nt dt]][A[B C]]. cbn[fst snd]in A,B,C. unfold P. pose proof(pivot_zero_lengths__success_math(16+i*24+e)t nt dt)as[E F]. rewrite E,F. split;[exact A|]. split;[exact B|]. rewrite pivot_zero_frame__success_math by(auto;try lia). exact C. }
 assert(HA:forall fnum fden src dst s,0<=dst<400 ->dst<>k ->P s ->P(simplex_pivot_addmul fnum fden src dst s)).
 { intros fnum fden src dst[t[nt dt]]Hdst Hne[A[B C]]. cbn[fst snd]in A,B,C. unfold P. pose proof(pivot_addmul_lengths__success_math fnum fden src dst t nt dt)as[E F]. rewrite E,F. split;[exact A|]. split;[exact B|]. rewrite pivot_addmul_frame__success_math by assumption. exact C. }
 assert(HP:forall fnum fden s,P s ->P(simplex_pivot_other_prefix fnum fden r i e cols s)).
 { intros fnum fden s HS. unfold simplex_pivot_other_prefix. apply(pivot_fold_invariant__success_math _ P).
   - intros t j Hj HT. apply In_Zrange in Hj. unfold simplex_pivot_other_column. destruct(Z.eqb j e);[exact HT|]. apply HA;[lia|apply Hother;exact Hj|exact HT].
   - exact HS. }
 assert(Hbase:P(q,(n,d)))by(unfold P;cbn;auto).
 assert(Hfinal:P(simplex_pivot_other_row r e cols(q,(n,d))i)).
 { unfold simplex_pivot_other_row. destruct(Z.eqb i r);[exact Hbase|]. destruct(Z.eqb q 1);[|exact Hbase]. apply HZ.
   destruct(Z.eqb(Znth(16+i*24+e)n 0)0);[exact Hbase|]. apply HP. apply HA;[lia|lia|exact Hbase]. }
 exact(proj2(proj2 Hfinal)).
Qed.
Lemma pivot_other_row_values__success_math : forall r i e cols n d on od,
 Zlength n=400 -> Zlength d=400 -> 0<=r<16 ->0<=i<16 ->i<>r ->
 0<=cols<=24 ->0<=e<cols ->0<Znth r d 1 ->0<Znth i d 1 ->
 (forall j,0<=j<cols ->0<Znth(16+r*24+j)d 1 /\0<Znth(16+i*24+j)d 1) ->
 simplex_pivot_other_row r e cols(1,(n,d))i=(1,(on,od)) ->
 Zlength on=400 /\Zlength od=400 /\
 (0<Znth i od 1 /\simplex_pivot_value on od i=
 (simplex_pivot_value n d i+simplex_pivot_value n d(16+i*24+e)*simplex_pivot_value n d r)%Qc) /\
 (forall j,0<=j<cols ->0<Znth(16+i*24+j)od 1 /\
 simplex_pivot_value on od(16+i*24+j)=
 (if Z.eq_dec j e then 0 else simplex_pivot_value n d(16+i*24+j)+
 simplex_pivot_value n d(16+i*24+e)*simplex_pivot_value n d(16+r*24+j))%Qc).
Proof.
 intros r i e cols n d on od HN HD Hr Hi Hir HC He DR DI DA HE.
 pose proof(pivot_other_row_lengths__success_math r i e cols 1 n d HN HD)as[NO DO]. rewrite HE in NO,DO. cbn[fst snd]in NO,DO.
 set(fnum:=Znth(16+i*24+e)n 0). set(fden:=Znth(16+i*24+e)d 1).
 assert(Hfd:0<fden)by(unfold fden;exact(proj2(DA e He))).
 assert(Eir:Z.eqb i r=false)by(apply Z.eqb_neq;exact Hir).
 unfold simplex_pivot_other_row in HE. rewrite Eir,Z.eqb_refl in HE. cbn beta iota zeta in HE. fold fnum fden in HE.
 destruct (if Z.eqb fnum 0 then (1,(n,d)) else
 simplex_pivot_other_prefix fnum fden r i e cols(simplex_pivot_addmul fnum fden r i(1,(n,d)))) as[q[mn md]]eqn:EM. pose proof(eq_trans(eq_sym(f_equal(fun s:simplex_pivot_state=>simplex_pivot_zero(16+i*24+e)s) EM))HE)as HZout. clear HE. rename HZout into HE.
 assert(Hq:q=1)by(pose proof(pivot_zero_back__success_math(16+i*24+e)(q,(mn,md))ltac:(rewrite HE;reflexivity));exact H). subst q.
 assert(HM:Zlength mn=400 /\Zlength md=400 /\
 (0<Znth i md 1 /\simplex_pivot_value mn md i=(simplex_pivot_value n d i+simplex_pivot_fraction fnum fden*simplex_pivot_value n d r)%Qc) /\
 (forall j,0<=j<cols ->j<>e ->0<Znth(16+i*24+j)md 1 /\simplex_pivot_value mn md(16+i*24+j)=
 (simplex_pivot_value n d(16+i*24+j)+simplex_pivot_fraction fnum fden*simplex_pivot_value n d(16+r*24+j))%Qc)).
 { destruct(Z.eqb fnum 0)eqn:EF.
   - injection EM as HMN HMD. subst mn md. apply Z.eqb_eq in EF.
     assert(HF:simplex_pivot_fraction fnum fden=0%Qc)by(rewrite EF;apply pivot_fraction_zero__success_math;exact Hfd).
     split;[exact HN|]. split;[exact HD|]. split.
     + split;[exact DI|]. rewrite HF. ring.
     + intros j Hj Hje. split;[exact(proj2(DA j Hj))|]. rewrite HF. ring.
   - destruct(simplex_pivot_addmul fnum fden r i(1,(n,d)))as[t[nt dt]]eqn:ET.
     assert(Ht:t=1)by(pose proof(pivot_other_back__success_math fnum fden r i e cols(t,(nt,dt))ltac:(rewrite EM;reflexivity));exact H). subst t.
     pose proof(pivot_addmul_lengths__success_math fnum fden r i 1 n d)as[NT DT]. rewrite ET in NT,DT. cbn[fst snd]in NT,DT.
     assert(HNT:Zlength nt=400)by lia. assert(HDT:Zlength dt=400)by lia.
     pose proof(pivot_other_lengths__success_math fnum fden r i e cols 1 nt dt HNT HDT)as[NM DM]. rewrite EM in NM,DM. cbn[fst snd]in NM,DM.
     assert(FT:forall k,0<=k<400 ->k<>i ->simplex_pivot_observe(1,(nt,dt))k=simplex_pivot_observe(1,(n,d))k).
     { intros k Hk Hki. rewrite <-ET. apply pivot_addmul_frame__success_math;try assumption;lia. }
     assert(DAT:forall j,0<=j<cols ->0<Znth(16+r*24+j)dt 1 /\0<Znth(16+i*24+j)dt 1).
     { intros j Hj. split.
       - rewrite(pivot_obs_den__success_math 1 nt dt 1 n d _ (FT(16+r*24+j)ltac:(lia)ltac:(lia))). exact(proj1(DA j Hj)).
       - rewrite(pivot_obs_den__success_math 1 nt dt 1 n d _ (FT(16+i*24+j)ltac:(lia)ltac:(lia))). exact(proj2(DA j Hj)). }
     pose proof(pivot_other_values__success_math fnum fden r i e cols nt dt mn md HNT HDT Hr Hi ltac:(lia) HC Hfd DAT EM)as VV.
     pose proof(pivot_addmul_value__success_math fnum fden r i n d nt dt HN HD ltac:(lia)Hfd DR DI ET)as[DTi VTi].
     assert(FI:simplex_pivot_observe(1,(mn,md))i=simplex_pivot_observe(1,(nt,dt))i).
     { rewrite <-EM. apply pivot_other_frame__success_math;try assumption;intros;lia. }
     split;[exact NM|]. split;[exact DM|]. split.
     + split.
       * rewrite(pivot_obs_den__success_math 1 mn md 1 nt dt i FI). exact DTi.
       * rewrite(pivot_obs_value__success_math 1 mn md 1 nt dt i FI). exact VTi.
     + intros j Hj Hje. destruct(VV j Hj Hje)as[DJ VJ]. split;[exact DJ|]. rewrite VJ.
       rewrite(pivot_obs_value__success_math 1 nt dt 1 n d _ (FT(16+i*24+j)ltac:(lia)ltac:(lia))).
       rewrite(pivot_obs_value__success_math 1 nt dt 1 n d _ (FT(16+r*24+j)ltac:(lia)ltac:(lia))). reflexivity. }
 destruct HM as[NM[DM[[DMI VMI]VMJ]]].
 assert(FZ:forall k,0<=k<400 ->(16+i*24+e)<>k ->simplex_pivot_observe(1,(on,od))k=simplex_pivot_observe(1,(mn,md))k).
 { intros k Hk Hne. rewrite <-HE. apply pivot_zero_frame__success_math;try assumption;lia. }
 split;[exact NO|]. split;[exact DO|]. split.
 - pose proof(FZ i ltac:(lia)ltac:(lia))as FI. split.
   + rewrite(pivot_obs_den__success_math 1 on od 1 mn md i FI). exact DMI.
   + rewrite(pivot_obs_value__success_math 1 on od 1 mn md i FI). exact VMI.
 - intros j Hj. destruct(Z.eq_dec j e)as[->|Hje].
   + pose proof(pivot_zero_value__success_math(16+i*24+e)mn md NM DM ltac:(lia))as HZ. rewrite HE in HZ.
     change((Znth(16+i*24+e)on 0,Znth(16+i*24+e)od 1)=(0,1))in HZ. injection HZ as HZ1 HZ2.
     change(Znth(16+i*24+e)on 0=0)in HZ1. change(Znth(16+i*24+e)od 1=1)in HZ2.
     split;[rewrite HZ2;lia|]. unfold simplex_pivot_value. rewrite HZ1,HZ2. apply pivot_fraction_zero__success_math;lia.
   + destruct(VMJ j Hj Hje)as[DJ VJ]. pose proof(FZ(16+i*24+j)ltac:(lia)ltac:(lia))as FJ. split.
     * rewrite(pivot_obs_den__success_math 1 on od 1 mn md _ FJ). exact DJ.
     * rewrite(pivot_obs_value__success_math 1 on od 1 mn md _ FJ). exact VJ.
Qed.
Lemma pivot_other_row_back__success_math : forall r i e cols q n d,
 fst(simplex_pivot_other_row r e cols(q,(n,d))i)=1 ->q=1.
Proof. intros. unfold simplex_pivot_other_row in H. destruct(Z.eqb i r);[exact H|]. destruct(Z.eqb q 1)eqn:EQ;[apply Z.eqb_eq in EQ;exact EQ|exact H]. Qed.
Lemma pivot_rows_values__success_math : forall r e cols rows n d on od,
 Zlength n=400 ->Zlength d=400 ->0<=rows<=16 ->0<=r<rows ->
 0<=cols<=24 ->0<=e<cols ->
 (forall i,0<=i<rows ->0<Znth i d 1 /\forall j,0<=j<cols ->0<Znth(16+i*24+j)d 1) ->
 simplex_pivot_rows_prefix r e cols rows(1,(n,d))=(1,(on,od)) ->
 Zlength on=400 /\Zlength od=400 /\
 (simplex_pivot_observe(1,(on,od))r=simplex_pivot_observe(1,(n,d))r /\
 forall j,0<=j<cols ->simplex_pivot_observe(1,(on,od))(16+r*24+j)=simplex_pivot_observe(1,(n,d))(16+r*24+j)) /\
 (forall i,0<=i<rows ->i<>r ->
 (0<Znth i od 1 /\simplex_pivot_value on od i=(simplex_pivot_value n d i+simplex_pivot_value n d(16+i*24+e)*simplex_pivot_value n d r)%Qc) /\
 forall j,0<=j<cols ->0<Znth(16+i*24+j)od 1 /\simplex_pivot_value on od(16+i*24+j)=
 (if Z.eq_dec j e then 0 else simplex_pivot_value n d(16+i*24+j)+simplex_pivot_value n d(16+i*24+e)*simplex_pivot_value n d(16+r*24+j))%Qc).
Proof.
 intros r e cols rows n d on od HN HD HM Hr HC He DA HE.
 set(P:=fun t(s:simplex_pivot_state)=>Zlength(fst(snd s))=400 /\Zlength(snd(snd s))=400 /\
 (fst s=1 ->
 (simplex_pivot_observe s r=simplex_pivot_observe(1,(n,d))r /\forall j,0<=j<cols ->simplex_pivot_observe s(16+r*24+j)=simplex_pivot_observe(1,(n,d))(16+r*24+j)) /\
 (forall l,0<=l<t ->l<>r ->
 (0<Znth l(snd(snd s))1 /\simplex_pivot_value(fst(snd s))(snd(snd s))l=(simplex_pivot_value n d l+simplex_pivot_value n d(16+l*24+e)*simplex_pivot_value n d r)%Qc) /\
 forall j,0<=j<cols ->0<Znth(16+l*24+j)(snd(snd s))1 /\simplex_pivot_value(fst(snd s))(snd(snd s))(16+l*24+j)=
 (if Z.eq_dec j e then 0 else simplex_pivot_value n d(16+l*24+j)+simplex_pivot_value n d(16+l*24+e)*simplex_pivot_value n d(16+r*24+j))%Qc) /\
 (forall l,t<=l<rows ->l<>r ->simplex_pivot_observe s l=simplex_pivot_observe(1,(n,d))l /\forall j,0<=j<cols ->simplex_pivot_observe s(16+l*24+j)=simplex_pivot_observe(1,(n,d))(16+l*24+j)))).
 assert(P0:P 0(1,(n,d))).
 { unfold P. cbn[fst snd]. split;[exact HN|]. split;[exact HD|]. intros _. split;[split;reflexivity|]. split;[intros;lia|]. intros l Hl Hlr. split;reflexivity. }
 assert(PS:forall t s,0<=t<rows ->P t s ->P(t+1)(simplex_pivot_other_row r e cols s t)).
 { intros t[q[cn cd]]Ht[NC[DC HH]]. cbn[fst snd]in NC,DC,HH.
   destruct(Z.eq_dec t r)as[Htr|Htr].
   - subst t. unfold simplex_pivot_other_row. rewrite Z.eqb_refl. unfold P. cbn[fst snd]. split;[exact NC|]. split;[exact DC|]. intro Hq. destruct(HH Hq)as[HP[HV HF]]. split;[exact HP|]. split.
     + intros l Hl Hlr. apply HV;[lia|exact Hlr].
     + intros l Hl Hlr. apply HF;[lia|exact Hlr].
   - destruct(simplex_pivot_other_row r e cols(q,(cn,cd))t)as[oq[nn dd]]eqn:ES.
     pose proof(pivot_other_row_lengths__success_math r t e cols q cn cd NC DC)as[NN DD]. rewrite ES in NN,DD. cbn[fst snd]in NN,DD.
     unfold P. cbn[fst snd]. split;[exact NN|]. split;[exact DD|]. intro Ho. subst oq.
     assert(Q:q=1)by(apply(pivot_other_row_back__success_math r t e cols q cn cd);rewrite ES;reflexivity). subst q.
     destruct(HH eq_refl)as[[PR PA][HV HF]]. destruct(HF t ltac:(lia)Htr)as[TR TA].
     assert(DR:0<Znth r cd 1).
     { rewrite(pivot_obs_den__success_math 1 cn cd 1 n d r PR). exact(proj1(DA r Hr)). }
     assert(DT:0<Znth t cd 1).
     { rewrite(pivot_obs_den__success_math 1 cn cd 1 n d t TR). exact(proj1(DA t Ht)). }
     assert(DDAT:forall j,0<=j<cols ->0<Znth(16+r*24+j)cd 1 /\0<Znth(16+t*24+j)cd 1).
     { intros j Hj. split.
       - rewrite(pivot_obs_den__success_math 1 cn cd 1 n d _ (PA j Hj)). exact(proj2(DA r Hr)j Hj).
       - rewrite(pivot_obs_den__success_math 1 cn cd 1 n d _ (TA j Hj)). exact(proj2(DA t Ht)j Hj). }
     pose proof(pivot_other_row_values__success_math r t e cols cn cd nn dd NC DC ltac:(lia)ltac:(lia)Htr HC He DR DT DDAT ES)as[_[_[VR VA]]].
     assert(FF:forall l,0<=l<rows ->l<>t ->simplex_pivot_observe(1,(nn,dd))l=simplex_pivot_observe(1,(cn,cd))l /\forall j,0<=j<cols ->simplex_pivot_observe(1,(nn,dd))(16+l*24+j)=simplex_pivot_observe(1,(cn,cd))(16+l*24+j)).
     { intros l Hl Hlt. split.
       - rewrite <-ES. apply pivot_other_row_frame__success_math;try assumption;try lia;intros;lia.
       - intros j Hj. rewrite <-ES. apply pivot_other_row_frame__success_math;try assumption;try lia;intros;lia. }
     destruct(FF r Hr ltac:(lia))as[FR FA]. split.
     + split;[etransitivity;[exact FR|exact PR]|]. intros j Hj. etransitivity;[exact(FA j Hj)|exact(PA j Hj)].
     + split.
       * intros l Hl Hlr. destruct(Z.eq_dec l t)as[->|Hlt].
         -- split.
            ++ destruct VR as[DVR VVR]. split;[exact DVR|]. rewrite VVR.
               rewrite(pivot_obs_value__success_math 1 cn cd 1 n d t TR),(pivot_obs_value__success_math 1 cn cd 1 n d r PR),(pivot_obs_value__success_math 1 cn cd 1 n d _ (TA e He)). reflexivity.
            ++ intros j Hj. destruct(VA j Hj)as[DVA VVA]. split;[exact DVA|]. rewrite VVA.
               rewrite(pivot_obs_value__success_math 1 cn cd 1 n d _ (TA j Hj)),(pivot_obs_value__success_math 1 cn cd 1 n d _ (TA e He)),(pivot_obs_value__success_math 1 cn cd 1 n d _ (PA j Hj)). reflexivity.
         -- destruct(HV l ltac:(lia)Hlr)as[[DL VL]VJ]. destruct(FF l ltac:(lia)Hlt)as[FL FJ]. split.
            ++ split.
               ** rewrite(pivot_obs_den__success_math 1 nn dd 1 cn cd l FL). exact DL.
               ** rewrite(pivot_obs_value__success_math 1 nn dd 1 cn cd l FL). exact VL.
            ++ intros j Hj. destruct(VJ j Hj)as[DJ VJj]. split.
               ** rewrite(pivot_obs_den__success_math 1 nn dd 1 cn cd _ (FJ j Hj)). exact DJ.
               ** rewrite(pivot_obs_value__success_math 1 nn dd 1 cn cd _ (FJ j Hj)). exact VJj.
       * intros l Hl Hlr. destruct(HF l ltac:(lia)Hlr)as[FL FJ]. destruct(FF l ltac:(lia)ltac:(lia))as[GL GJ]. split.
         -- etransitivity;[exact GL|exact FL].
         -- intros j Hj. etransitivity;[exact(GJ j Hj)|exact(FJ j Hj)]. }
 pose proof(pivot_range_induction__success_math (simplex_pivot_other_row r e cols)P rows(1,(n,d))ltac:(lia)P0 PS)as OUT.
 change(P rows(simplex_pivot_rows_prefix r e cols rows(1,(n,d))))in OUT. rewrite HE in OUT.
 destruct OUT as[NO[DO HH]]. split;[exact NO|]. split;[exact DO|]. destruct(HH eq_refl)as[HP[HV HF]]. split;[exact HP|exact HV].
Qed.
Lemma pivot_compute_closed__success_math : forall n d rows cols r e b on od,
 Zlength n=400 ->Zlength d=400 ->0<=rows<=16 ->0<=r<rows ->
 0<=cols<=24 ->0<=e<cols ->0<=b<cols ->b<>e ->
 (forall i,0<=i<rows ->0<Znth i d 1 /\forall j,0<=j<cols ->0<Znth(16+i*24+j)d 1) ->
 simplex_pivot_compute n d rows cols r e b=(1,(on,od)) ->
 simplex_pivot_closed n d on od rows cols r e b.
Proof.
 intros n d rows cols r e b on od HN HD HM Hr HC He Hb Hbe DA HE.
 assert(HP:simplex_pivot_value n d(16+r*24+e)<>0%Qc).
 { unfold simplex_pivot_value. apply pivot_fraction_nonzero__success_math.
   - exact(proj2(DA r Hr)e He).
   - exact(pivot_compute_nonzero__success_math n d rows cols r e b on od HE). }
 change(simplex_pivot_rows_prefix r e cols rows(simplex_pivot_before_rows n d cols r e b)=(1,(on,od)))in HE.
 destruct(simplex_pivot_before_rows n d cols r e b)as[q[bn bd]]eqn:EB.
 assert(Hq:q=1)by(pose proof(pivot_rows_back__success_math r e cols rows(q,(bn,bd))ltac:(rewrite HE;reflexivity));exact H). subst q.
 pose proof(pivot_before_values__success_math n d cols r e b bn bd HN HD ltac:(lia)HC He Hb Hbe(proj1(DA r Hr))(proj2(DA r Hr))EB)as[NB[DB[[DBr VBr][VB FB]]]].
 assert(FI:forall i,0<=i<rows ->i<>r ->simplex_pivot_observe(1,(bn,bd))i=simplex_pivot_observe(1,(n,d))i /\forall j,0<=j<cols ->simplex_pivot_observe(1,(bn,bd))(16+i*24+j)=simplex_pivot_observe(1,(n,d))(16+i*24+j)).
 { intros i Hi Hir. split.
   - apply FB;lia.
   - intros j Hj. apply FB;lia. }
 assert(DAB:forall i,0<=i<rows ->0<Znth i bd 1 /\forall j,0<=j<cols ->0<Znth(16+i*24+j)bd 1).
 { intros i Hi. destruct(Z.eq_dec i r)as[->|Hir].
   - split;[exact DBr|]. intros j Hj. exact(proj1(VB j Hj)).
   - destruct(FI i Hi Hir)as[FR FA]. split.
     + rewrite(pivot_obs_den__success_math 1 bn bd 1 n d i FR). exact(proj1(DA i Hi)).
     + intros j Hj. rewrite(pivot_obs_den__success_math 1 bn bd 1 n d _ (FA j Hj)). exact(proj2(DA i Hi)j Hj). }
 pose proof(pivot_rows_values__success_math r e cols rows bn bd on od NB DB HM Hr HC He DAB HE)as[_[_[[FR FA]VO]]].
 unfold simplex_pivot_closed. cbn zeta. split;[exact HP|]. split.
 - rewrite(pivot_obs_value__success_math 1 on od 1 bn bd r FR). rewrite VBr. field;exact HP.
 - split.
   + intros j Hj. rewrite(pivot_obs_value__success_math 1 on od 1 bn bd _ (FA j Hj)). rewrite(proj2(VB j Hj)). destruct(Z.eq_dec j e);[reflexivity|]. destruct(Z.eq_dec j b);[reflexivity|]. field;exact HP.
   + split.
     * intros i Hi Hir. destruct(FI i Hi Hir)as[FIR FIA]. destruct(VO i Hi Hir)as[[DI VI]VJ]. rewrite VI.
       rewrite(pivot_obs_value__success_math 1 bn bd 1 n d i FIR),(pivot_obs_value__success_math 1 bn bd 1 n d _ (FIA e He)),(pivot_obs_value__success_math 1 on od 1 bn bd r FR). reflexivity.
     * intros i j Hi Hir Hj. destruct(FI i Hi Hir)as[FIR FIA]. destruct(VO i Hi Hir)as[VI VJ]. rewrite(proj2(VJ j Hj)).
       rewrite(pivot_obs_value__success_math 1 bn bd 1 n d _ (FIA j Hj)),(pivot_obs_value__success_math 1 bn bd 1 n d _ (FIA e He)),(pivot_obs_value__success_math 1 on od 1 bn bd _ (FA j Hj)). reflexivity.
Qed.
Lemma pivot_sums__success_math (J:list Z)(A C z:Z->Qc)(e b:Z)(p:Qc) :
 (NoDup J ->In e J ->In b J ->b<>e ->p<>0 ->A e=p ->A b=0 ->
 (forall j,In j J ->C j=if Z.eq_dec j e then 0 else if Z.eq_dec j b then 1/p else -A j/p) ->
 let U:=simplex_pivot_linear J(fun j=>if Z.eq_dec j e then 0 else A j*z j)in
 simplex_pivot_linear J(fun j=>A j*z j)=p*z e+U /\
 simplex_pivot_linear J(fun j=>C j*z j)=z b/p-U/p)%Qc.
Proof.
 intros Hnd He Hb Hbe Hp Hae Hab HC. cbn zeta. split.
 - rewrite(simplex_pivot_linear_split J(fun j=>(A j*z j)%Qc)e Hnd He),Hae. reflexivity.
 - rewrite(simplex_pivot_linear_split J(fun j=>(C j*z j)%Qc)b Hnd Hb).
   assert(Hcb:(C b=1/p)%Qc).
   { rewrite(HC b Hb). destruct(Z.eq_dec b e);[contradiction|]. destruct(Z.eq_dec b b);[reflexivity|contradiction]. }
   rewrite Hcb.
   assert(Hrest:(simplex_pivot_linear J(fun j=>if Z.eq_dec j b then 0 else C j*z j)=
    (-(1%Qc)/p)*simplex_pivot_linear J(fun j=>if Z.eq_dec j e then 0 else A j*z j))%Qc).
   { transitivity(simplex_pivot_linear J(fun j=>((-(1%Qc)/p)*(if Z.eq_dec j e then 0 else A j*z j))%Qc)).
     - apply simplex_pivot_linear_ext. intros j Hj. destruct(Z.eq_dec j b)as[->|Hjb].
       + destruct(Z.eq_dec b e);[contradiction|]. rewrite Hab. ring.
       + rewrite(HC j Hj). destruct(Z.eq_dec j e)as[->|Hje].
         * ring.
         * destruct(Z.eq_dec j b);[contradiction|]. field;exact Hp.
     - apply simplex_pivot_linear_scale. }
   rewrite Hrest. field;exact Hp.
Qed.
Lemma pivot_other_sums__success_math (J:list Z)(A B C z:Z->Qc)(e:Z) :
 (NoDup J ->In e J ->C e=0 ->
 (forall j,In j J ->B j=if Z.eq_dec j e then 0 else A j+A e*C j) ->
 let V:=simplex_pivot_linear J(fun j=>if Z.eq_dec j e then 0 else A j*z j)in
 let W:=simplex_pivot_linear J(fun j=>C j*z j)in
 simplex_pivot_linear J(fun j=>A j*z j)=A e*z e+V /\
 simplex_pivot_linear J(fun j=>B j*z j)=V+A e*W)%Qc.
Proof.
 intros Hnd He Hce HB. cbn zeta. split.
 - exact(simplex_pivot_linear_split J(fun j=>(A j*z j)%Qc)e Hnd He).
 - transitivity(simplex_pivot_linear J(fun j=>((if Z.eq_dec j e then 0 else A j*z j)+A e*(C j*z j))%Qc)).
   + apply simplex_pivot_linear_ext. intros j Hj. rewrite(HB j Hj). destruct(Z.eq_dec j e)as[->|Hje];[rewrite Hce;ring|ring].
   + rewrite simplex_pivot_linear_add,simplex_pivot_linear_scale. reflexivity.
Qed.
Lemma pivot_tableau_equiv__success_math (J:list Z)(rows r e b:Z)(bs:list Z)(D T:Z->Qc)(A C:Z->Z->Qc) :
 (Zlength bs=rows ->(0<=r<rows)%Z ->NoDup J ->In e J ->In b J ->
 b<>e ->b=Znth r bs 0%Z ->A r b=0 ->A r e<>0 ->T r= -D r/A r e ->
 (forall j,In j J ->C r j=if Z.eq_dec j e then 0 else if Z.eq_dec j b then 1/A r e else -A r j/A r e) ->
 (forall i,(0<=i<rows)%Z ->i<>r ->T i=D i+A i e*T r) ->
 (forall i j,(0<=i<rows)%Z ->i<>r ->In j J ->C i j=if Z.eq_dec j e then 0 else A i j+A i e*C r j) ->
 forall z:Z->Qc,
 (forall i,(0<=i<rows)%Z ->z(Znth i bs 0%Z)=D i+simplex_pivot_linear J(fun j=>A i j*z j)) <->
 (forall i,(0<=i<rows)%Z ->z(Znth i(replace_Znth r e bs)0%Z)=T i+simplex_pivot_linear J(fun j=>C i j*z j)))%Qc.
Proof.
 intros Hlen Hr Hnd He Hb Hbe Hbasis Hab Hp Htr Hcr Hti Hci z.
 pose proof(pivot_sums__success_math J(A r)(C r)z e b(A r e)Hnd He Hb Hbe Hp eq_refl Hab Hcr)as HS.
 cbn zeta in HS. destruct HS as[HSold HSnew].
 set(U:=simplex_pivot_linear J(fun j=>if Z.eq_dec j e then 0%Qc else (A r j*z j)%Qc))in *.
 assert(Hrow:((z b=D r+simplex_pivot_linear J(fun j=>A r j*z j)) <->
 (z e=T r+simplex_pivot_linear J(fun j=>C r j*z j)))%Qc).
 { rewrite HSold,HSnew,Htr.
   replace(D r+(A r e*z e+U))%Qc with (D r+A r e*z e+U)%Qc by ring.
   replace(-D r/A r e+(z b/A r e-U/A r e))%Qc with (-D r/A r e+z b/A r e-U/A r e)%Qc by ring.
   apply simplex_pivot_row_algebra. exact Hp. }
 assert(Hce:C r e=0%Qc).
 { rewrite(Hcr e He). destruct(Z.eq_dec e e);[reflexivity|contradiction]. }
 assert(Hothers:forall i,(0<=i<rows)%Z ->i<>r ->
 (z e=T r+simplex_pivot_linear J(fun j=>C r j*z j))%Qc ->
 ((z(Znth i bs 0%Z)=D i+simplex_pivot_linear J(fun j=>A i j*z j)) <->
 (z(Znth i bs 0%Z)=T i+simplex_pivot_linear J(fun j=>C i j*z j)))%Qc).
 { intros i Hi Hir HPe.
   pose proof(pivot_other_sums__success_math J(A i)(C i)(C r)z e Hnd He Hce(fun j Hj=>Hci i j Hi Hir Hj))as HSi.
   cbn zeta in HSi. destruct HSi as[HO HNew]. rewrite HO,HNew,(Hti i Hi Hir).
   set(V:=simplex_pivot_linear J(fun j=>if Z.eq_dec j e then 0%Qc else(A i j*z j)%Qc)).
   set(W:=simplex_pivot_linear J(fun j=>(C r j*z j)%Qc))in *.
   replace(D i+(A i e*z e+V))%Qc with (D i+A i e*z e+V)%Qc by ring.
   apply simplex_pivot_other_algebra. exact HPe. }
 split;intro H.
 - assert(HPe:(z e=T r+simplex_pivot_linear J(fun j=>C r j*z j))%Qc).
   { apply(proj1 Hrow). rewrite Hbasis. apply H. exact Hr. }
   intros i Hi. destruct(Z.eq_dec i r)as[->|Hir].
   + rewrite Znth_replace_Znth_Same by lia. exact HPe.
   + rewrite Znth_replace_Znth_Diff by lia. apply(proj1(Hothers i Hi Hir HPe)). apply H. exact Hi.
 - assert(HPe:(z e=T r+simplex_pivot_linear J(fun j=>C r j*z j))%Qc).
   { specialize(H r Hr). rewrite Znth_replace_Znth_Same in H by lia. exact H. }
   intros i Hi. destruct(Z.eq_dec i r)as[->|Hir].
   + rewrite <-Hbasis. apply(proj2 Hrow). exact HPe.
   + apply(proj2(Hothers i Hi Hir HPe)). specialize(H i Hi). rewrite Znth_replace_Znth_Diff in H by lia. exact H.
Qed.
Lemma pivot_nodup_snoc__success_math (l:list Z)(x:Z) : NoDup l ->~In x l ->NoDup(l++[x]).
Proof.
 intro Hnd. induction Hnd as[|a l Hna Hnd IH];intro Hx;cbn.
 - constructor;[cbn;tauto|constructor].
 - constructor.
   + intro H. apply in_app_or in H. destruct H as[H|H].
     * exact(Hna H).
     * cbn in H. destruct H as[Hax|Hfalse];[|contradiction]. apply Hx. left. congruence.
   + apply IH. intro Hin. apply Hx. right. exact Hin.
Qed.
Lemma pivot_range_nodup__success_math (c:Z) : 0<=c ->NoDup(Zrange 0 c).
Proof.
 intro Hc. assert(H:forall k:nat,NoDup(Zrange 0(Z.of_nat k))).
 { intro k. induction k as[|k IH].
   - change(NoDup([]:list Z)). constructor.
   - rewrite Nat2Z.inj_succ. replace(Z.succ(Z.of_nat k))with(Z.of_nat k+1)by lia.
     rewrite simplex_scan_range_snoc by lia. apply pivot_nodup_snoc__success_math;[exact IH|]. intro Hin. apply In_Zrange in Hin. lia. }
 rewrite <-(Z2Nat.id c Hc). apply H.
Qed.
Lemma pivot_closed_equiv__success_math (n d on od bs:list Z)(rows cols r e:Z) :
 Zlength bs=rows ->0<=r<rows ->0<=e<cols ->0<=Znth r bs 0<cols ->Znth r bs 0<>e ->
 simplex_pivot_value n d(16+r*24+Znth r bs 0)=0%Qc ->
 simplex_pivot_closed n d on od rows cols r e(Znth r bs 0) ->
 simplex_pivot_equiv n d on od bs rows cols r e.
Proof.
 intros Hlen Hr He Hb Hbe Hab Hclosed. unfold simplex_pivot_closed in Hclosed. cbn zeta in Hclosed.
 destruct Hclosed as[Hp[Htr[Hcr[Hti Hci]]]]. unfold simplex_pivot_equiv,simplex_pivot_equations.
 apply(pivot_tableau_equiv__success_math(Zrange 0 cols)rows r e(Znth r bs 0)bs
 (fun i=>simplex_pivot_value n d i)(fun i=>simplex_pivot_value on od i)
 (fun i j=>simplex_pivot_value n d(16+i*24+j))(fun i j=>simplex_pivot_value on od(16+i*24+j))).
 - exact Hlen.
 - exact Hr.
 - apply pivot_range_nodup__success_math. lia.
 - apply In_Zrange. lia.
 - apply In_Zrange. lia.
 - exact Hbe.
 - reflexivity.
 - exact Hab.
 - exact Hp.
 - exact Htr.
 - intros j Hj. apply In_Zrange in Hj. apply Hcr. lia.
 - exact Hti.
 - intros i j Hi Hir Hj. apply In_Zrange in Hj. apply Hci;assumption.
Qed.
Lemma filter_absent__success_math : forall xs k, ~In k xs -> filter(fun x=>negb(Z.eqb x k)) xs=xs.
Proof. induction xs;intros;simpl;auto. assert(E:(a =? k)=false) by (apply Z.eqb_neq;intro;subst;apply H;left;reflexivity). rewrite E.
 simpl. f_equal. apply IHxs. intro K;apply H;right;exact K. Qed.
Lemma iter_merge__success_math : forall xs (F:Z->Assertion) k, NoDup xs -> In k xs ->
 F k ** iter_sepcon(map F(filter(fun x=>negb(Z.eqb x k))xs)) |-- iter_sepcon(map F xs).
Proof. intros xs F k H;induction H;intro Hin;[contradiction|]. simpl.
 destruct(Z.eq_dec x k) as [->|Hne].
 - rewrite Z.eqb_refl. simpl. rewrite filter_absent__success_math by exact H. rewrite !logic_equiv_iter_sepcon_cons. reflexivity.
 - rewrite (proj2(Z.eqb_neq x k) Hne). simpl. rewrite !logic_equiv_iter_sepcon_cons. sep_apply_r_atomic(IHNoDup ltac:(destruct Hin;[contradiction|assumption])).
   csimpl. sepcon_right_assoc. cancel(F k). cancel(F x). reflexivity.
Qed.
Lemma filter_two__success_math : forall xs a b,
 filter(fun x=>negb(Z.eqb x a || Z.eqb x b))xs=
 filter(fun x=>negb(Z.eqb x b))(filter(fun x=>negb(Z.eqb x a))xs).
Proof. induction xs;intros;simpl;auto. destruct(a =? a0) eqn:E;destruct(a =? b) eqn:F;simpl;rewrite ?E,?F;simpl;rewrite IHxs;reflexivity. Qed.
Lemma iter_merge_two__success_math : forall xs (F:Z->Assertion) a b,NoDup xs -> In a xs -> In b xs -> a<>b ->
 F a ** F b ** iter_sepcon(map F(filter(fun x=>negb(Z.eqb x a || Z.eqb x b))xs)) |-- iter_sepcon(map F xs).
Proof. intros xs F a b H Ha Hb Hne. rewrite filter_two__success_math.
 assert(Hb':In b(filter(fun x=>negb(Z.eqb x a))xs)).
 { apply filter_In. split;[exact Hb|]. rewrite(proj2(Z.eqb_neq b a) ltac:(lia));reflexivity. }
 sep_apply_r_atomic(iter_merge__success_math xs F a H Ha).
 sep_apply_r_atomic(iter_merge__success_math _ F b (NoDup_filter _ H) Hb').
 csimpl. sepcon_right_assoc. cancel(F a). cancel(F b). reflexivity. Qed.
Lemma range_cons__success_math : forall lo hi,lo<hi -> Zrange lo hi=lo::Zrange(lo+1)hi.
Proof. intros. unfold Zrange. replace(hi-lo) with (Z.succ(hi-(lo+1))) by lia.
 rewrite Z2Nat.inj_succ by lia. reflexivity. Qed.
Lemma iter_array_rec__success_math : forall l x lo hi,Zlength l=hi-lo ->
 iter_sepcon(map(fun k=>StoreIntAsElement.storeA x k(Znth(k-lo)l 0))(Zrange lo hi)) |--
 store_array_rec StoreIntAsElement.storeA x lo hi l.
Proof. induction l as [|a l IH];intros x lo hi Hl.
 - rewrite Zlength_nil in Hl. assert(hi=lo)by lia. subst hi.
   unfold Zrange. rewrite Z.sub_diag. simpl. rewrite logic_equiv_iter_sepcon_nil.
   simpl store_array_rec. split_pure_spatial;[reflexivity|split_pures;dump_pre_spatial;reflexivity].
 - rewrite Zlength_cons in Hl. simpl store_array_rec. rewrite range_cons__success_math by(pose proof(Zlength_nonneg l);lia).
   simpl map. rewrite logic_equiv_iter_sepcon_cons. replace(lo-lo)with 0 by lia. rewrite Znth0_cons.
   assert(E:map(fun k=>StoreIntAsElement.storeA x k(Znth(k-lo)(a::l)0))(Zrange(lo+1)hi)=
            map(fun k=>StoreIntAsElement.storeA x k(Znth(k-(lo+1))l 0))(Zrange(lo+1)hi)).
   { apply map_ext_in. intros k Hk. apply In_Zrange in Hk. rewrite Znth_cons by lia.
     replace(k-lo-1)with(k-(lo+1))by lia. reflexivity. }
   rewrite E. sep_apply_r_atomic(IH x (lo+1)hi ltac:(lia)). cancel(StoreIntAsElement.storeA x lo a). reflexivity.
Qed.
Lemma iter_full__success_math : forall x v ib,Zlength ib=v ->
 iter_sepcon(map(fun k=>(x+k*sizeof(INT)) # Int |-> Znth k ib 0)(Zrange 0 v)) |-- IntArray.full x v ib.
Proof. intros x v ib Hl. unfold IntArray.full,store_array.
 sep_apply_r_atomic(iter_array_rec__success_math ib x 0 v ltac:(lia)).
 assert(E:map(fun k=>StoreIntAsElement.storeA x k(Znth(k-0)ib 0))(Zrange 0 v)=map(fun k=>(x+k*sizeof(INT)) # Int |-> Znth k ib 0)(Zrange 0 v)).
 { apply map_ext. intro k. replace(k-0)with k by lia. reflexivity. } rewrite E. reflexivity.
Qed.
Lemma pivot_marks_merge__success_math : forall s v ib b e,Zlength ib=v ->0<=b<v ->0<=e<v ->b<>e ->
 simplex_pivot_flags_except s v ib b e **
 (((&((s) # "SxState" ->ₛ "is_basic"))+b*sizeof(INT)) # Int |-> 0) **
 (((&((s) # "SxState" ->ₛ "is_basic"))+e*sizeof(INT)) # Int |-> 1) |--
 IntArray.full (&((s) # "SxState" ->ₛ "is_basic")) v (simplex_pivot_marks ib b e 1).
Proof. intros s v ib b e HL HB HE Hne. unfold simplex_pivot_marks. cbn iota.
 sep_apply_r_atomic(iter_full__success_math (&((s) # "SxState" ->ₛ "is_basic")) v (replace_Znth e 1(replace_Znth b 0 ib)) ltac:(rewrite !Zlength_replace_Znth;exact HL)).
 sep_apply_r_atomic(iter_merge_two__success_math (Zrange 0 v)
 (fun k=>((&((s) # "SxState" ->ₛ "is_basic"))+k*sizeof(INT)) # Int |-> Znth k (replace_Znth e 1(replace_Znth b 0 ib)) 0)
 b e (NoDup_Zrange 0 v) ltac:(apply In_Zrange;lia) ltac:(apply In_Zrange;lia) Hne).
 rewrite Znth_replace_Znth_Diff by(rewrite ?Zlength_replace_Znth;lia).
 rewrite !Znth_replace_Znth_Same by(rewrite ?Zlength_replace_Znth;lia).
 unfold simplex_pivot_flags_except.
 assert(E:map(fun k=>((&((s) # "SxState" ->ₛ "is_basic"))+k*sizeof(INT)) # Int |-> Znth k (replace_Znth e 1(replace_Znth b 0 ib)) 0)
 (filter(fun k=>negb(Z.eqb k b || Z.eqb k e))(Zrange 0 v))=
 map(fun k=>((&((s) # "SxState" ->ₛ "is_basic"))+k*sizeof(INT)) # Int |-> Znth k ib 0)
 (filter(fun k=>negb(Z.eqb k b || Z.eqb k e))(Zrange 0 v))).
 { apply map_ext_in. intros k Hk. apply filter_In in Hk. destruct Hk as[Hk Hneq]. apply In_Zrange in Hk.
   apply Bool.negb_true_iff in Hneq. apply Bool.orb_false_iff in Hneq. destruct Hneq as[Hkb Hke].
   apply Z.eqb_neq in Hkb. apply Z.eqb_neq in Hke. rewrite !Znth_replace_Znth_Diff by(rewrite ?Zlength_replace_Znth;lia). reflexivity. }
 rewrite <- E. csimpl. sepcon_right_assoc. cancel. reflexivity. 
Qed.
Lemma nodup_map_inj__outer_commit : forall (f:Z->Z) xs,
 NoDup xs -> (forall x y, In x xs -> In y xs -> f x=f y -> x=y) -> NoDup(map f xs).
Proof. intros f xs H;induction H;intros Hf;simpl;constructor.
 - intro K. apply in_map_iff in K. destruct K as [y [E Hy]]. apply H. assert(x=y) by (apply Hf;[left;reflexivity|right;exact Hy|symmetry;exact E]). subst;auto.
 - apply IHNoDup. intros a b Ha Hb E. apply Hf;[right;exact Ha|right;exact Hb|exact E].
Qed.
Lemma nodup_flat__outer_commit : forall (xs:list Z) (f:Z->list Z),
 NoDup xs -> (forall x,In x xs -> NoDup(f x)) ->
 (forall x y k,In x xs -> In y xs -> In k(f x) -> In k(f y) -> x=y) -> NoDup(flat_map f xs).
Proof. intros xs f H;induction H;intros Hf Hd;simpl;[constructor|].
 apply NoDup_app.
 - apply Hf. left;reflexivity.
 - apply IHNoDup.
   + intros y Hy. apply Hf. right;exact Hy.
   + intros a b k Ha Hb Hka Hkb. apply Hd with k;[right;exact Ha|right;exact Hb|exact Hka|exact Hkb].
 - intros k Hk K. apply in_flat_map in K. destruct K as [y [Hy Hky]].
   assert(x=y) by (apply Hd with k;[left;reflexivity|right;exact Hy|exact Hk|exact Hky]). subst;contradiction.
Qed.
Lemma slots_nodup__outer_commit : forall m v,0<=m<=16 -> 0<=v<=24 -> NoDup(simplex_pivot_slots m v).
Proof. intros m v Hm Hv. unfold simplex_pivot_slots. apply NoDup_app.
 - apply NoDup_Zrange.
 - apply nodup_flat__outer_commit.
   + apply NoDup_Zrange.
   + intros i Hi. apply nodup_map_inj__outer_commit;[apply NoDup_Zrange|]. intros;lia.
   + intros i j k Hi Hj Hki Hkj. apply in_map_iff in Hki,Hkj.
     destruct Hki as [a [E Ha]],Hkj as [b [F Hb]]. apply In_Zrange in Ha,Hb. nia.
 - intros k Hk K. apply In_Zrange in Hk. apply in_flat_map in K. destruct K as [i [Hi Hki]].
   apply in_map_iff in Hki. destruct Hki as [j [E Hj]]. apply In_Zrange in Hi,Hj. nia.
Qed.
Lemma filter_absent__outer_commit : forall xs k, ~In k xs -> filter(fun x=>negb(Z.eqb x k)) xs=xs.
Proof. induction xs;intros;simpl;auto. assert(E:(a =? k)=false) by (apply Z.eqb_neq;intro;subst;apply H;left;reflexivity). rewrite E.
 simpl. f_equal. apply IHxs. intro K;apply H;right;exact K. Qed.
Lemma iter_focus__outer_commit : forall xs (F:Z->Assertion) k, NoDup xs -> In k xs ->
 iter_sepcon(map F xs) |-- F k ** iter_sepcon(map F(filter(fun x=>negb(Z.eqb x k))xs)).
Proof. intros xs F k H;induction H;intro Hin;[contradiction|]. simpl.
 destruct(Z.eq_dec x k) as [->|Hne].
 - rewrite Z.eqb_refl. simpl. rewrite filter_absent__outer_commit by exact H. rewrite !logic_equiv_iter_sepcon_cons. reflexivity.
 - rewrite (proj2(Z.eqb_neq x k) Hne). simpl. rewrite !logic_equiv_iter_sepcon_cons. sep_apply (IHNoDup ltac:(destruct Hin;[contradiction|assumption])).
   csimpl. sepcon_right_assoc. cancel(F k). cancel(F x). reflexivity.
Qed.
Lemma iter_merge__outer_commit : forall xs (F:Z->Assertion) k, NoDup xs -> In k xs ->
 F k ** iter_sepcon(map F(filter(fun x=>negb(Z.eqb x k))xs)) |-- iter_sepcon(map F xs).
Proof. intros xs F k H;induction H;intro Hin;[contradiction|]. simpl.
 destruct(Z.eq_dec x k) as [->|Hne].
 - rewrite Z.eqb_refl. simpl. rewrite filter_absent__outer_commit by exact H. rewrite !logic_equiv_iter_sepcon_cons. reflexivity.
 - rewrite (proj2(Z.eqb_neq x k) Hne). simpl. rewrite !logic_equiv_iter_sepcon_cons. sep_apply_r_atomic(IHNoDup ltac:(destruct Hin;[contradiction|assumption])).
   csimpl. sepcon_right_assoc. cancel(F k). cancel(F x). reflexivity.
Qed.
Lemma single_filter__outer_commit : forall xs k,
 filter(fun x=>negb(Z.eqb x k || Z.eqb x k))xs=filter(fun x=>negb(Z.eqb x k))xs.
Proof. intros. apply filter_ext. intro x. destruct(Z.eqb x k);reflexivity. Qed.
Lemma memory_focus__outer_commit : forall s m v n d k,0<=m<=16 -> 0<=v<=24 -> In k(simplex_pivot_slots m v) ->
 simplex_pivot_memory s m v n d |-- simplex_pivot_except s m v n d k k ** simplex_pivot_memory_cell s k (Znth k n 0)(Znth k d 1).
Proof. intros. unfold simplex_pivot_memory,simplex_pivot_except. rewrite single_filter__outer_commit.
 sep_apply(iter_focus__outer_commit (simplex_pivot_slots m v) (fun x=>simplex_pivot_memory_cell s x (Znth x n 0)(Znth x d 1)) k (slots_nodup__outer_commit _ _ H H0) H1).
 cancel(simplex_pivot_memory_cell s k (Znth k n 0)(Znth k d 1)). reflexivity. Qed.
Lemma matrix_cell__outer_commit : forall s i j n d,0<=i -> 0<=j<24 ->
 simplex_pivot_memory_cell s (16+i*24+j) n d =
 (&((((&((s) # "SxState" ->ₛ "a") + (i * (24 * sizeof("SxRat")))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> n **
 (&((((&((s) # "SxState" ->ₛ "a") + (i * (24 * sizeof("SxRat")))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> d.
Proof. intros. unfold simplex_pivot_memory_cell. rewrite (proj2(Z.ltb_ge (16+i*24+j) 16) ltac:(lia)).
 replace(16+i*24+j-16) with (j+i*24) by ring.
 rewrite Z.div_add,Z.mod_add by lia. rewrite Z.div_small,Z.mod_small by lia.
 replace(0+i) with i by lia. replace(sizeof("SxRat")*24) with (24*sizeof("SxRat")) by ring. reflexivity. Qed.
Lemma other_ready_nonzero__outer_commit : forall n d v r e b i fnum fden cn cd,
 fnum<>0 -> simplex_pivot_columns_progress n d v r e b i v fnum fden cn cd ->
 simplex_pivot_other_ready n d v r e b i fnum fden cn cd.
Proof. intros. unfold simplex_pivot_other_ready. rewrite (proj2(Z.eqb_neq fnum 0) H). exact H0. Qed.
Lemma skip_row__outer_commit : forall n d v r e b cn cd,0<=r ->
 simplex_pivot_rows_progress n d v r e b r cn cd -> simplex_pivot_rows_progress n d v r e b (r+1) cn cd.
Proof. intros. unfold simplex_pivot_rows_progress in *. rewrite simplex_pivot_rows_step by auto.
 rewrite H0. unfold simplex_pivot_other_row. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma filter_two__outer_commit : forall xs a b,
 filter(fun x=>negb(Z.eqb x a || Z.eqb x b))xs=
 filter(fun x=>negb(Z.eqb x b))(filter(fun x=>negb(Z.eqb x a))xs).
Proof. induction xs;intros;simpl;auto. destruct(a =? a0) eqn:E;destruct(a =? b) eqn:F;simpl;rewrite ?E,?F;simpl;rewrite IHxs;reflexivity. Qed.
Lemma iter_merge_two__outer_commit : forall xs (F:Z->Assertion) a b,NoDup xs -> In a xs -> In b xs -> a<>b ->
 F a ** F b ** iter_sepcon(map F(filter(fun x=>negb(Z.eqb x a || Z.eqb x b))xs)) |-- iter_sepcon(map F xs).
Proof. intros xs F a b H Ha Hb Hne. rewrite filter_two__outer_commit.
 assert(Hb':In b(filter(fun x=>negb(Z.eqb x a))xs)).
 { apply filter_In. split;[exact Hb|]. rewrite(proj2(Z.eqb_neq b a) ltac:(lia));reflexivity. }
 sep_apply_r_atomic(iter_merge__outer_commit xs F a H Ha).
 sep_apply_r_atomic(iter_merge__outer_commit _ F b (NoDup_filter _ H) Hb').
 csimpl. sepcon_right_assoc. cancel(F a). cancel(F b). reflexivity. Qed.
Lemma memory_merge_two__outer_commit : forall s m v n d a b,0<=m<=16 -> 0<=v<=24 ->
 In a(simplex_pivot_slots m v) -> In b(simplex_pivot_slots m v) -> a<>b ->
 simplex_pivot_memory_cell s a(Znth a n 0)(Znth a d 1) **
 simplex_pivot_memory_cell s b(Znth b n 0)(Znth b d 1) ** simplex_pivot_except s m v n d a b |-- simplex_pivot_memory s m v n d.
Proof. intros. unfold simplex_pivot_except,simplex_pivot_memory.
 apply(iter_merge_two__outer_commit (simplex_pivot_slots m v) (fun k=>simplex_pivot_memory_cell s k(Znth k n 0)(Znth k d 1)) a b);auto using slots_nodup__outer_commit. Qed.
Lemma rhs_cell__outer_commit : forall s i n d,0<=i<16 ->
 simplex_pivot_memory_cell s i n d=simplex_scan_rat_memory s "rhs" i true n d.
Proof. intros. unfold simplex_pivot_memory_cell. rewrite(proj2(Z.ltb_lt i 16) ltac:(lia)). reflexivity. Qed.
Lemma rhs_native__outer_commit : forall s i n d,0<=i<16 ->
 simplex_pivot_memory_cell s i n d =
 ((&(((&((s) # "SxState" ->ₛ "rhs") + (i * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> n) **
 ((&(((&((s) # "SxState" ->ₛ "rhs") + (i * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> d).
Proof. intros. rewrite rhs_cell__outer_commit by lia. unfold simplex_scan_rat_memory.
 assert(E1: &(s # "SxState" ->ₛ "rhs" [i] .ₛ "num") = &(((&((s) # "SxState" ->ₛ "rhs") + (i * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) by (csimpl;reflexivity).
 assert(E2: &(s # "SxState" ->ₛ "rhs" [i] .ₛ "den") = &(((&((s) # "SxState" ->ₛ "rhs") + (i * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) by (csimpl;reflexivity).
 rewrite E1,E2. reflexivity. Qed.
Lemma memory_update__outer_commit : forall s m v n d k a b,
 0<=m<=16 ->0<=v<=24 ->Zlength n=400 -> Zlength d=400 ->In k(simplex_pivot_slots m v) ->
 simplex_pivot_memory_cell s k a b ** simplex_pivot_except s m v n d k k |--
 simplex_pivot_memory s m v(replace_Znth k a n)(replace_Znth k b d).
Proof. intros s m v n d k a b Hm Hv Hn Hd Hk.
 pose proof(simplex_pivot_slots_bounds m v k Hm Hv Hk) as Hkb.
 unfold simplex_pivot_memory,simplex_pivot_except. rewrite single_filter__outer_commit.
 sep_apply_r_atomic(iter_merge__outer_commit (simplex_pivot_slots m v)
 (fun x=>simplex_pivot_memory_cell s x (Znth x(replace_Znth k a n)0)(Znth x(replace_Znth k b d)1)) k
 (slots_nodup__outer_commit m v Hm Hv) Hk).
 rewrite !Znth_replace_Znth_Same by lia.
 assert(E:map(fun x=>simplex_pivot_memory_cell s x(Znth x(replace_Znth k a n)0)(Znth x(replace_Znth k b d)1))
 (filter(fun x=>negb(Z.eqb x k))(simplex_pivot_slots m v))=
 map(fun x=>simplex_pivot_memory_cell s x(Znth x n 0)(Znth x d 1))
 (filter(fun x=>negb(Z.eqb x k))(simplex_pivot_slots m v))).
 { apply map_ext_in. intros x Hx. apply filter_In in Hx. destruct Hx as [Hx He].
   assert(Hne:x<>k) by(intro;subst;rewrite Z.eqb_refl in He;discriminate).
   pose proof(simplex_pivot_slots_bounds m v x Hm Hv Hx). rewrite !Znth_replace_Znth_Diff by lia. reflexivity. }
 rewrite E. reflexivity. Qed.
Lemma other_complete__outer_commit : forall n d v r e b i fnum fden cn cd,
 0<=i -> i<>r -> simplex_pivot_factor n d v r e b i fnum fden ->
 simplex_pivot_other_ready n d v r e b i fnum fden cn cd ->
 simplex_pivot_rows_progress n d v r e b(i+1)(replace_Znth(16+i*24+e)0 cn)(replace_Znth(16+i*24+e)1 cd).
Proof. intros n d v r e b i fnum fden cn cd Hi Hne [a [bb [Hp [Hfn Hfd]]]] Hr.
 unfold simplex_pivot_rows_progress in *. rewrite simplex_pivot_rows_step by auto.
 unfold simplex_pivot_other_row. rewrite(proj2(Z.eqb_neq i r) Hne),Hp. cbn zeta.
 unfold simplex_pivot_other_ready in Hr. rewrite Hp in Hr. cbn beta iota zeta in Hr.
 change(simplex_pivot_zero(16+i*24+e)(if Znth(16+i*24+e)a 0 =? 0 then (1,(a,bb)) else simplex_pivot_other_prefix (Znth(16+i*24+e)a 0)(Znth(16+i*24+e)bb 1) r i e v (simplex_pivot_addmul (Znth(16+i*24+e)a 0)(Znth(16+i*24+e)bb 1) r i (1,(a,bb)))) = (1,(replace_Znth(16+i*24+e)0 cn,replace_Znth(16+i*24+e)1 cd))).
 rewrite <-Hfn,<-Hfd. rewrite Hr. reflexivity. Qed.
Lemma update_good__outer_commit : forall m v n d k,
 Zlength n=400 ->Zlength d=400 -> 0<=m<=16 ->0<=v<=24 -> 0<=k<400 ->
 (forall x,In x(simplex_pivot_slots m v) -> -INT_MAX<=Znth x n 0<=INT_MAX /\ 1<=Znth x d 1<=INT_MAX /\ Z.gcd(Z.abs(Znth x n 0))(Znth x d 1)=1) ->
 forall x,In x(simplex_pivot_slots m v) -> -INT_MAX<=Znth x(replace_Znth k 0 n)0<=INT_MAX /\ 1<=Znth x(replace_Znth k 1 d)1<=INT_MAX /\ Z.gcd(Z.abs(Znth x(replace_Znth k 0 n)0))(Znth x(replace_Znth k 1 d)1)=1.
Proof. intros m v n d k Hn Hd Hm Hv Hk Hg x Hx. pose proof(simplex_pivot_slots_bounds m v x Hm Hv Hx).
 destruct(Z.eq_dec x k);subst.
 - rewrite !Znth_replace_Znth_Same by lia. cbn. repeat split;lia.
 - rewrite !Znth_replace_Znth_Diff by lia. apply Hg;exact Hx.
Qed.
Lemma range_cons__outer_commit : forall lo hi,lo<hi -> Zrange lo hi=lo::Zrange(lo+1)hi.
Proof. intros. unfold Zrange. replace(hi-lo) with (Z.succ(hi-(lo+1))) by lia.
 rewrite Z2Nat.inj_succ by lia. reflexivity. Qed.
Lemma array_rec_iter__outer_commit : forall l x lo hi,Zlength l=hi-lo ->
 store_array_rec StoreIntAsElement.storeA x lo hi l |--
 iter_sepcon(map(fun k=>StoreIntAsElement.storeA x k(Znth(k-lo)l 0))(Zrange lo hi)).
Proof. induction l as [|a l IH];intros x lo hi Hl.
 - rewrite Zlength_nil in Hl. assert(hi=lo) by lia. subst hi.
   unfold Zrange. rewrite Z.sub_diag. simpl. Intros_p H1. Intros_p H2. rewrite logic_equiv_iter_sepcon_nil. reflexivity.
 - rewrite Zlength_cons in Hl. simpl store_array_rec. rewrite range_cons__outer_commit by (pose proof(Zlength_nonneg l);lia).
   simpl map. rewrite logic_equiv_iter_sepcon_cons. replace(lo-lo) with 0 by lia. rewrite Znth0_cons.
   assert(E:map(fun k=>StoreIntAsElement.storeA x k(Znth(k-lo)(a::l)0))(Zrange(lo+1)hi)=
            map(fun k=>StoreIntAsElement.storeA x k(Znth(k-(lo+1))l 0))(Zrange(lo+1)hi)).
   { apply map_ext_in. intros k Hk. apply In_Zrange in Hk. rewrite Znth_cons by lia.
     replace(k-lo-1) with(k-(lo+1)) by lia. reflexivity. }
   rewrite E. sep_apply(IH x (lo+1)hi ltac:(lia)). cancel(StoreIntAsElement.storeA x lo a). reflexivity.
Qed.
Lemma full_iter__outer_commit : forall x v ib,
 IntArray.full x v ib |--iter_sepcon(map(fun k=>(x+k*sizeof(INT)) # Int |-> Znth k ib 0)(Zrange 0 v)).
Proof. intros. prop_apply_p(IntArray.full_Zlength x v ib). Intros_p Hl.
 unfold IntArray.full,store_array. sep_apply(array_rec_iter__outer_commit ib x 0 v ltac:(lia)).
 assert(E:map(fun k=>StoreIntAsElement.storeA x k(Znth(k-0)ib 0))(Zrange 0 v)=map(fun k=>(x+k*sizeof(INT)) # Int |-> Znth k ib 0)(Zrange 0 v)).
 { apply map_ext. intro k. replace(k-0)with k by lia. reflexivity. } rewrite E. reflexivity. Qed.
Lemma iter_focus_two__outer_commit : forall xs (F:Z->Assertion) a b,NoDup xs -> In a xs ->In b xs ->a<>b ->
 iter_sepcon(map F xs) |-- F a ** F b ** iter_sepcon(map F(filter(fun x=>negb(Z.eqb x a || Z.eqb x b))xs)).
Proof. intros xs F a b H Ha Hb Hne. rewrite filter_two__outer_commit.
 sep_apply(iter_focus__outer_commit xs F a H Ha).
 assert(Hb':In b(filter(fun x=>negb(Z.eqb x a))xs)).
 { apply filter_In. split;[exact Hb|]. rewrite(proj2(Z.eqb_neq b a)ltac:(lia));reflexivity. }
 sep_apply(iter_focus__outer_commit _ F b (NoDup_filter _ H) Hb'). sepcon_right_assoc. cancel(F a). cancel(F b). reflexivity. Qed.
Lemma flags_focus__outer_commit : forall s v ib b e,0<=b<v ->0<=e<v ->b<>e ->
 IntArray.full (&((s) # "SxState" ->ₛ "is_basic")) v ib |--
 (((&((s) # "SxState" ->ₛ "is_basic"))+b*sizeof(INT)) # Int |-> Znth b ib 0) **
 (((&((s) # "SxState" ->ₛ "is_basic"))+e*sizeof(INT)) # Int |-> Znth e ib 0) **simplex_pivot_flags_except s v ib b e.
Proof. intros. sep_apply(full_iter__outer_commit (&((s) # "SxState" ->ₛ "is_basic")) v ib).
 unfold simplex_pivot_flags_except. sep_apply(iter_focus_two__outer_commit (Zrange 0 v)
 (fun k=>((&((s) # "SxState" ->ₛ "is_basic"))+k*sizeof(INT)) # Int |-> Znth k ib 0) b e (NoDup_Zrange 0 v) ltac:(apply In_Zrange;lia) ltac:(apply In_Zrange;lia) H1).
 sepcon_right_assoc. reflexivity. Qed.
Lemma nd_app__entry_focus : forall (a b:list Z), NoDup a -> NoDup b -> (forall x, In x a -> ~In x b) -> NoDup (a++b).
Proof. intros a b H; induction H; intros Hb Hd; simpl; auto. constructor.
 - rewrite in_app_iff. intro E. destruct E; [contradiction|eapply Hd; eauto; left;auto].
 - apply IHNoDup; auto. intros; apply Hd;right;auto.
Qed.
Lemma nd_map__entry_focus : forall (l:list Z) (f:Z->Z), NoDup l -> (forall x y, In x l -> In y l -> f x=f y -> x=y) -> NoDup(map f l).
Proof. intros l f H; induction H; intros Hi; simpl; constructor.
 - intro E. apply in_map_iff in E. destruct E as [y [E Hy]]. apply H. assert(x=y) by (apply Hi;auto;[left;auto|right;auto]). congruence.
 - apply IHNoDup. intros;apply Hi;auto;right;auto.
Qed.
Lemma nd_flat__entry_focus : forall (l:list Z) (f:Z->list Z), NoDup l ->
 (forall x,In x l -> NoDup(f x)) ->
 (forall x y z,In x l -> In y l -> x<>y -> In z(f x) -> ~In z(f y)) -> NoDup(flat_map f l).
Proof. intros l f H; induction H; intros Hn Hd; simpl; [constructor|]. apply nd_app__entry_focus.
 - apply Hn;left;auto.
 - apply IHNoDup; intros; eauto; try (apply Hn;right;auto). eapply Hd;eauto;right;auto.
 - intros z Hz E. apply in_flat_map in E. destruct E as [y [Hy He]]. eapply (Hd x y z);eauto;[left;auto|right;auto|intro;subst;contradiction].
Qed.
Lemma slots_nd__entry_focus : forall m v, 0<=m<=16 -> 0<=v<=24 -> NoDup(simplex_pivot_slots m v).
Proof.
 intros m v Hm Hv. unfold simplex_pivot_slots. apply nd_app__entry_focus.
 - apply NoDup_Zrange.
 - apply nd_flat__entry_focus; [apply NoDup_Zrange| |].
   + intros i Hi. apply nd_map__entry_focus;[apply NoDup_Zrange|]. intros;lia.
   + intros i k z Hi Hk Hik Hz He. apply in_map_iff in Hz. apply in_map_iff in He.
     destruct Hz as [j [<- Hj]], He as [t [Et Ht]].
     apply In_Zrange in Hi. apply In_Zrange in Hk. apply In_Zrange in Hj. apply In_Zrange in Ht. lia.
 - intros z Hz He. apply In_Zrange in Hz. apply in_flat_map in He. destruct He as [i [Hi He]]. apply in_map_iff in He. destruct He as [j [<- Hj]]. apply In_Zrange in Hi. apply In_Zrange in Hj. lia.
Qed.
Lemma filter_all__entry_focus : forall (l:list Z) f, (forall x,In x l -> f x=true) -> filter f l=l.
Proof. induction l;intros f H; simpl;auto. rewrite H by (left;auto). rewrite IHl;auto. intros;apply H;right;auto. Qed.
Lemma filter_focus__entry_focus : forall (l:list Z) (f:Z->Assertion) k,
 NoDup l -> In k l ->
 iter_sepcon(map f l) |-- iter_sepcon(map f (filter(fun x=>negb(Z.eqb x k || Z.eqb x k))l)) ** f k.
Proof.
 intros l f k Hn; induction Hn; intros Hin; [contradiction|]. simpl in Hin. destruct Hin as [Ee|Hin].
 - subst x. simpl. rewrite Z.eqb_refl. simpl.
   assert(E:filter(fun x=>negb(Z.eqb x k || Z.eqb x k))l=l).
   { apply filter_all__entry_focus. intros x Hx. assert(x<>k) by (intro;subst;contradiction). apply Bool.negb_true_iff. apply Bool.orb_false_iff. split;apply Z.eqb_neq;auto. }
   rewrite E. rewrite !logic_equiv_iter_sepcon_cons. cancel (f k). reflexivity.
 - assert(E:Z.eqb x k=false) by (apply Z.eqb_neq;intro;subst;contradiction).
   simpl. rewrite E. simpl. rewrite !logic_equiv_iter_sepcon_cons.
   sep_apply_l_atomic (IHHn Hin). cancel (f x). reflexivity.
Qed.
Lemma memory_focus__entry_focus : forall s m v n d k,
 0<=m<=16 -> 0<=v<=24 -> In k(simplex_pivot_slots m v) ->
 simplex_pivot_memory s m v n d |-- simplex_pivot_except s m v n d k k ** simplex_pivot_memory_cell s k (Znth k n 0)(Znth k d 1).
Proof. intros. unfold simplex_pivot_memory,simplex_pivot_except. apply (filter_focus__entry_focus (simplex_pivot_slots m v) (fun t=>simplex_pivot_memory_cell s t (Znth t n 0)(Znth t d 1)) k);auto. apply slots_nd__entry_focus;auto. Qed.
Lemma filter_merge__entry_focus : forall (l:list Z) (f:Z->Assertion) k,
 NoDup l -> In k l ->
 iter_sepcon(map f (filter(fun x=>negb(Z.eqb x k || Z.eqb x k))l)) ** f k |-- iter_sepcon(map f l).
Proof.
 intros l f k Hn; induction Hn; intros Hin; [contradiction|]. simpl in Hin. destruct Hin as [Ee|Hin].
 - subst x. simpl. rewrite Z.eqb_refl. simpl.
   assert(E:filter(fun x=>negb(Z.eqb x k || Z.eqb x k))l=l).
   { apply filter_all__entry_focus. intros x Hx. assert(x<>k) by (intro;subst;contradiction). apply Bool.negb_true_iff. apply Bool.orb_false_iff. split;apply Z.eqb_neq;auto. }
   rewrite E. rewrite !logic_equiv_iter_sepcon_cons. cancel (f k). reflexivity.
 - assert(E:Z.eqb x k=false) by (apply Z.eqb_neq;intro;subst;contradiction).
   simpl. rewrite E. simpl. rewrite !logic_equiv_iter_sepcon_cons.
   sep_apply_r_atomic (IHHn Hin). cancel (f x). reflexivity.
Qed.
Lemma memory_merge__entry_focus : forall s m v n d k,
 0<=m<=16 -> 0<=v<=24 -> In k(simplex_pivot_slots m v) ->
 simplex_pivot_except s m v n d k k ** simplex_pivot_memory_cell s k (Znth k n 0)(Znth k d 1) |-- simplex_pivot_memory s m v n d.
Proof. intros. unfold simplex_pivot_memory,simplex_pivot_except. apply (filter_merge__entry_focus (simplex_pivot_slots m v) (fun t=>simplex_pivot_memory_cell s t (Znth t n 0)(Znth t d 1)) k);auto. apply slots_nd__entry_focus;auto. Qed.
Lemma cell_rhs__entry_focus : forall s i n d, 0<=i<16 ->
 simplex_pivot_memory_cell s i n d = simplex_scan_rat_memory s "rhs" i true n d.
Proof. intros. unfold simplex_pivot_memory_cell. assert(E:Z.ltb i 16=true) by (apply Z.ltb_lt;lia). rewrite E. reflexivity. Qed.
Lemma cell_a__entry_focus : forall s i j n d, 0<=i -> 0<=j<24 ->
 simplex_pivot_memory_cell s (16+i*24+j) n d =
 (&((((&((s) # "SxState" ->ₛ "a") + (i * (sizeof("SxRat") * 24))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> n **
 (&((((&((s) # "SxState" ->ₛ "a") + (i * (sizeof("SxRat") * 24))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> d.
Proof. intros. unfold simplex_pivot_memory_cell. assert(E:Z.ltb (16+i*24+j) 16=false) by (apply Z.ltb_ge;lia). rewrite E.
 replace (16+i*24+j-16) with (j+i*24) by ring. rewrite Z.div_add,Z.mod_add by lia.
 rewrite Z.div_small,Z.mod_small by lia. replace (0+i) with i by lia. reflexivity. Qed.
Lemma native_focus_a__entry_focus : forall s m v n d r e,
 0<=m<=16 -> 0<=v<=24 -> 0<=r<m -> 0<=e<v ->
 simplex_pivot_memory s m v n d |-- simplex_pivot_except s m v n d (16+r*24+e)(16+r*24+e) **
 (&((((&((s) # "SxState" ->ₛ "a") + (r * (sizeof("SxRat") * 24))) + (e * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> (Znth (16+r*24+e) n 0) **
 (&((((&((s) # "SxState" ->ₛ "a") + (r * (sizeof("SxRat") * 24))) + (e * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> (Znth (16+r*24+e) d 1).
Proof. intros. sep_apply_l_atomic(memory_focus__entry_focus s m v n d (16+r*24+e) H H0 (simplex_pivot_a_active m v r e H1 H2)). rewrite cell_a__entry_focus by lia. reflexivity. Qed.
Lemma native_focus_rhs__entry_focus : forall s m v n d r,
 0<=m<=16 -> 0<=v<=24 -> 0<=r<m ->
 simplex_pivot_memory s m v n d |-- simplex_pivot_except s m v n d r r **
 (&(((&((s) # "SxState" ->ₛ "rhs") + (r * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> Znth r n 0 **
 (&(((&((s) # "SxState" ->ₛ "rhs") + (r * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> Znth r d 1.
Proof. intros. sep_apply_l_atomic(memory_focus__entry_focus s m v n d r H H0 (simplex_pivot_rhs_active m v r H1)). rewrite cell_rhs__entry_focus by lia. unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc. reflexivity. Qed.
Lemma native_merge_a__entry_focus : forall s m v n d r e,
 0<=m<=16 -> 0<=v<=24 -> 0<=r<m -> 0<=e<v ->
 (&((((&((s) # "SxState" ->ₛ "a") + (r * (sizeof("SxRat") * 24))) + (e * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> (Znth (16+r*24+e) n 0) ** (&((((&((s) # "SxState" ->ₛ "a") + (r * (sizeof("SxRat") * 24))) + (e * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> (Znth (16+r*24+e) d 1) ** simplex_pivot_except s m v n d (16+r*24+e)(16+r*24+e) |-- simplex_pivot_memory s m v n d.
Proof. intros. sep_apply_r_atomic(memory_merge__entry_focus s m v n d (16+r*24+e) H H0 (simplex_pivot_a_active m v r e H1 H2)).
 rewrite cell_a__entry_focus by lia. sepcon_right_assoc.
 repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity. Qed.
Lemma filter_abs__row_division : forall (l:list Z) k, ~In k l -> filter (fun x=>negb(Z.eqb x k)) l=l.
Proof. induction l; intros; simpl; auto. assert(a<>k) by (intro;subst;apply H;left;reflexivity).
 assert (Heq : Z.eqb a k = false) by (apply Z.eqb_neq; auto). rewrite Heq. simpl. f_equal. apply IHl. intro;apply H;right;auto. Qed.
Lemma nd_app__row_division : forall (a b:list Z), NoDup a -> NoDup b ->
 (forall x,In x a -> ~In x b) -> NoDup(a++b).
Proof. induction a;intros b Ha Hb H; simpl;auto. inversion Ha;subst. constructor.
 intro K;apply in_app_or in K;destruct K;[contradiction|eapply H;eauto;left;reflexivity].
 apply IHa;auto. intros x Hx. apply H. right;auto. Qed.
Lemma nd_map__row_division : forall (l:list Z) (f:Z->Z), NoDup l ->
 (forall x y,In x l -> In y l -> f x=f y -> x=y) -> NoDup(map f l).
Proof. induction l as [|a l IH]; intros f Hnd H; simpl.
 - constructor.
 - inversion Hnd as [|a0 l0 Hnot Htail]; subst. constructor.
   + intro K. apply in_map_iff in K. destruct K as [y [Hy Hin]]. apply Hnot.
     assert (a=y) by (apply H; [left;reflexivity|right;exact Hin|symmetry;exact Hy]). subst;exact Hin.
   + apply IH; auto. intros x y Hx Hy He. apply H; auto;right;auto.
Qed.
Lemma nd_flat__row_division : forall (l:list Z) (f:Z->list Z), NoDup l ->
 (forall x,In x l -> NoDup(f x)) ->
 (forall x y k,In x l -> In y l -> x<>y -> In k(f x) -> ~In k(f y)) ->
 NoDup(flat_map f l).
Proof. induction l as [|a l IH]; intros f Hnd Hf Hd; simpl; [constructor|].
 inversion Hnd as [|a0 l0 Hnot Htail]; subst. apply nd_app__row_division.
 - apply Hf. left; reflexivity.
 - apply IH; auto.
   + intros x Hx; apply Hf; right; auto.
   + intros x y k Hx Hy; apply Hd; auto;right;auto.
 - intros k Hk HK. apply in_flat_map in HK. destruct HK as [y [Hy Hky]].
   eapply (Hd a y k);eauto;[left;auto|right;auto|intro;subst;contradiction].
Qed.
Lemma slots_nd__row_division : forall m v, 0<=m<=16 -> 0<=v<=24 -> NoDup(simplex_pivot_slots m v).
Proof. intros m v Hm Hv. unfold simplex_pivot_slots. apply nd_app__row_division.
 - apply NoDup_Zrange.
 - apply nd_flat__row_division. apply NoDup_Zrange.
   + intros i Hi. apply nd_map__row_division. apply NoDup_Zrange. intros;lia.
   + intros i j k Hi Hj Hne Hki Hkj.
     apply in_map_iff in Hki. destruct Hki as [x [<- Hx]].
     apply in_map_iff in Hkj. destruct Hkj as [y [He Hy]].
     apply In_Zrange in Hx. apply In_Zrange in Hy. nia.
 - intros k Hk Hflat. apply In_Zrange in Hk. apply in_flat_map in Hflat.
   destruct Hflat as [i [Hi Hj]]. apply in_map_iff in Hj. destruct Hj as [j [<- Hj]].
   apply In_Zrange in Hi. apply In_Zrange in Hj. nia.
Qed.
Lemma filter_focus__row_division : forall (l:list Z) (F:Z->Assertion) k,
 NoDup l -> In k l -> (iter_sepcon(map F l) |-- F k ** iter_sepcon(map F(filter(fun x=>negb(Z.eqb x k))l)))%sac.
Proof. induction l;intros F k Hnd Hin;[contradiction|]. inversion Hnd as [|a0 l0 Hnot Htail];subst.
 simpl map. rewrite logic_equiv_iter_sepcon_cons. destruct(Z.eq_dec a k) as [->|Hne].
 - simpl filter. rewrite Z.eqb_refl. simpl. rewrite filter_abs__row_division by auto. reflexivity.
 - simpl filter. assert (Heq : Z.eqb a k = false) by (apply Z.eqb_neq; auto). rewrite Heq. simpl map. rewrite logic_equiv_iter_sepcon_cons.
   assert(Hk:In k l) by (destruct Hin;[contradiction|auto]).
   sep_apply_l_atomic(IHl F k Htail Hk). cancel. Qed.
Lemma filter_merge__row_division : forall (l:list Z) (F:Z->Assertion) k,
 NoDup l -> In k l -> (F k ** iter_sepcon(map F(filter(fun x=>negb(Z.eqb x k))l)) |-- iter_sepcon(map F l))%sac.
Proof. induction l;intros F k Hnd Hin;[contradiction|]. inversion Hnd as [|a0 l0 Hnot Htail];subst.
 simpl map. rewrite logic_equiv_iter_sepcon_cons. destruct(Z.eq_dec a k) as [->|Hne].
 - simpl filter. rewrite Z.eqb_refl. simpl. rewrite filter_abs__row_division by auto. reflexivity.
 - simpl filter. assert (Heq : Z.eqb a k = false) by (apply Z.eqb_neq; auto). rewrite Heq. simpl map. rewrite logic_equiv_iter_sepcon_cons.
   assert(Hk:In k l) by (destruct Hin;[contradiction|auto]).
   sepcon_right_assoc. sep_apply_l_atomic(IHl F k Htail Hk). cancel. Qed.
Lemma div_update__row_division : forall pn pd k n d u v,
 simplex_rat_div_flag (Znth k n 0)(Znth k d 1) pn pd=1 ->
 simplex_rat_div_result (Znth k n 0)(Znth k d 1) pn pd u v ->
 simplex_pivot_div pn pd k true (1,(n,d))=(1,(replace_Znth k (-u) n,replace_Znth k v d)).
Proof. intros pn pd k n d u v HF HR. unfold simplex_pivot_div.
 rewrite HF. cbn [Z.eqb]. unfold simplex_rat_div_result,simplex_rat_reduce_result in HR.
 destruct HR as [-> ->]. reflexivity. Qed.
Lemma put_good__row_division : forall m c n d k u v,
 0<=m<=16 -> 0<=c<=24 ->
 Zlength n=400 -> Zlength d=400 -> 0<=k<400 ->
 (-INT_MAX<=u<=INT_MAX) -> 1<=v<=INT_MAX -> Z.gcd(Z.abs u)v=1 ->
 (forall j,In j(simplex_pivot_slots m c) ->
 -INT_MAX<=Znth j n 0<=INT_MAX /\ 1<=Znth j d 1<=INT_MAX /\ Z.gcd(Z.abs(Znth j n 0))(Znth j d 1)=1) ->
 forall j, In j(simplex_pivot_slots m c) ->
 -INT_MAX<=Znth j(replace_Znth k u n)0<=INT_MAX /\
 1<=Znth j(replace_Znth k v d)1<=INT_MAX /\
 Z.gcd(Z.abs(Znth j(replace_Znth k u n)0))(Znth j(replace_Znth k v d)1)=1.
Proof. intros m c n d k u v Hm Hc Hn Hd Hk Hu Hv Hg Hgood j Hj.
 assert(Hjbound:0<=j<400) by (eapply simplex_pivot_slots_bounds;eauto).
 destruct(Z.eq_dec j k) as [->|Hne]. rewrite !Znth_replace_Znth_Same by lia. auto.
 rewrite !Znth_replace_Znth_Diff by lia. apply Hgood;auto. Qed.
Lemma except_diag__row_division : forall s m c n d k,
 simplex_pivot_except s m c n d k k =
 iter_sepcon(map(fun j=>simplex_pivot_memory_cell s j (Znth j n 0)(Znth j d 1))
 (filter(fun j=>negb(Z.eqb j k))(simplex_pivot_slots m c))).
Proof. intros. unfold simplex_pivot_except. f_equal. f_equal.
 apply filter_ext. intros x. rewrite Bool.orb_diag. reflexivity. Qed.
Lemma memory_focus__row_division : forall s m c n d k,
 0<=m<=16 -> 0<=c<=24 -> In k(simplex_pivot_slots m c) ->
 (simplex_pivot_memory s m c n d |--
 simplex_pivot_memory_cell s k (Znth k n 0)(Znth k d 1) ** simplex_pivot_except s m c n d k k)%sac.
Proof. intros. unfold simplex_pivot_memory. rewrite except_diag__row_division.
 apply (filter_focus__row_division (simplex_pivot_slots m c) (fun j=>simplex_pivot_memory_cell s j (Znth j n 0)(Znth j d 1)) k); auto. apply slots_nd__row_division;auto. Qed.
Lemma memory_update__row_division : forall s m c n d k u v,
 0<=m<=16 -> 0<=c<=24 -> Zlength n=400 -> Zlength d=400 -> In k(simplex_pivot_slots m c) ->
 (simplex_pivot_memory_cell s k u v ** simplex_pivot_except s m c n d k k |--
 simplex_pivot_memory s m c (replace_Znth k u n)(replace_Znth k v d))%sac.
Proof. intros s m c n d k u v Hm Hc Hn Hd Hk.
 assert(Hkb:0<=k<400) by(eapply simplex_pivot_slots_bounds;eauto).
 rewrite except_diag__row_division. unfold simplex_pivot_memory.
 assert (E:map(fun j=>simplex_pivot_memory_cell s j (Znth j n 0)(Znth j d 1))
 (filter(fun j=>negb(Z.eqb j k))(simplex_pivot_slots m c)) =
 map(fun j=>simplex_pivot_memory_cell s j (Znth j(replace_Znth k u n)0)(Znth j(replace_Znth k v d)1))
 (filter(fun j=>negb(Z.eqb j k))(simplex_pivot_slots m c))).
 { apply map_ext_in. intros j Hj. apply filter_In in Hj. destruct Hj as [Hj Hne].
   apply Bool.negb_true_iff in Hne. apply Z.eqb_neq in Hne.
   assert(Hjb:0<=j<400) by(eapply simplex_pivot_slots_bounds;eauto).
   rewrite !Znth_replace_Znth_Diff by lia. reflexivity. }
 rewrite E.
 pose proof (filter_merge__row_division (simplex_pivot_slots m c)
 (fun j=>simplex_pivot_memory_cell s j (Znth j(replace_Znth k u n)0)(Znth j(replace_Znth k v d)1)) k
 (slots_nd__row_division m c Hm Hc) Hk) as HH.
 cbn beta in HH. rewrite !Znth_replace_Znth_Same in HH by lia. exact HH.
Qed.
Lemma native_a__row_division : forall s r j u v,
 0<=r -> 0<=j<24 ->
 simplex_pivot_memory_cell s (16+r*24+j) u v =
 ((&((((&((s) # "SxState" ->ₛ "a") + (r * (24 * sizeof("SxRat")))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> u **
 (&((((&((s) # "SxState" ->ₛ "a") + (r * (24 * sizeof("SxRat")))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> v)%sac.
Proof. intros. unfold simplex_pivot_memory_cell.
 assert(E:Z.ltb(16+r*24+j)16=false) by(apply Z.ltb_ge;lia). rewrite E.
 assert(D:(16+r*24+j-16)/24=r) by(symmetry;apply Z.div_unique with j;lia).
 assert(M:(16+r*24+j-16) mod 24=j) by(symmetry;apply Z.mod_unique with r;lia).
 rewrite D,M. replace (sizeof("SxRat")*24) with (24*sizeof("SxRat")) by ring. reflexivity.
Qed.
Lemma native_rhs__row_division : forall s r u v,
 0<=r<16 -> simplex_pivot_memory_cell s r u v =
 ((&(((&((s) # "SxState" ->ₛ "rhs") + (r * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> u **
 (&(((&((s) # "SxState" ->ₛ "rhs") + (r * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> v)%sac.
Proof. intros. unfold simplex_pivot_memory_cell. assert(E:Z.ltb r 16=true) by(apply Z.ltb_lt;lia).
 rewrite E. unfold simplex_scan_rat_memory. csimpl. reflexivity. Qed.
Lemma memory_merge__row_division : forall s m c n d k,
 0<=m<=16 -> 0<=c<=24 -> In k(simplex_pivot_slots m c) ->
 (simplex_pivot_memory_cell s k (Znth k n 0)(Znth k d 1) ** simplex_pivot_except s m c n d k k |-- simplex_pivot_memory s m c n d)%sac.
Proof. intros. unfold simplex_pivot_memory. rewrite except_diag__row_division.
 apply(filter_merge__row_division (simplex_pivot_slots m c)(fun j=>simplex_pivot_memory_cell s j (Znth j n 0)(Znth j d 1)) k);auto.
 apply slots_nd__row_division;auto. Qed.
Lemma nodup_flat__row_finalize : forall (xs:list Z) (f:Z->list Z),
 NoDup xs -> (forall x, In x xs -> NoDup(f x)) ->
 (forall x y k, In x xs -> In y xs -> In k(f x) -> In k(f y) -> x=y) ->
 NoDup(flat_map f xs).
Proof.
 intros xs; induction xs as [|x xs IH]; intros f HN HF HD; simpl; [constructor|].
 inversion HN; subst. apply NoDup_app. repeat split.
 - apply HF; left; reflexivity.
 - apply IH; [assumption|intros; apply HF; right; assumption|].
   intros; eapply HD; eauto; right; assumption.
 - intros k HK HL. apply in_flat_map in HL as [y [HY HKY]].
   assert (x=y) by (eapply HD; eauto; [left;reflexivity|right;assumption]). subst; contradiction.
Qed.
Lemma nodup_map__row_finalize : forall (f:Z->Z) xs,
 NoDup xs -> (forall x y,f x=f y->x=y) -> NoDup(map f xs).
Proof.
 intros f xs H; induction H; intros HF; simpl; constructor; auto.
 intro HI; apply in_map_iff in HI as [y [E HY]]. apply H. assert(y=x) by (apply HF;exact E). subst;assumption.
Qed.
Lemma slots_nodup__row_finalize : forall m v, 0<=m<=16 -> 0<=v<=24 ->
 NoDup(simplex_pivot_slots m v).
Proof.
 intros m v HM HV. unfold simplex_pivot_slots. apply NoDup_app. repeat split.
 - apply NoDup_Zrange.
 - apply nodup_flat__row_finalize.
   + apply NoDup_Zrange.
   + intros i HI. apply nodup_map__row_finalize; [apply NoDup_Zrange|intros;lia].
   + intros i j k HI HJ HK HL.
     apply In_Zrange in HI; apply In_Zrange in HJ.
     apply in_map_iff in HK as [a [EA HA]]; apply In_Zrange in HA.
     apply in_map_iff in HL as [b [EB HB]]; apply In_Zrange in HB. nia.
 - intros k HK HL. apply In_Zrange in HK.
   apply in_flat_map in HL as [i [HI HL]]. apply In_Zrange in HI.
   apply in_map_iff in HL as [j [E HJ]]. apply In_Zrange in HJ. nia.
Qed.
Lemma filter_absent__row_finalize : forall xs k, ~In k xs ->
 filter (fun x=>negb(Z.eqb x k || Z.eqb x k)) xs=xs.
Proof.
 induction xs as [|x xs IH]; intros k H; simpl; auto.
 assert (x<>k) by (intro;subst;apply H;left;reflexivity).
 assert (EB : Z.eqb x k = false) by (apply Z.eqb_neq; assumption). rewrite EB. simpl. f_equal. apply IH. intro; apply H;right;assumption.
Qed.
Lemma cell_focus__row_finalize : forall xs (f:Z->Assertion) k,
 NoDup xs -> In k xs -> iter_sepcon(map f xs) |--
 f k ** iter_sepcon(map f (filter(fun x=>negb(Z.eqb x k || Z.eqb x k)) xs)).
Proof.
 induction xs as [|x xs IH]; intros f k HN HI; simpl in HI; [contradiction|].
 inversion HN as [|? ? HNot HT]; subst. simpl. destruct HI as [E|HI].
 - subst x. rewrite Z.eqb_refl. simpl. rewrite filter_absent__row_finalize by assumption.
   rewrite logic_equiv_iter_sepcon_cons. reflexivity.
 - destruct (Z.eq_dec x k) as [E|E]; [subst;contradiction|].
   assert (EB : Z.eqb x k = false) by (apply Z.eqb_neq; assumption). rewrite EB. simpl. rewrite !logic_equiv_iter_sepcon_cons.
   sepcon_right_assoc. sep_apply_l_atomic (IH f k HT HI).
   sepcon_right_assoc. cancel (f x). cancel (f k). reflexivity.
Qed.
Lemma cell_merge__row_finalize : forall xs (f:Z->Assertion) k,
 NoDup xs -> In k xs ->
 f k ** iter_sepcon(map f (filter(fun x=>negb(Z.eqb x k || Z.eqb x k)) xs)) |-- iter_sepcon(map f xs).
Proof.
 induction xs as [|x xs IH]; intros f k HN HI; simpl in HI; [contradiction|].
 inversion HN as [|? ? HNot HT]; subst. simpl. destruct HI as [E|HI].
 - subst x. rewrite Z.eqb_refl. simpl. rewrite filter_absent__row_finalize by assumption.
   rewrite logic_equiv_iter_sepcon_cons. reflexivity.
 - destruct (Z.eq_dec x k) as [E|E]; [subst;contradiction|].
   assert (EB : Z.eqb x k = false) by (apply Z.eqb_neq; assumption). rewrite EB. simpl. rewrite !logic_equiv_iter_sepcon_cons.
   sepcon_right_assoc. cancel (f x). apply IH; assumption.
Qed.
Lemma matrix_cell__row_finalize : forall s i j n d, 0<=i -> 0<=j<24 ->
 simplex_pivot_memory_cell s (16+i*24+j) n d =
 (&((((&((s) # "SxState" ->ₛ "a") + (i * (24 * sizeof("SxRat")))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> n **
 (&((((&((s) # "SxState" ->ₛ "a") + (i * (24 * sizeof("SxRat")))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> d.
Proof.
 intros. unfold simplex_pivot_memory_cell.
 assert ((16+i*24+j <? 16)=false) by (apply Z.ltb_ge;lia). rewrite H1.
 replace (16+i*24+j-16) with (i*24+j) by ring.
 rewrite Z.div_add_l by lia. rewrite Z.div_small by lia.
 replace ((i*24+j) mod 24) with j by (rewrite Z.add_comm, Z.mod_add by lia; rewrite Z.mod_small by lia; reflexivity).
 replace (i+0) with i by lia. replace (sizeof("SxRat")*24) with (24*sizeof("SxRat")) by ring. reflexivity.
Qed.
Lemma except_put__row_finalize : forall s m v n d k a b,
 0<=m<=16 -> 0<=v<=24 -> Zlength n=400 -> Zlength d=400 -> 0<=k<400 ->
 simplex_pivot_except s m v (replace_Znth k a n) (replace_Znth k b d) k k =
 simplex_pivot_except s m v n d k k.
Proof.
 intros s m v n d k a b HM HV HN HD HK. unfold simplex_pivot_except. f_equal. apply map_ext_in. intros j HJ.
 apply filter_In in HJ as [HA HJ].
 pose proof (simplex_pivot_slots_bounds m v j HM HV HA) as HB.
 assert (j<>k) by (intro E;subst j;rewrite Z.eqb_refl in HJ;discriminate).
 rewrite !Znth_replace_Znth_Diff by lia. reflexivity.
Qed.
Lemma memory_put__row_finalize : forall s m v n d k a b,
 0<=m<=16 -> 0<=v<=24 -> Zlength n=400 -> Zlength d=400 ->
 In k (simplex_pivot_slots m v) ->
 simplex_pivot_memory_cell s k a b ** simplex_pivot_except s m v n d k k |--
 simplex_pivot_memory s m v (replace_Znth k a n) (replace_Znth k b d).
Proof.
 intros s m v n d k a b HM HV HN HD HK.
 pose proof (simplex_pivot_slots_bounds m v k HM HV HK) as HB.
 rewrite <- (except_put__row_finalize s m v n d k a b HM HV HN HD HB).
 unfold simplex_pivot_memory, simplex_pivot_except.
 pose proof (cell_merge__row_finalize (simplex_pivot_slots m v)
  (fun j=>simplex_pivot_memory_cell s j (Znth j (replace_Znth k a n) 0) (Znth j (replace_Znth k b d) 1)) k
  (slots_nodup__row_finalize m v HM HV) HK) as HH.
 cbn beta in HH. rewrite !Znth_replace_Znth_Same in HH by lia. exact HH.
Qed.
Lemma memory_focus__row_finalize : forall s m v n d k,
 0<=m<=16 -> 0<=v<=24 -> In k(simplex_pivot_slots m v) ->
 simplex_pivot_memory s m v n d |--
 simplex_pivot_memory_cell s k (Znth k n 0) (Znth k d 1) ** simplex_pivot_except s m v n d k k.
Proof.
 intros. unfold simplex_pivot_memory, simplex_pivot_except.
 exact (cell_focus__row_finalize (simplex_pivot_slots m v) (fun j=>simplex_pivot_memory_cell s j (Znth j n 0) (Znth j d 1)) k (slots_nodup__row_finalize m v H H0) H1).
Qed.
Lemma good_put__row_finalize : forall m v n d k a b,
 0<=m<=16 -> 0<=v<=24 -> Zlength n=400 -> Zlength d=400 -> 0<=k<400 ->
 -INT_MAX<=a<=INT_MAX -> 1<=b<=INT_MAX -> Z.gcd (Z.abs a) b=1 ->
 (forall j,In j(simplex_pivot_slots m v)->
 (((-INT_MAX<=Znth j n 0 /\ Znth j n 0<=INT_MAX) /\ 1<=Znth j d 1) /\ Znth j d 1<=INT_MAX) /\ Z.gcd(Z.abs(Znth j n 0))(Znth j d 1)=1) ->
 forall j,In j(simplex_pivot_slots m v)->
 (((-INT_MAX<=Znth j (replace_Znth k a n) 0 /\ Znth j (replace_Znth k a n) 0<=INT_MAX) /\ 1<=Znth j (replace_Znth k b d) 1) /\ Znth j (replace_Znth k b d) 1<=INT_MAX) /\ Z.gcd(Z.abs(Znth j (replace_Znth k a n) 0))(Znth j (replace_Znth k b d) 1)=1.
Proof.
 intros m v n d k a b HM HV HN HD HK HA HB HG Hgood j HJ.
 pose proof (simplex_pivot_slots_bounds m v j HM HV HJ) as HJB.
 destruct (Z.eq_dec j k) as [E|E].
 - subst; rewrite !Znth_replace_Znth_Same by lia. tauto.
 - rewrite !Znth_replace_Znth_Diff by lia. apply Hgood;assumption.
Qed.
Lemma recip_update__row_finalize : forall n d cn cd cols r e k p q,
 simplex_pivot_row_progress n d r e cols cn cd ->
 simplex_rat_div_flag 1 1 (Znth(16+r*24+e)n 0) (Znth(16+r*24+e)d 1)=1 ->
 simplex_rat_div_result 1 1 (Znth(16+r*24+e)n 0) (Znth(16+r*24+e)d 1) p q ->
 simplex_pivot_ready_zero n d cols r e (k-16-r*24) (replace_Znth k p cn) (replace_Znth k q cd).
Proof.
 intros n d cn cd cols r e k p q HP HF HR.
 unfold simplex_pivot_ready_zero. replace (16+r*24+(k-16-r*24)) with k by ring.
 unfold simplex_pivot_row_progress in HP. rewrite HP.
 unfold simplex_pivot_recip. rewrite Z.eqb_refl, HF, Z.eqb_refl.
 unfold simplex_rat_div_result, simplex_rat_reduce_result in HR.
 replace (1*Znth(16+r*24+e)n 0) with (Znth(16+r*24+e)n 0) in HR by ring.
 replace (1*Znth(16+r*24+e)d 1) with (Znth(16+r*24+e)d 1) in HR by ring.
 destruct HR as [-> ->]. reflexivity.
Qed.
Lemma zero_update__row_finalize : forall n d cn cd cols r e leaving,
 simplex_pivot_ready_zero n d cols r e leaving cn cd ->
 simplex_pivot_rows_progress n d cols r e leaving 0
 (replace_Znth (16+r*24+e) 0 cn) (replace_Znth (16+r*24+e) 1 cd).
Proof.
 intros. unfold simplex_pivot_rows_progress, simplex_pivot_rows_prefix. simpl.
 unfold simplex_pivot_before_rows. unfold simplex_pivot_ready_zero in H. rewrite H.
 reflexivity.
Qed.
Lemma app_nodup__factor_rhs {A:Type} : forall (a b:list A), NoDup a -> NoDup b ->
 (forall x, In x a -> In x b -> False) -> NoDup(a++b).
Proof.
 induction a; simpl; intros b Ha Hb Hdis; auto.
 inversion Ha; subst. constructor.
 - intro K. apply in_app_or in K. destruct K; [contradiction|eapply Hdis; eauto; simpl; auto].
 - apply IHa; auto. intros; eapply Hdis; eauto; simpl; auto.
Qed.
Lemma map_nodup__factor_rhs {A B:Type} : forall (f:A->B) l,
 NoDup l -> (forall x y, In x l -> In y l -> f x=f y -> x=y) -> NoDup(map f l).
Proof.
 intros f l. induction l; simpl; intros Hn Hi; constructor.
 - inversion Hn; subst. intro K. apply in_map_iff in K. destruct K as [y [E Hy]].
   assert(a=y) by (apply Hi; simpl; auto). subst. contradiction.
 - apply IHl. inversion Hn; auto. intros; apply Hi; simpl; auto.
Qed.
Lemma matrix_slots_nodup__factor_rhs : forall xs cols,
 NoDup xs -> 0<=cols<=24 ->
 NoDup(flat_map (fun i=>map (fun j=>16+i*24+j) (Zrange 0 cols)) xs).
Proof.
 induction xs; intros cols Hn Hc; [constructor|].
 change (NoDup (map (fun j=>16+a*24+j) (Zrange 0 cols) ++ flat_map (fun i=>map (fun j=>16+i*24+j) (Zrange 0 cols)) xs)). inversion Hn; subst.
 apply app_nodup__factor_rhs.
 - apply map_nodup__factor_rhs; [apply NoDup_Zrange|]. intros; lia.
 - apply IHxs; auto.
 - intros k Hk Hk'. apply in_map_iff in Hk. destruct Hk as [j [<- Hj]].
   apply in_flat_map in Hk'. destruct Hk' as [i [Hi Hki]].
   apply in_map_iff in Hki. destruct Hki as [j' [E Hj']].
   apply In_Zrange in Hj. apply In_Zrange in Hj'.
   assert(a=i) by (destruct (Z_lt_ge_dec a i); [nia|]; destruct (Z_lt_ge_dec i a); nia). subst. contradiction.
Qed.
Lemma slots_nodup__factor_rhs : forall rows cols, 0<=rows<=16 -> 0<=cols<=24 ->
 NoDup(simplex_pivot_slots rows cols).
Proof.
 intros rows cols Hr Hc. unfold simplex_pivot_slots. apply app_nodup__factor_rhs.
 - apply NoDup_Zrange.
 - apply matrix_slots_nodup__factor_rhs; auto using NoDup_Zrange.
 - intros k Hk Hk'. apply In_Zrange in Hk. apply in_flat_map in Hk'.
   destruct Hk' as [i [Hi Hki]]. apply in_map_iff in Hki. destruct Hki as [j [<- Hj]].
   apply In_Zrange in Hi. apply In_Zrange in Hj. nia.
Qed.
Lemma filter_keep__factor_rhs {A:Type} : forall (f:A->bool) xs,
 (forall x, In x xs -> f x=true) -> filter f xs=xs.
Proof. intros f xs. induction xs; simpl; intros H; auto. rewrite H by (simpl;auto).
 f_equal. apply IHxs. intros; apply H; simpl;auto. Qed.
Lemma filter_single_perm__factor_rhs : forall xs k, NoDup xs -> In k xs ->
 Coq.Sorting.Permutation.Permutation xs (k::filter (fun x=>negb(Z.eqb x k)) xs).
Proof.
 induction xs as [|a xs IH]; intros k Hn Hin; simpl in *; [contradiction|].
 inversion Hn; subst. destruct (Z.eq_dec a k) as [->|Hne].
 - rewrite Z.eqb_refl. simpl. assert (F:filter (fun x:Z=>negb(x =? k)) xs=xs).
   { apply filter_keep__factor_rhs. intros x Hx. apply Bool.negb_true_iff. apply Z.eqb_neq. intro E; subst; contradiction. }
   rewrite F. reflexivity.
 - assert(E:(a =? k)=false) by (apply Z.eqb_neq;auto). rewrite E. simpl.
   destruct Hin; [contradiction|]. eapply Coq.Sorting.Permutation.Permutation_trans with (l':=a::k::filter (fun x=>negb(x =? k)) xs).
   + apply Coq.Sorting.Permutation.perm_skip. apply IH; auto.
   + apply Coq.Sorting.Permutation.perm_swap.
Qed.
Lemma iter_perm__factor_rhs : forall a b:list Assertion,
 Coq.Sorting.Permutation.Permutation a b -> iter_sepcon a |-- iter_sepcon b.
Proof.
 intros a b P. induction P.
 - reflexivity.
 - rewrite !logic_equiv_iter_sepcon_cons. sep_apply IHP. cancel x. reflexivity.
 - rewrite !logic_equiv_iter_sepcon_cons. sepcon_right_assoc. cancel x. cancel y. reflexivity.
 - sep_apply IHP1. exact IHP2.
Qed.
Lemma memory_focus__factor_rhs : forall s rows cols n d k,
 0<=rows<=16 -> 0<=cols<=24 -> In k (simplex_pivot_slots rows cols) ->
 simplex_pivot_memory s rows cols n d |--
 simplex_pivot_memory_cell s k (Znth k n 0) (Znth k d 1) ** simplex_pivot_except s rows cols n d k k.
Proof.
 intros s rows cols n d k Hr Hc Hk. unfold simplex_pivot_memory, simplex_pivot_except.
 assert(E:filter (fun x=>negb((x =? k)||(x =? k))) (simplex_pivot_slots rows cols)=
 filter (fun x=>negb(x =? k)) (simplex_pivot_slots rows cols)).
 { apply filter_ext. intros x. destruct(x =? k); reflexivity. }
 rewrite E. pose proof (filter_single_perm__factor_rhs _ k (slots_nodup__factor_rhs rows cols Hr Hc) Hk) as P.
 apply (Coq.Sorting.Permutation.Permutation_map (fun j=>simplex_pivot_memory_cell s j (Znth j n 0) (Znth j d 1))) in P.
 sep_apply (iter_perm__factor_rhs _ _ P). cbn [map]. rewrite logic_equiv_iter_sepcon_cons. reflexivity.
Qed.
Lemma memory_merge__factor_rhs : forall s rows cols n d k,
 0<=rows<=16 -> 0<=cols<=24 -> In k (simplex_pivot_slots rows cols) ->
 simplex_pivot_memory_cell s k (Znth k n 0) (Znth k d 1) ** simplex_pivot_except s rows cols n d k k |--
 simplex_pivot_memory s rows cols n d.
Proof.
 intros s rows cols n d k Hr Hc Hk. unfold simplex_pivot_memory, simplex_pivot_except.
 assert(E:filter (fun x=>negb((x =? k)||(x =? k))) (simplex_pivot_slots rows cols)=
 filter (fun x=>negb(x =? k)) (simplex_pivot_slots rows cols)).
 { apply filter_ext. intros x. destruct(x =? k); reflexivity. }
 rewrite E. pose proof (filter_single_perm__factor_rhs _ k (slots_nodup__factor_rhs rows cols Hr Hc) Hk) as P.
 apply (Coq.Sorting.Permutation.Permutation_map (fun j=>simplex_pivot_memory_cell s j (Znth j n 0) (Znth j d 1))) in P.
 sep_apply_r_atomic (iter_perm__factor_rhs _ _ (Coq.Sorting.Permutation.Permutation_sym P)). cbn [map]. rewrite logic_equiv_iter_sepcon_cons. reflexivity.
Qed.
Lemma cell_a__factor_rhs : forall s i j n d, 0<=i -> 0<=j<24 ->
 simplex_pivot_memory_cell s (16+i*24+j) n d =
 ((&((((&((s) # "SxState" ->ₛ "a") + (i * (24 * sizeof("SxRat")))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> n **
 (&((((&((s) # "SxState" ->ₛ "a") + (i * (24 * sizeof("SxRat")))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> d).
Proof.
 intros s i j n d Hi Hj. unfold simplex_pivot_memory_cell.
 assert(E:(16+i*24+j <? 16)=false) by (apply Z.ltb_ge;nia). rewrite E.
 replace (16+i*24+j-16) with (i*24+j) by ring.
 assert(D:(i*24+j)/24=i) by (symmetry; apply Z.div_unique with (r:=j); lia).
 assert(M:(i*24+j) mod 24=j) by (symmetry; apply Z.mod_unique with (q:=i); lia).
 rewrite D,M. replace (sizeof("SxRat")*24) with (24*sizeof("SxRat")) by ring. reflexivity.
Qed.
Lemma pair_perm__factor_rhs : forall xs a b, NoDup xs -> In a xs -> In b xs -> a<>b ->
 Coq.Sorting.Permutation.Permutation xs
 (a::b::filter (fun k=>negb((k =? a)||(k =? b))) xs).
Proof.
 intros xs a b Hn Ha Hb Hab. apply Coq.Sorting.Permutation.NoDup_Permutation.
 - exact Hn.
 - constructor.
   + simpl. intros [E|K]; [congruence|]. apply filter_In in K. destruct K as [_ K].
     rewrite Z.eqb_refl in K. discriminate.
   + constructor.
     * intro K. apply filter_In in K. destruct K as [_ K]. rewrite Z.eqb_refl, Bool.orb_true_r in K. discriminate.
     * apply NoDup_filter. exact Hn.
 - intros k. simpl. rewrite filter_In.
   destruct (Z.eq_dec k a) as [->|Hka]; [tauto|].
   destruct (Z.eq_dec k b) as [->|Hkb]; [tauto|].
   assert(Ea:(k =? a)=false) by (apply Z.eqb_neq;auto).
   assert(Eb:(k =? b)=false) by (apply Z.eqb_neq;auto). rewrite Ea,Eb. simpl. intuition congruence.
Qed.
Lemma memory_focus_pair__factor_rhs : forall s rows cols n d a b,
 0<=rows<=16 -> 0<=cols<=24 -> In a (simplex_pivot_slots rows cols) ->
 In b (simplex_pivot_slots rows cols) -> a<>b ->
 simplex_pivot_memory s rows cols n d |--
 simplex_pivot_memory_cell s a (Znth a n 0) (Znth a d 1) **
 simplex_pivot_memory_cell s b (Znth b n 0) (Znth b d 1) ** simplex_pivot_except s rows cols n d a b.
Proof.
 intros s rows cols n d a b Hr Hc Ha Hb Hab.
 unfold simplex_pivot_memory, simplex_pivot_except.
 pose proof(pair_perm__factor_rhs _ a b (slots_nodup__factor_rhs rows cols Hr Hc) Ha Hb Hab) as P.
 apply (Coq.Sorting.Permutation.Permutation_map (fun k=>simplex_pivot_memory_cell s k (Znth k n 0) (Znth k d 1))) in P.
 sep_apply (iter_perm__factor_rhs _ _ P). cbn [map]. rewrite !logic_equiv_iter_sepcon_cons.
 sepcon_right_assoc. reflexivity.
Qed.
Lemma memory_merge_pair__factor_rhs : forall s rows cols n d a b,
 0<=rows<=16 -> 0<=cols<=24 -> In a (simplex_pivot_slots rows cols) ->
 In b (simplex_pivot_slots rows cols) -> a<>b ->
 simplex_pivot_memory_cell s a (Znth a n 0) (Znth a d 1) **
 simplex_pivot_memory_cell s b (Znth b n 0) (Znth b d 1) ** simplex_pivot_except s rows cols n d a b |--
 simplex_pivot_memory s rows cols n d.
Proof.
 intros s rows cols n d a b Hr Hc Ha Hb Hab.
 unfold simplex_pivot_memory, simplex_pivot_except.
 pose proof(pair_perm__factor_rhs _ a b (slots_nodup__factor_rhs rows cols Hr Hc) Ha Hb Hab) as P.
 apply (Coq.Sorting.Permutation.Permutation_map (fun k=>simplex_pivot_memory_cell s k (Znth k n 0) (Znth k d 1))) in P.
 sep_apply_r_atomic (iter_perm__factor_rhs _ _ (Coq.Sorting.Permutation.Permutation_sym P)).
 cbn [map]. rewrite !logic_equiv_iter_sepcon_cons. sepcon_right_assoc. reflexivity.
Qed.
Lemma addmul_exact__factor_rhs : forall f g r i n d p q u v,
 simplex_rat_mul_flag f g (Znth r n 0) (Znth r d 1)=1 ->
 simplex_rat_mul_result f g (Znth r n 0) (Znth r d 1) p q ->
 simplex_rat_add_flag (Znth i n 0) (Znth i d 1) p q=1 ->
 simplex_rat_add_result (Znth i n 0) (Znth i d 1) p q u v ->
 simplex_pivot_addmul f g r i (1,(n,d))=(1,(replace_Znth i u n,replace_Znth i v d)).
Proof.
 intros f g r i n d p q u v Hm Rm Ha Ra.
 unfold simplex_rat_mul_result, simplex_rat_reduce_result in Rm. destruct Rm as [Hp Hq].
 unfold simplex_rat_add_result, simplex_rat_reduce_result in Ra. destruct Ra as [Hu Hv].
 unfold simplex_pivot_addmul. cbn beta iota zeta.
 rewrite Z.eqb_refl, Hm, Z.eqb_refl. rewrite <-Hp, <-Hq, Ha, Z.eqb_refl.
 unfold simplex_pivot_put. cbn beta iota zeta. rewrite <-Hu, <-Hv. reflexivity.
Qed.
Lemma columns_zero__factor_rhs : forall n d cols r e leaving i f g cn cd p q u v,
 simplex_pivot_rows_progress n d cols r e leaving i cn cd ->
 simplex_rat_mul_flag f g (Znth r cn 0) (Znth r cd 1)=1 ->
 simplex_rat_mul_result f g (Znth r cn 0) (Znth r cd 1) p q ->
 simplex_rat_add_flag (Znth i cn 0) (Znth i cd 1) p q=1 ->
 simplex_rat_add_result (Znth i cn 0) (Znth i cd 1) p q u v ->
 simplex_pivot_columns_progress n d cols r e leaving i 0 f g (replace_Znth i u cn) (replace_Znth i v cd).
Proof.
 intros n d cols r e leaving i f g cn cd p q u v Hs Hm Rm Ha Ra.
 unfold simplex_pivot_columns_progress, simplex_pivot_other_prefix.
 change (simplex_pivot_addmul f g r i (simplex_pivot_rows_prefix r e cols i (simplex_pivot_before_rows n d cols r e leaving))=(1,(replace_Znth i u cn,replace_Znth i v cd))).
 unfold simplex_pivot_rows_progress in Hs. rewrite Hs. eapply addmul_exact__factor_rhs; eauto.
Qed.
Lemma except_replace__factor_rhs : forall s rows cols n d i r u v,
 0<=rows<=16 -> 0<=cols<=24 -> Zlength n=400 -> Zlength d=400 -> 0<=i<400 ->
 simplex_pivot_except s rows cols (replace_Znth i u n) (replace_Znth i v d) i r=
 simplex_pivot_except s rows cols n d i r.
Proof.
 intros s rows cols n d i r u v Hr Hc Hn Hd Hi. unfold simplex_pivot_except. f_equal.
 apply map_ext_in. intros k Hk. apply filter_In in Hk. destruct Hk as [Hk Hb].
 pose proof(simplex_pivot_slots_bounds rows cols k Hr Hc Hk) as Hbound.
 assert(Hki:k<>i). { intro E; subst k. rewrite Z.eqb_refl in Hb. discriminate. }
 rewrite !Znth_replace_Znth_Diff by lia. reflexivity.
Qed.
Lemma active_update__factor_rhs : forall rows cols n d i u v,
 0<=rows<=16 -> 0<=cols<=24 -> Zlength n=400 -> Zlength d=400 -> 0<=i<400 ->
 (-INT_MAX<=u<=INT_MAX) -> 1<=v<=INT_MAX -> Z.gcd(Z.abs u)v=1 ->
 (forall k, In k (simplex_pivot_slots rows cols) ->
 ((-INT_MAX<=Znth k n 0<=INT_MAX)/\(1<=Znth k d 1<=INT_MAX))/\Z.gcd(Z.abs(Znth k n 0))(Znth k d 1)=1) ->
 forall k, In k (simplex_pivot_slots rows cols) ->
 ((-INT_MAX<=Znth k (replace_Znth i u n) 0<=INT_MAX)/\(1<=Znth k (replace_Znth i v d) 1<=INT_MAX))/\
 Z.gcd(Z.abs(Znth k (replace_Znth i u n) 0))(Znth k (replace_Znth i v d) 1)=1.
Proof.
 intros rows cols n d i u v Hr Hc Hn Hd Hi Hu Hv Hg Hgood k Hk.
 pose proof(simplex_pivot_slots_bounds rows cols k Hr Hc Hk) as Hbound.
 destruct(Z.eq_dec k i) as [->|Hne].
 - rewrite !Znth_replace_Znth_Same by lia. tauto.
 - rewrite !Znth_replace_Znth_Diff by lia. apply Hgood; auto.
Qed.
Lemma cell_rhs__factor_rhs : forall s i n d, 0<=i<16 ->
 simplex_pivot_memory_cell s i n d =
 ((&(((&((s) # "SxState" ->ₛ "rhs") + (i * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> n **
 (&(((&((s) # "SxState" ->ₛ "rhs") + (i * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> d).
Proof.
 intros s i n d Hi. unfold simplex_pivot_memory_cell. assert(E:(i <? 16)=true) by (apply Z.ltb_lt;lia).
 rewrite E. unfold simplex_scan_rat_memory. csimpl. reflexivity.
Qed.
Lemma memory_update_rhs__factor_rhs : forall s rows cols n d i r u v,
 0<=rows<=16 -> 0<=cols<=24 -> Zlength n=400 -> Zlength d=400 ->
 0<=i<rows -> 0<=r<rows -> i<>r ->
 simplex_pivot_memory_cell s i u v ** simplex_pivot_memory_cell s r (Znth r n 0) (Znth r d 1) **
 simplex_pivot_except s rows cols n d i r |--
 simplex_pivot_memory s rows cols (replace_Znth i u n) (replace_Znth i v d).
Proof.
 intros s rows cols n d i r u v Hr Hc Hn Hd Hi Hri Hne.
 sep_apply_r_atomic (memory_merge_pair__factor_rhs s rows cols (replace_Znth i u n) (replace_Znth i v d) i r Hr Hc
 (simplex_pivot_rhs_active rows cols i Hi) (simplex_pivot_rhs_active rows cols r Hri) Hne).
 rewrite except_replace__factor_rhs by lia.
 rewrite !Znth_replace_Znth_Same by lia. rewrite !Znth_replace_Znth_Diff by lia. reflexivity.
Qed.
Lemma pivot_map_nodup__other_columns : forall (f:Z->Z) xs,
 NoDup xs -> (forall a b, In a xs -> In b xs -> f a=f b -> a=b) -> NoDup(map f xs).
Proof.
 intros f xs H. induction H as [|a xs Hnot Hnd IH];intro Hinj;cbn -[Z.add Z.mul Z.sub iter_sepcon];constructor.
 - intro H. apply in_map_iff in H. destruct H as [b [E Hb]].
   apply Hnot. assert(a=b) by (apply Hinj;[left;reflexivity|right;exact Hb|symmetry;exact E]). now subst.
 - apply IH. intros;apply Hinj;auto using in_cons.
Qed.
Lemma pivot_flat_nodup__other_columns : forall xs cols,
 NoDup xs -> 0<=cols<=24 ->
 NoDup(flat_map (fun i=>map(fun j=>16+i*24+j)(Zrange 0 cols)) xs).
Proof.
 intros xs cols Hnd Hcols. induction Hnd as [|i xs Hnot Hnd IH];cbn -[Z.add Z.mul Z.sub iter_sepcon];[constructor|].
 apply NoDup_app;[|exact IH|].
 - apply pivot_map_nodup__other_columns;[apply NoDup_Zrange|]. intros;lia.
 - intros k Hk Hk'. apply in_map_iff in Hk. destruct Hk as [j [<- Hj]].
   apply in_flat_map in Hk'. destruct Hk' as [i' [Hi' Hk']].
   apply in_map_iff in Hk'. destruct Hk' as [j' [E Hj']].
   apply In_Zrange in Hj. apply In_Zrange in Hj'.
   assert(i=i') by lia. subst i'. contradiction.
Qed.
Lemma pivot_slots_nodup__other_columns : forall rows cols,
 0<=rows<=16 -> 0<=cols<=24 -> NoDup(simplex_pivot_slots rows cols).
Proof.
 intros rows cols Hr Hc. unfold simplex_pivot_slots.
 apply NoDup_app;[apply NoDup_Zrange|apply pivot_flat_nodup__other_columns;auto;apply NoDup_Zrange|].
 intros k Hk Hk'. apply In_Zrange in Hk. apply in_flat_map in Hk'.
 destruct Hk' as [i [Hi Hki]]. apply In_Zrange in Hi.
 apply in_map_iff in Hki. destruct Hki as [j [E Hj]]. apply In_Zrange in Hj. nia.
Qed.
Lemma pivot_filter_absent__other_columns : forall l k,
 ~In k l -> filter(fun x=>negb(Z.eqb x k))l=l.
Proof.
 induction l as [|a l IH];intros k H;cbn -[Z.add Z.mul Z.sub iter_sepcon];auto.
 assert(E:Z.eqb a k=false) by (apply Z.eqb_neq;intro He;subst a;apply H;left;reflexivity).
 rewrite E. cbn -[Z.add Z.mul Z.sub iter_sepcon]. f_equal. apply IH. intro Hin;apply H;right;exact Hin.
Qed.
Lemma pivot_iter_focus__other_columns : forall (f:Z->Assertion) l k,
 NoDup l -> In k l ->
 iter_sepcon(map f l) |-- f k ** iter_sepcon(map f(filter(fun x=>negb(Z.eqb x k))l)).
Proof.
 intros f l. induction l as [|a l IH];intros k Hnd Hin;[contradiction|].
 inversion Hnd as [|a' l' Hnot Htail];subst.
 destruct(Z.eq_dec a k) as [->|Hne].
 - cbn -[Z.add Z.mul Z.sub iter_sepcon]. rewrite Z.eqb_refl. cbn -[Z.add Z.mul Z.sub iter_sepcon].
   rewrite pivot_filter_absent__other_columns by exact Hnot.
   rewrite logic_equiv_iter_sepcon_cons. reflexivity.
 - assert(E:Z.eqb a k=false) by (apply Z.eqb_neq;exact Hne).
   cbn -[Z.add Z.mul Z.sub iter_sepcon]. rewrite E. cbn -[Z.add Z.mul Z.sub iter_sepcon]. rewrite !logic_equiv_iter_sepcon_cons.
   sep_apply (IH k Htail ltac:(destruct Hin;[contradiction|assumption])).
   sepcon_right_assoc. cancel (f k). cancel (f a). reflexivity.
Qed.
Lemma pivot_iter_merge__other_columns : forall (f:Z->Assertion) l k,
 NoDup l -> In k l ->
 f k ** iter_sepcon(map f(filter(fun x=>negb(Z.eqb x k))l)) |-- iter_sepcon(map f l).
Proof.
 intros f l. induction l as [|a l IH];intros k Hnd Hin;[contradiction|].
 inversion Hnd as [|a' l' Hnot Htail];subst.
 destruct(Z.eq_dec a k) as [->|Hne].
 - cbn -[Z.add Z.mul Z.sub iter_sepcon]. rewrite Z.eqb_refl. cbn -[Z.add Z.mul Z.sub iter_sepcon].
   rewrite pivot_filter_absent__other_columns by exact Hnot.
   rewrite logic_equiv_iter_sepcon_cons. reflexivity.
 - assert(E:Z.eqb a k=false) by (apply Z.eqb_neq;exact Hne).
   cbn -[Z.add Z.mul Z.sub iter_sepcon]. rewrite E. cbn -[Z.add Z.mul Z.sub iter_sepcon]. rewrite !logic_equiv_iter_sepcon_cons.
   sep_apply_r_atomic (IH k Htail ltac:(destruct Hin;[contradiction|assumption])).
   sepcon_right_assoc. cancel (f k). cancel (f a). reflexivity.
Qed.
Lemma pivot_filter_two__other_columns : forall l a b,
 filter(fun k=>negb(Z.eqb k b))(filter(fun k=>negb(Z.eqb k a))l)=
 filter(fun k=>negb(Z.eqb k a || Z.eqb k b))l.
Proof. induction l as [|k l IH];intros a b;cbn;[reflexivity|].
 destruct(Z.eqb k a) eqn:Ea;destruct(Z.eqb k b) eqn:Eb;cbn;rewrite ?Ea,?Eb;cbn;rewrite IH;reflexivity. Qed.
Lemma pivot_memory_focus__other_columns : forall s rows cols n d a b,
 0<=rows<=16 -> 0<=cols<=24 -> In a(simplex_pivot_slots rows cols) ->
 In b(simplex_pivot_slots rows cols) -> a<>b ->
 simplex_pivot_memory s rows cols n d |--
 simplex_pivot_memory_cell s a (Znth a n 0)(Znth a d 1) **
 simplex_pivot_memory_cell s b (Znth b n 0)(Znth b d 1) **
 simplex_pivot_except s rows cols n d a b.
Proof.
 intros s rows cols n d a b Hr Hc Ha Hb Hab.
 pose proof(pivot_slots_nodup__other_columns rows cols Hr Hc) as Hnd.
 unfold simplex_pivot_memory,simplex_pivot_except.
 sep_apply(pivot_iter_focus__other_columns (fun k=>simplex_pivot_memory_cell s k (Znth k n 0)(Znth k d 1)) (simplex_pivot_slots rows cols) a Hnd Ha).
 assert(Hb':In b(filter(fun k=>negb(Z.eqb k a))(simplex_pivot_slots rows cols))).
 { apply filter_In. split;auto. apply Bool.negb_true_iff,Z.eqb_neq. lia. }
 sep_apply(pivot_iter_focus__other_columns (fun k=>simplex_pivot_memory_cell s k (Znth k n 0)(Znth k d 1)) (filter(fun k=>negb(Z.eqb k a))(simplex_pivot_slots rows cols)) b (NoDup_filter _ Hnd) Hb').
 rewrite pivot_filter_two__other_columns. sepcon_right_assoc.
 repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end.
 try reflexivity.
Qed.
Lemma pivot_memory_merge__other_columns : forall s rows cols n d a b,
 0<=rows<=16 -> 0<=cols<=24 -> In a(simplex_pivot_slots rows cols) ->
 In b(simplex_pivot_slots rows cols) -> a<>b ->
 simplex_pivot_memory_cell s a (Znth a n 0)(Znth a d 1) **
 simplex_pivot_memory_cell s b (Znth b n 0)(Znth b d 1) **
 simplex_pivot_except s rows cols n d a b |-- simplex_pivot_memory s rows cols n d.
Proof.
 intros s rows cols n d a b Hr Hc Ha Hb Hab.
 pose proof(pivot_slots_nodup__other_columns rows cols Hr Hc) as Hnd.
 unfold simplex_pivot_memory,simplex_pivot_except.
 rewrite <-pivot_filter_two__other_columns.
 sep_apply_r_atomic(pivot_iter_merge__other_columns (fun k=>simplex_pivot_memory_cell s k (Znth k n 0)(Znth k d 1)) (simplex_pivot_slots rows cols) a Hnd Ha).
 assert(Hb':In b(filter(fun k=>negb(Z.eqb k a))(simplex_pivot_slots rows cols))).
 { apply filter_In. split;auto. apply Bool.negb_true_iff,Z.eqb_neq. lia. }
 sep_apply_r_atomic(pivot_iter_merge__other_columns (fun k=>simplex_pivot_memory_cell s k (Znth k n 0)(Znth k d 1)) (filter(fun k=>negb(Z.eqb k a))(simplex_pivot_slots rows cols)) b (NoDup_filter _ Hnd) Hb').
 sepcon_right_assoc.
 repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end.
 try reflexivity.
Qed.
Lemma pivot_matrix_cell__other_columns : forall s i j n d,
 0<=i -> 0<=j<24 -> simplex_pivot_memory_cell s (16+i*24+j) n d =

 (&((((&((s) # "SxState" ->ₛ "a") + (i * (24 * sizeof("SxRat")))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> n **
 (&((((&((s) # "SxState" ->ₛ "a") + (i * (24 * sizeof("SxRat")))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> d.
Proof.
 intros s i j n d Hi Hj. unfold simplex_pivot_memory_cell.
 assert(E:Z.ltb(16+i*24+j)16=false) by (apply Z.ltb_ge;nia). rewrite E.
 replace(16+i*24+j-16) with (j+i*24) by ring.
 rewrite Z.div_add,Z.mod_add by lia. rewrite Z.div_small,Z.mod_small by lia.
 replace(0+i) with i by lia. replace(sizeof("SxRat")*24) with (24*sizeof("SxRat")) by ring.
 reflexivity.
Qed.
Lemma pivot_column_skip__other_columns : forall n d cols r e leaving i j fnum fd cn cd,
 0<=j -> j=e -> simplex_pivot_columns_progress n d cols r e leaving i j fnum fd cn cd ->
 simplex_pivot_columns_progress n d cols r e leaving i (j+1) fnum fd cn cd.
Proof. intros. unfold simplex_pivot_columns_progress in *. rewrite simplex_pivot_other_step by lia.
 unfold simplex_pivot_other_column. subst j. rewrite Z.eqb_refl. assumption. Qed.
Lemma pivot_addmul_exact__other_columns : forall fnum fden src dst cn cd p q u v,
 simplex_rat_mul_flag fnum fden (Znth src cn 0)(Znth src cd 1)=1 ->
 simplex_rat_mul_result fnum fden (Znth src cn 0)(Znth src cd 1) p q ->
 simplex_rat_add_flag (Znth dst cn 0)(Znth dst cd 1) p q=1 ->
 simplex_rat_add_result (Znth dst cn 0)(Znth dst cd 1) p q u v ->
 simplex_pivot_addmul fnum fden src dst (1,(cn,cd))=
 (1,(replace_Znth dst u cn,replace_Znth dst v cd)).
Proof.
 intros fnum fden src dst cn cd p q u v HM HR HA HS.
 unfold simplex_rat_mul_result,simplex_rat_reduce_result in HR. destruct HR as [HP HQ].
 unfold simplex_rat_add_result,simplex_rat_reduce_result in HS. destruct HS as [HU HV].
 unfold simplex_pivot_addmul. rewrite HM,Z.eqb_refl.
 cbv beta iota zeta.
 rewrite <-HP,<-HQ,HA,Z.eqb_refl. unfold simplex_pivot_put.
 rewrite <-HU,<-HV. reflexivity.
Qed.
Lemma pivot_column_step__other_columns : forall n d cols r e leaving i j fnum fden cn cd p q u v,
 0<=j -> j<>e -> simplex_pivot_columns_progress n d cols r e leaving i j fnum fden cn cd ->
 simplex_rat_mul_flag fnum fden (Znth(16+r*24+j)cn 0)(Znth(16+r*24+j)cd 1)=1 ->
 simplex_rat_mul_result fnum fden (Znth(16+r*24+j)cn 0)(Znth(16+r*24+j)cd 1) p q ->
 simplex_rat_add_flag (Znth(16+i*24+j)cn 0)(Znth(16+i*24+j)cd 1)p q=1 ->
 simplex_rat_add_result (Znth(16+i*24+j)cn 0)(Znth(16+i*24+j)cd 1)p q u v ->
 simplex_pivot_columns_progress n d cols r e leaving i (j+1) fnum fden
 (replace_Znth(16+i*24+j)u cn)(replace_Znth(16+i*24+j)v cd).
Proof.
 intros n d cols r e leaving i j fnum fden cn cd p q u v Hj Hne HP HM HR HA HS.
 unfold simplex_pivot_columns_progress in *. rewrite simplex_pivot_other_step by lia.
 unfold simplex_pivot_other_column. assert(E:Z.eqb j e=false) by (apply Z.eqb_neq;auto).
 rewrite E,HP. apply(pivot_addmul_exact__other_columns fnum fden (16+r*24+j) (16+i*24+j) cn cd p q u v);assumption.
Qed.
Lemma pivot_good_put__other_columns : forall rows cols cn cd k u v,
 0<=rows<=16 -> 0<=cols<=24 -> Zlength cn=400 -> Zlength cd=400 -> 0<=k<400 ->
 (forall t,In t(simplex_pivot_slots rows cols) ->
 (((-INT_MAX<=Znth t cn 0<=INT_MAX)/\ 1<=Znth t cd 1)/\Znth t cd 1<=INT_MAX)/\Zgcd(Zabs(Znth t cn 0))(Znth t cd 1)=1) ->
 -INT_MAX<=u<=INT_MAX -> 1<=v<=INT_MAX -> Zgcd(Zabs u)v=1 ->
 forall t,In t(simplex_pivot_slots rows cols) ->
 (((-INT_MAX<=Znth t(replace_Znth k u cn)0<=INT_MAX)/\ 1<=Znth t(replace_Znth k v cd)1)/\Znth t(replace_Znth k v cd)1<=INT_MAX)/\ Zgcd(Zabs(Znth t(replace_Znth k u cn)0))(Znth t(replace_Znth k v cd)1)=1.
Proof.
 intros rows cols cn cd k u v Hrows Hcols Hn Hd Hk Hg Hu Hv Huv t Ht.
 pose proof(simplex_pivot_slots_bounds rows cols t Hrows Hcols Ht) as Htb.
 destruct(Z.eq_dec k t) as [<-|Hne].
 - rewrite !Znth_replace_Znth_Same by lia. tauto.
 - rewrite !Znth_replace_Znth_Diff by lia. apply Hg. exact Ht.
Qed.
Lemma pivot_except_put__other_columns : forall s rows cols cn cd a b u v,
 0<=rows<=16 -> 0<=cols<=24 -> Zlength cn=400 -> Zlength cd=400 -> 0<=b<400 ->
 simplex_pivot_except s rows cols cn cd a b=
 simplex_pivot_except s rows cols (replace_Znth b u cn)(replace_Znth b v cd)a b.
Proof.
 intros s rows cols cn cd a b u v Hrows Hcols Hn Hd Hb.
 unfold simplex_pivot_except. f_equal. apply map_ext_in. intros k Hk.
 apply filter_In in Hk. destruct Hk as [Hmem Hk].
 pose proof(simplex_pivot_slots_bounds rows cols k Hrows Hcols Hmem) as Hkbounds.
 apply Bool.negb_true_iff in Hk. apply Bool.orb_false_iff in Hk.
 destruct Hk as [_ Hkb]. apply Z.eqb_neq in Hkb.
 rewrite !Znth_replace_Znth_Diff by lia. reflexivity.
Qed.
Lemma pivot_matrix_update__other_columns : forall s rows cols cn cd r i j u v,
 0<=rows<=16 -> 0<=cols<=24 -> 0<=r<rows -> 0<=i<rows -> r<>i -> 0<=j<cols ->
 Zlength cn=400 -> Zlength cd=400 ->
 simplex_pivot_memory_cell s (16+r*24+j)(Znth(16+r*24+j)cn 0)(Znth(16+r*24+j)cd 1) **
 simplex_pivot_memory_cell s (16+i*24+j)u v **
 simplex_pivot_except s rows cols cn cd (16+r*24+j)(16+i*24+j) |--
 simplex_pivot_memory s rows cols(replace_Znth(16+i*24+j)u cn)(replace_Znth(16+i*24+j)v cd).
Proof.
 intros s rows cols cn cd r i j u v Hrows Hcols Hr Hi Hri Hj Hn Hd.
 rewrite(pivot_except_put__other_columns s rows cols cn cd (16+r*24+j)(16+i*24+j)u v Hrows Hcols Hn Hd ltac:(lia)).
 sep_apply_r_atomic(pivot_memory_merge__other_columns s rows cols (replace_Znth(16+i*24+j)u cn)
 (replace_Znth(16+i*24+j)v cd)(16+r*24+j)(16+i*24+j)Hrows Hcols
 (simplex_pivot_a_active rows cols r j Hr Hj)(simplex_pivot_a_active rows cols i j Hi Hj)ltac:(lia)).
 rewrite !Znth_replace_Znth_Same by lia. rewrite !Znth_replace_Znth_Diff by lia.
 reflexivity.
Qed.
Lemma range_split__failure_matrix : forall a b, 0<=a<=b ->
 Zrange 0 b=(Zrange 0 a++Zrange a b)%list.
Proof. intros a b H. unfold Zrange. replace (b-0) with (a+(b-a)) by lia. replace (a-0) with a by lia.
 rewrite Z2Nat.inj_add by lia. rewrite Zrange_aux_app. rewrite Z2Nat.id by lia.
 replace (0+a) with a by lia. reflexivity. Qed.
Lemma other_failure_suffix__failure_matrix : forall n d cols r e b rows i j fnum fd cn cd,
 0<=j<cols -> 0<=i<rows -> i<>r -> fnum<>0 ->
 simplex_pivot_factor n d cols r e b i fnum fd ->
 simplex_pivot_columns_progress n d cols r e b i j fnum fd cn cd ->
 simplex_pivot_other_column fnum fd r i e (1,(cn,cd)) j=(0,(cn,cd)) ->
 simplex_pivot_result n d rows cols r e b 0 cn cd.
Proof.
 intros n d cols r e b rows i j fnum fd cn cd Hj Hi Hir Hfn [an [ad [Hprog [Hfnv Hfdv]]]] Hcol Hfail.
 unfold simplex_pivot_result, simplex_pivot_compute.
 change (simplex_pivot_rows_prefix r e cols rows (simplex_pivot_before_rows n d cols r e b)=(0,(cn,cd))).
 unfold simplex_pivot_rows_prefix at 1.
 rewrite (range_split__failure_matrix (i+1) rows) by lia. rewrite fold_left_app.
 change (fold_left (simplex_pivot_other_row r e cols) (Zrange (i+1) rows)
 (simplex_pivot_rows_prefix r e cols (i+1) (simplex_pivot_before_rows n d cols r e b))=(0,(cn,cd))).
 rewrite simplex_pivot_rows_step by lia. unfold simplex_pivot_rows_progress in Hprog.
 rewrite Hprog. unfold simplex_pivot_other_row.
 assert(Eir:Z.eqb i r=false) by (apply Z.eqb_neq;auto).
 rewrite Eir. cbn [fst]. rewrite <-Hfnv,<-Hfdv.
 assert(Efn:Z.eqb fnum 0=false) by (apply Z.eqb_neq;auto). rewrite Efn.
 assert(HP:simplex_pivot_other_prefix fnum fd r i e cols
 (simplex_pivot_addmul fnum fd r i (1,(an,ad)))=(0,(cn,cd))).
 { unfold simplex_pivot_other_prefix at 1.
 rewrite(range_split__failure_matrix (j+1) cols) by lia. rewrite fold_left_app.
 change (fold_left (simplex_pivot_other_column fnum fd r i e) (Zrange (j+1) cols)
 (simplex_pivot_other_prefix fnum fd r i e (j+1) (simplex_pivot_addmul fnum fd r i (1,(an,ad))))=(0,(cn,cd))).
 rewrite simplex_pivot_other_step by lia. unfold simplex_pivot_columns_progress in Hcol.
 rewrite Hprog in Hcol. rewrite Hcol,Hfail.
 apply simplex_pivot_fold_fixed. intros x. unfold simplex_pivot_other_column.
 destruct(Z.eqb x e);reflexivity. }
 rewrite HP. cbn [simplex_pivot_zero]. apply simplex_pivot_fold_fixed.
 intros x. unfold simplex_pivot_other_row. destruct(Z.eqb x r);reflexivity.
Qed.
Lemma nodup_map__failure_matrix : forall (f:Z->Z) xs,
 NoDup xs -> (forall x y,In x xs -> In y xs -> f x=f y -> x=y) -> NoDup(map f xs).
Proof. intros f xs Hnd. induction Hnd as [|x xs Hnot Hnd IH];intros Hf;cbn;constructor.
 - intro Hin. apply in_map_iff in Hin. destruct Hin as [y [E Hy]]. assert(Eyx:y=x) by (apply Hf; [right;exact Hy|left;reflexivity|exact E]). subst y. contradiction.
 - apply IH. intros a b Ha Hb E. apply Hf; [right;exact Ha|right;exact Hb|exact E].
Qed.
Lemma nodup_flat__failure_matrix : forall (f:Z->list Z) xs,
 NoDup xs -> (forall x,In x xs -> NoDup(f x)) ->
 (forall x y z,In x xs -> In y xs -> In z(f x) -> In z(f y) -> x=y) -> NoDup(flat_map f xs).
Proof. intros f xs Hnd. induction Hnd as [|x xs Hnot Hnd IH];intros Hf Hd;cbn;[constructor|].
 apply NoDup_app. repeat split.
 - apply Hf. left;reflexivity.
 - apply IH.
   + intros y Hy. apply Hf. right;exact Hy.
   + intros a b z Ha Hb Hz Hbz. eapply Hd;[right;exact Ha|right;exact Hb|exact Hz|exact Hbz].
 - intros z Hz Hin. apply in_flat_map in Hin. destruct Hin as [y [Hy Hzy]].
   assert(E:x=y) by (eapply Hd;[left;reflexivity|right;exact Hy|exact Hz|exact Hzy]). subst y. contradiction.
Qed.
Lemma slots_nodup__failure_matrix : forall m v, 0<=m<=16 -> 0<=v<=24 -> NoDup(simplex_pivot_slots m v).
Proof. intros m v Hm Hv. unfold simplex_pivot_slots. apply NoDup_app. repeat split.
 - apply NoDup_Zrange.
 - apply nodup_flat__failure_matrix.
   + apply NoDup_Zrange.
   + intros i Hi. apply nodup_map__failure_matrix;[apply NoDup_Zrange|]. intros;lia.
   + intros i t z Hi Ht Hz Hzt. apply in_map_iff in Hz. apply in_map_iff in Hzt.
     destruct Hz as [a [<- Ha]],Hzt as [c [E Hc]]. apply In_Zrange in Ha. apply In_Zrange in Hc. nia.
 - intros z Hz Hzz. apply In_Zrange in Hz. apply in_flat_map in Hzz. destruct Hzz as [i [Hi Hj]].
   apply In_Zrange in Hi. apply in_map_iff in Hj. destruct Hj as [j [<- Hj]]. apply In_Zrange in Hj. nia.
Qed.
Lemma filter_merge__failure_matrix : forall (xs:list Z) (F:Z->Assertion) k,
 NoDup xs -> In k xs ->
 iter_sepcon(map F (filter(fun x=>negb(Z.eqb x k)) xs)) ** F k |-- iter_sepcon(map F xs).
Proof.
 intros xs F k Hnd. induction Hnd as [|a xs Hnot Hnd IH];intro Hin;[contradiction|].
 destruct(Z.eq_dec a k) as [->|Hne].
 - cbn [filter map]. rewrite Z.eqb_refl. cbn [negb].
   assert(Hf:filter(fun x:Z=>negb(Z.eqb x k)) xs=xs).
   { clear IH Hnd Hin. induction xs as [|x xs IH];[reflexivity|]. cbn. assert(E:Z.eqb x k=false) by (apply Z.eqb_neq;intro E;subst x;apply Hnot;left;reflexivity). rewrite E. cbn. f_equal. apply IH. intro Hk. apply Hnot. right;exact Hk. }
   rewrite Hf. change (iter_sepcon(map F xs) ** F k |-- iter_sepcon(F k::map F xs)). rewrite logic_equiv_iter_sepcon_cons. cancel(F k). reflexivity.
 - assert(E:Z.eqb a k=false) by (apply Z.eqb_neq;auto). cbn [filter map]. rewrite E. cbn [negb map].
   rewrite !logic_equiv_iter_sepcon_cons. csimpl. sep_apply (IH ltac:(destruct Hin;[contradiction|auto])). cancel(F a). reflexivity.
Qed.
Lemma dual_merge__failure_matrix : forall xs (F:Z->Assertion) k t,
 NoDup xs -> In k xs -> In t xs -> k<>t ->
 iter_sepcon(map F(filter(fun x=>negb(Z.eqb x k || Z.eqb x t))xs)) ** F k ** F t |--iter_sepcon(map F xs).
Proof. intros xs F k t Hnd Hk Ht Hne.
 assert(E:filter(fun x=>negb(Z.eqb x k || Z.eqb x t))xs=
 filter(fun x=>negb(Z.eqb x t))(filter(fun x=>negb(Z.eqb x k))xs)).
 { clear Hnd Hk Ht Hne. induction xs as [|x xs IH];[reflexivity|]. cbn. destruct(Z.eqb x k) eqn:Ek, (Z.eqb x t) eqn:Et;cbn;rewrite ?Ek,?Et;cbn;rewrite IH;reflexivity. }
 rewrite E. sep_apply (filter_merge__failure_matrix (filter(fun x=>negb(Z.eqb x k))xs) F t (NoDup_filter _ Hnd) ltac:(apply filter_In;split;auto;apply Bool.negb_true_iff,Z.eqb_neq;lia)).
 sep_apply(filter_merge__failure_matrix xs F k Hnd Hk). reflexivity.
Qed.
Lemma matrix_cell__failure_matrix : forall s i j n d, 0<=i -> 0<=j<24 ->
 simplex_pivot_memory_cell s (16+i*24+j) n d=
 (&((((&((s) # "SxState" ->ₛ "a") + (i * (24 * sizeof("SxRat")))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "num")) # Int |-> n **
 (&((((&((s) # "SxState" ->ₛ "a") + (i * (24 * sizeof("SxRat")))) + (j * sizeof("SxRat")))) # "SxRat" ->ₛ "den")) # Int |-> d.
Proof. intros s i j n d Hi Hj. unfold simplex_pivot_memory_cell.
 assert(E:Z.ltb (16+i*24+j) 16=false) by (apply Z.ltb_ge;lia). rewrite E.
 replace (16+i*24+j-16) with (i*24+j) by ring.
 rewrite Z.div_add_l by lia. rewrite Z.div_small by lia.
 replace (i*24+j) with (j+i*24) by ring. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
 replace (i+0) with i by lia. replace (sizeof("SxRat")*24) with (24*sizeof("SxRat")) by ring. reflexivity.
Qed.
Lemma memory_merge__failure_matrix : forall s m v cn cd r i j,
 0<=m<=16 -> 0<=v<=24 -> 0<=r<m -> 0<=i<m -> i<>r -> 0<=j<v ->
 simplex_pivot_except s m v cn cd (16+r*24+j) (16+i*24+j) **
 simplex_pivot_memory_cell s (16+r*24+j) (Znth(16+r*24+j)cn 0) (Znth(16+r*24+j)cd 1) **
 simplex_pivot_memory_cell s (16+i*24+j) (Znth(16+i*24+j)cn 0) (Znth(16+i*24+j)cd 1)
 |-- simplex_pivot_memory s m v cn cd.
Proof. intros. unfold simplex_pivot_except,simplex_pivot_memory.
 apply (dual_merge__failure_matrix (simplex_pivot_slots m v) (fun k=>simplex_pivot_memory_cell s k (Znth k cn 0) (Znth k cd 1)) (16+r*24+j) (16+i*24+j));try apply slots_nodup__failure_matrix;try apply simplex_pivot_a_active;auto;lia.
Qed.
Lemma addmul_mul_reject__failure_matrix : forall fnn fd src dst cn cd,
 simplex_rat_mul_flag fnn fd (Znth src cn 0) (Znth src cd 1)=0 ->
 simplex_pivot_addmul fnn fd src dst (1,(cn,cd))=(0,(cn,cd)).
Proof. intros. unfold simplex_pivot_addmul. rewrite H. reflexivity. Qed.
Lemma addmul_add_reject__failure_matrix : forall fnn fd src dst cn cd p q,
 simplex_rat_mul_flag fnn fd (Znth src cn 0) (Znth src cd 1)=1 ->
 simplex_rat_mul_result fnn fd (Znth src cn 0) (Znth src cd 1) p q ->
 simplex_rat_add_flag (Znth dst cn 0) (Znth dst cd 1) p q=0 ->
 simplex_pivot_addmul fnn fd src dst (1,(cn,cd))=(0,(cn,cd)).
Proof. intros fnn fd src dst cn cd p q HM [HP HQ] HA.
 unfold simplex_pivot_addmul. rewrite HM. cbn [Z.eqb]. rewrite <-HP,<-HQ,HA. reflexivity. Qed.
Lemma range_split__failure_rhs : forall a b c, a<=b<=c -> Zrange a c=List.app (Zrange a b) (Zrange b c).
Proof. intros a b c H. unfold Zrange. replace(c-a) with ((b-a)+(c-b)) by lia. rewrite Z2Nat.inj_add by lia. rewrite Zrange_aux_app. rewrite Z2Nat.id by lia. replace(a+(b-a)) with b by lia. reflexivity. Qed.
Lemma rhs_failure_suffix__failure_rhs : forall n d m v r e b i cn cd fnum fd,
 0<=i<m -> i<>r -> fnum<>0 ->
 simplex_pivot_rows_progress n d v r e b i cn cd ->
 fnum=Znth(16+i*24+e)cn 0 -> fd=Znth(16+i*24+e)cd 1 ->
 simplex_pivot_addmul fnum fd r i (1,(cn,cd))=(0,(cn,cd)) ->
 simplex_pivot_result n d m v r e b 0 cn cd.
Proof.
 intros n d m v r e b i cn cd fnum fd Hi Hne Hfnum HP HF HD HA.
 unfold simplex_pivot_result, simplex_pivot_compute.
 change(simplex_pivot_rows_prefix r e v m (simplex_pivot_before_rows n d v r e b)=(0,(cn,cd))).
 unfold simplex_pivot_rows_prefix in *.
 rewrite(range_split__failure_rhs 0 (i+1) m ltac:(lia)),fold_left_app.
 fold (simplex_pivot_rows_prefix r e v (i+1) (simplex_pivot_before_rows n d v r e b)).
 rewrite simplex_pivot_rows_step by lia. unfold simplex_pivot_rows_progress in HP. rewrite HP.
 unfold simplex_pivot_other_row. assert(NE:(i =? r)=false) by (apply Z.eqb_neq;exact Hne). rewrite NE. cbn zeta.
 rewrite <-HF, <-HD. assert(NF:(fnum =? 0)=false) by (apply Z.eqb_neq;exact Hfnum). rewrite NF. rewrite HA,simplex_pivot_other_failed.
 change(fold_left (simplex_pivot_other_row r e v) (Zrange (i+1) m) (0,(cn,cd))=(0,(cn,cd))).
 apply simplex_pivot_fold_fixed. intros k. unfold simplex_pivot_other_row. destruct(Z.eqb k r); reflexivity.
Qed.
Lemma addmul_reject_mul__failure_rhs : forall fnum fd r i cn cd,
 simplex_rat_mul_flag fnum fd (Znth r cn 0) (Znth r cd 1)=0 ->
 simplex_pivot_addmul fnum fd r i (1,(cn,cd))=(0,(cn,cd)).
Proof. intros. unfold simplex_pivot_addmul. rewrite H. reflexivity. Qed.
Lemma addmul_reject_add__failure_rhs : forall fnum fd r i cn cd p q,
 simplex_rat_mul_flag fnum fd (Znth r cn 0) (Znth r cd 1)=1 ->
 simplex_rat_mul_result fnum fd (Znth r cn 0) (Znth r cd 1) p q ->
 simplex_rat_add_flag (Znth i cn 0) (Znth i cd 1) p q=0 ->
 simplex_pivot_addmul fnum fd r i (1,(cn,cd))=(0,(cn,cd)).
Proof.
 intros. unfold simplex_rat_mul_result, simplex_rat_reduce_result in H0. destruct H0 as [-> ->].
 unfold simplex_pivot_addmul. rewrite H,H1. reflexivity.
Qed.
Lemma filter_id__failure_rhs : forall {A} (p:A->bool) l, (forall x,In x l -> p x=true) -> filter p l=l.
Proof. intros A p l; induction l as [|a l IH]; intros H; simpl;auto. rewrite(H a (or_introl eq_refl)),IH;auto. intros;apply H;right;auto. Qed.
Lemma filter_merge__failure_rhs : forall (l:list Z) (f:Z->Assertion) k,
 NoDup l -> In k l ->
 f k ** iter_sepcon(map f (filter (fun x=>negb(Z.eqb x k)) l)) |-- iter_sepcon(map f l).
Proof.
 induction l as [|a l IH]; intros f k Hnd Hin; [contradiction|].
 inversion Hnd as [|? ? Hnot Htail]; subst. simpl in Hin.
 destruct(Z.eq_dec a k) as [->|Hne].
 - simpl. rewrite Z.eqb_refl. simpl.
   assert(HF:filter(fun x=>negb(Z.eqb x k))l=l).
   { apply filter_id__failure_rhs. intros x Hx. destruct(Z.eqb x k) eqn:E;[apply Z.eqb_eq in E;subst;contradiction|reflexivity]. }
   rewrite HF,logic_equiv_iter_sepcon_cons. reflexivity.
 - simpl. assert(NE:(a =? k)=false) by (apply Z.eqb_neq;exact Hne). rewrite NE. simpl. rewrite !logic_equiv_iter_sepcon_cons.
   sep_apply(IH f k Htail ltac:(destruct Hin;[contradiction|assumption])).
   cancel. 
Qed.
Lemma map_nodup__failure_rhs : forall (l:list Z) (f:Z->Z), NoDup l -> (forall x y,In x l -> In y l -> f x=f y -> x=y) -> NoDup(map f l).
Proof. intros l;induction l as [|a l IH];intros f Hnd Hf;simpl;constructor.
 - inversion Hnd;subst. intro H. apply in_map_iff in H. destruct H as [x [E Hx]]. assert(x=a) by (apply Hf; simpl;auto). subst;contradiction.
 - apply IH. inversion Hnd;auto. intros;apply Hf;simpl;auto.
Qed.
Lemma rows_nodup__failure_rhs : forall l v, NoDup l -> 0<=v<=24 -> NoDup(flat_map(fun i=>map(fun j=>16+i*24+j)(Zrange 0 v))l).
Proof. intros l;induction l as [|a l IH];intros v Hnd Hv;simpl;[constructor|]. inversion Hnd;subst. apply NoDup_app.
 - apply map_nodup__failure_rhs;[apply NoDup_Zrange|]. intros;lia.
 - apply IH;auto.
 - intros k Hk Hother. apply in_map_iff in Hk. destruct Hk as [j [<- Hj]]. apply In_Zrange in Hj.
   apply in_flat_map in Hother. destruct Hother as [i [Hi Hki]]. apply in_map_iff in Hki. destruct Hki as [t [E Ht]]. apply In_Zrange in Ht.
   change(16+i*24+t=16+a*24+j) in E. assert(i=a) by (destruct(Z.lt_trichotomy i a) as [K|[K|K]];lia). subst;contradiction.
Qed.
Lemma slots_nodup__failure_rhs : forall m v, 0<=m<=16 -> 0<=v<=24 -> NoDup(simplex_pivot_slots m v).
Proof. intros m v Hm Hv. unfold simplex_pivot_slots. apply NoDup_app.
 - apply NoDup_Zrange.
 - apply rows_nodup__failure_rhs;[apply NoDup_Zrange|auto].
 - intros k Hk Hother. apply In_Zrange in Hk. apply in_flat_map in Hother. destruct Hother as [i [Hi Hki]]. apply In_Zrange in Hi. apply in_map_iff in Hki. destruct Hki as [j [E Hj]]. apply In_Zrange in Hj. nia.
Qed.
Lemma dual_merge__failure_rhs : forall l (f:Z->Assertion) a b,
 NoDup l -> In a l -> In b l -> a<>b ->
 f a ** f b ** iter_sepcon(map f(filter(fun k=>negb(Z.eqb k a||Z.eqb k b))l)) |-- iter_sepcon(map f l).
Proof.
 intros l f a b Hnd Ha Hb Hne.
 assert(E:filter(fun k=>negb(Z.eqb k a||Z.eqb k b))l=filter(fun k=>negb(Z.eqb k b))(filter(fun k=>negb(Z.eqb k a))l)).
 { clear Hnd Ha Hb. induction l as [|k l IH];simpl;auto. destruct(Z.eqb k a) eqn:KA;destruct(Z.eqb k b) eqn:KB;simpl;rewrite ?KB,IH;reflexivity. }
 rewrite E. sep_apply_r_atomic(filter_merge__failure_rhs l f a Hnd Ha).
 sep_apply_r_atomic(filter_merge__failure_rhs (filter(fun k=>negb(Z.eqb k a))l) f b (NoDup_filter _ Hnd) ltac:(apply filter_In;split;[exact Hb|];destruct(Z.eqb b a)eqn:K;[apply Z.eqb_eq in K;lia|reflexivity])).
 sepcon_right_assoc. repeat multimatch goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
Qed.
Lemma rhs_cell__failure_rhs : forall s k n d, 0<=k<16 -> simplex_pivot_memory_cell s k n d = simplex_scan_rat_memory s "rhs" k true n d.
Proof. intros. unfold simplex_pivot_memory_cell. assert(E:(k<?16)=true) by(apply Z.ltb_lt;lia). rewrite E. reflexivity. Qed.
Lemma rhs_memory_merge__failure_rhs : forall s m v cn cd i r,
 0<=m<=16 -> 0<=v<=24 -> 0<=i<m -> 0<=r<m -> i<>r ->
 simplex_pivot_memory_cell s i (Znth i cn 0)(Znth i cd 1) **
 simplex_pivot_memory_cell s r (Znth r cn 0)(Znth r cd 1) **
 simplex_pivot_except s m v cn cd i r |-- simplex_pivot_memory s m v cn cd.
Proof. intros. unfold simplex_pivot_except,simplex_pivot_memory. apply(dual_merge__failure_rhs (simplex_pivot_slots m v) (fun k=>simplex_pivot_memory_cell s k (Znth k cn 0)(Znth k cd 1)) i r);auto using simplex_pivot_rhs_active,slots_nodup__failure_rhs. Qed.
Lemma factor_current__failure_rhs : forall n d v r e b i fnm fd cn cd,
 simplex_pivot_factor n d v r e b i fnm fd -> simplex_pivot_rows_progress n d v r e b i cn cd ->
 fnm=Znth(16+i*24+e)cn 0 /\ fd=Znth(16+i*24+e)cd 1.
Proof. unfold simplex_pivot_factor,simplex_pivot_rows_progress. intros n d v r e b i fnm fd cn cd [a [c [HP [HF HD]]]] HQ. rewrite HQ in HP. inversion HP;subst;auto. Qed.
Lemma app_nd__failure_pivot {A:Type} (xs ys:list A) :
 NoDup xs -> NoDup ys -> (forall x,In x xs -> ~In x ys) -> NoDup(xs++ys).
Proof. intros H. induction H; intros HY HD; simpl;auto. constructor.
 intro Hbad. apply in_app_or in Hbad. destruct Hbad;[contradiction|eapply HD;eauto;left;reflexivity].
 apply IHNoDup;auto. intros;apply HD;right;auto. Qed.
Lemma map_nd__failure_pivot {A B:Type} (f:A->B) xs :
 NoDup xs -> (forall x y,In x xs -> In y xs -> f x=f y -> x=y) -> NoDup(map f xs).
Proof. intros H;induction H;intro HI;simpl;constructor;auto.
 intro HB; apply in_map_iff in HB;destruct HB as [y [HE HY]].
 assert(x=y) by (apply HI;auto;[left;auto|right;auto]). subst;contradiction.
 apply IHNoDup. intros;apply HI;auto;right;auto. Qed.
Lemma flat_nd__failure_pivot (f:Z->list Z) xs : NoDup xs ->
 (forall x,In x xs -> NoDup(f x)) ->
 (forall x y k,In x xs -> In y xs -> In k(f x) -> In k(f y) -> x=y) -> NoDup(flat_map f xs).
Proof. intros H;induction H;intros HF HD;simpl;[constructor|].
 apply app_nd__failure_pivot.
 apply HF;left;auto.
 apply IHNoDup;[intros;apply HF;right;auto|intros; eapply HD;eauto;right;auto].
 intros k HK HB;apply in_flat_map in HB;destruct HB as [y [HY HKY]].
 assert(x=y) by(eapply HD;eauto;[left;auto|right;auto]). subst;contradiction. Qed.
Lemma slots_nd__failure_pivot m v : 0<=m<=16 -> 0<=v<=24 -> NoDup(simplex_pivot_slots m v).
Proof. intros HM HV. unfold simplex_pivot_slots. apply app_nd__failure_pivot.
 apply NoDup_Zrange.
 apply flat_nd__failure_pivot;[apply NoDup_Zrange| |].
 intros i HI. apply map_nd__failure_pivot;[apply NoDup_Zrange|]. intros;lia.
 intros i j k HI HJ HK HL. apply in_map_iff in HK;apply in_map_iff in HL.
 destruct HK as [a [EA HA]];destruct HL as [b [EB HB]].
 apply In_Zrange in HA;apply In_Zrange in HB. lia.
 intros k HK HL. apply In_Zrange in HK. apply in_flat_map in HL;destruct HL as [i [HI HL]].
 apply in_map_iff in HL;destruct HL as [j [E HJ]]. apply In_Zrange in HI;apply In_Zrange in HJ. nia. Qed.
Lemma filter_absent__failure_pivot (xs:list Z) k : ~In k xs ->
 filter(fun x=>negb(Z.eqb x k || Z.eqb x k)) xs=xs.
Proof. induction xs;intros H;simpl;auto. assert(E:Z.eqb a k=false) by(apply Z.eqb_neq;intro;subst;apply H;left;auto).
 rewrite E; simpl; f_equal;apply IHxs;intro;apply H;right;auto. Qed.
Lemma iter_merge__failure_pivot (F:Z->Assertion) xs k : NoDup xs -> In k xs ->
 F k ** iter_sepcon(map F(filter(fun x=>negb(Z.eqb x k || Z.eqb x k)) xs)) |-- iter_sepcon(map F xs).
Proof. intros H;induction H as [|x xs Hnot Hnd IH];intro HK;[contradiction|]. simpl in HK. destruct(Z.eq_dec x k) as [->|NE].
 - simpl. rewrite Z.eqb_refl; simpl. rewrite (filter_absent__failure_pivot xs k Hnot). rewrite logic_equiv_iter_sepcon_cons. reflexivity.
 - assert(E:Z.eqb x k=false) by(apply Z.eqb_neq;auto). simpl;rewrite E;simpl. rewrite !logic_equiv_iter_sepcon_cons.
   destruct HK as [HB|HK];[contradiction|]. sepcon_right_assoc.
   sep_apply_r_atomic (IH HK). cancel (F x). reflexivity. Qed.
Lemma memory_merge__failure_pivot s m v n d k : 0<=m<=16 -> 0<=v<=24 -> In k(simplex_pivot_slots m v) ->
 simplex_pivot_memory_cell s k (Znth k n 0)(Znth k d 1) ** simplex_pivot_except s m v n d k k |-- simplex_pivot_memory s m v n d.
Proof. intros. unfold simplex_pivot_except,simplex_pivot_memory. apply (iter_merge__failure_pivot (fun z=>simplex_pivot_memory_cell s z (Znth z n 0)(Znth z d 1)) (simplex_pivot_slots m v) k);auto using slots_nd__failure_pivot. Qed.
Lemma matrix_native__failure_pivot s i j n d : 0<=i -> 0<=j<24 ->
 simplex_pivot_memory_cell s (16+i*24+j) n d =
((&((((&((s)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> n) **
((&((((&((s)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> d).
Proof. intros. unfold simplex_pivot_memory_cell. assert(EB:Z.ltb (16+i*24+j) 16=false) by(apply Z.ltb_ge;lia). rewrite EB.
 replace(16+i*24+j-16) with(j+i*24) by ring.
 rewrite Z.div_add,Z.mod_add by lia. rewrite Z.div_small,Z.mod_small by lia. rewrite Z.add_0_l. replace(i*(sizeof("SxRat")*24)) with(i*(24*sizeof("SxRat"))) by ring. reflexivity. Qed.
Lemma rhs_native__failure_pivot s i n d : 0<=i<16 ->
 simplex_pivot_memory_cell s i n d =
((&(((&((s)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> n) **
((&(((&((s)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> d).
Proof. intros. unfold simplex_pivot_memory_cell. assert(EB:Z.ltb i 16=true) by(apply Z.ltb_lt;lia). rewrite EB. unfold simplex_scan_rat_memory. csimpl. reflexivity. Qed.
Lemma range_split__failure_pivot lo hi : 0<=lo<=hi -> Zrange 0 hi=List.app (Zrange 0 lo) (Zrange lo hi).
Proof. intro H. unfold Zrange. replace(hi-0) with ((lo-0)+(hi-lo)) by lia.
 rewrite Z2Nat.inj_add by lia. rewrite Zrange_aux_app. rewrite Z2Nat.id by lia.
 replace(0+(lo-0)) with lo by lia. reflexivity. Qed.
Lemma row_suffix__failure_pivot pn pd r e lo hi s n d : 0<=lo<=hi ->
 simplex_pivot_row_prefix pn pd r e lo s=(0,(n,d)) ->
 simplex_pivot_row_prefix pn pd r e hi s=(0,(n,d)).
Proof. intros H E. unfold simplex_pivot_row_prefix in *. rewrite (range_split__failure_pivot lo hi) by lia.
 rewrite fold_left_app,E. apply simplex_pivot_fold_fixed. intros j;unfold simplex_pivot_row_column;destruct(Z.eqb j e);reflexivity. Qed.
Lemma fail_recip__failure_pivot n d m v r e b cn cd :
 simplex_pivot_row_progress n d r e v cn cd ->
 simplex_rat_div_flag 1 1 (Znth(16+r*24+e)n 0)(Znth(16+r*24+e)d 1)=0 ->
 simplex_pivot_result n d m v r e b 0 cn cd.
Proof. intros HP HF. unfold simplex_pivot_result,simplex_pivot_compute.
 change(simplex_pivot_rows_prefix r e v m (simplex_pivot_zero(16+r*24+e)
 (simplex_pivot_recip (Znth(16+r*24+e)n 0)(Znth(16+r*24+e)d 1)(16+r*24+b)
 (simplex_pivot_row_prefix (Znth(16+r*24+e)n 0)(Znth(16+r*24+e)d 1) r e v (simplex_pivot_start n d r e))))=(0,(cn,cd))).
 unfold simplex_pivot_row_progress in HP. rewrite HP. unfold simplex_pivot_recip. rewrite HF. simpl. apply simplex_pivot_rows_failed. Qed.
Lemma fail_column__failure_pivot n d m v r e b j cn cd : 0<=j<v -> j<>e ->
 simplex_pivot_row_progress n d r e j cn cd ->
 simplex_rat_div_flag(Znth(16+r*24+j)cn 0)(Znth(16+r*24+j)cd 1)(Znth(16+r*24+e)n 0)(Znth(16+r*24+e)d 1)=0 ->
 simplex_pivot_result n d m v r e b 0 cn cd.
Proof. intros HJ HNE HP HF.
 assert(HS:simplex_pivot_row_prefix (Znth(16+r*24+e)n 0)(Znth(16+r*24+e)d 1) r e (j+1) (simplex_pivot_start n d r e)=(0,(cn,cd))).
 { rewrite simplex_pivot_row_step by lia. unfold simplex_pivot_row_progress in HP. rewrite HP.
 unfold simplex_pivot_row_column. assert(EB:Z.eqb j e=false) by(apply Z.eqb_neq;auto). rewrite EB. unfold simplex_pivot_div. rewrite HF. reflexivity. }
 pose proof(row_suffix__failure_pivot (Znth(16+r*24+e)n 0)(Znth(16+r*24+e)d 1) r e (j+1) v (simplex_pivot_start n d r e) cn cd ltac:(lia) HS) as HE.
 unfold simplex_pivot_result,simplex_pivot_compute. change(simplex_pivot_rows_prefix r e v m(simplex_pivot_zero(16+r*24+e)(simplex_pivot_recip (Znth(16+r*24+e)n 0)(Znth(16+r*24+e)d 1) (16+r*24+b) (simplex_pivot_row_prefix (Znth(16+r*24+e)n 0)(Znth(16+r*24+e)d 1) r e v (simplex_pivot_start n d r e))))=(0,(cn,cd))).
 rewrite HE. simpl. apply simplex_pivot_rows_failed. Qed.
Lemma fail_rhs__failure_pivot n d m v r e b :
 simplex_rat_div_flag(Znth r n 0)(Znth r d 1)(Znth(16+r*24+e)n 0)(Znth(16+r*24+e)d 1)=0 ->
 simplex_pivot_result n d m v r e b 0 n d.
Proof. intro HF. unfold simplex_pivot_result,simplex_pivot_compute,simplex_pivot_div. rewrite HF. simpl.
 rewrite simplex_pivot_row_failed. simpl. apply simplex_pivot_rows_failed. Qed.
