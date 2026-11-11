From Coq Require Import ZArith List Lia String Bool.
From SimpleC.EE.Applications_human.simplex_recompute Require Export simplex_recompute_lib.
Import ListNotations naive_C_Rules.
Local Open Scope Z_scope.
(* Initialization's public values are the integer RHS in the auxiliary slots.
   This is an index formula, independent of the loop that constructs the table. *)
Definition simplex_init_value_at (rn:list Z) (n done j:Z) : Z :=
 if (n <=? j) && (j <? n+done) then Znth (j-n) rn 0 else 0.
Definition simplex_init_basic (n rows:Z) : list Z := Zrange n (n+rows).
Definition simplex_init_flags (n vars:Z) : list Z := map (fun j => if j <? n then 0 else 1) (Zrange 0 vars).
Definition simplex_init_rhs (a:list Z) (rows:Z) : list Z := map (fun i => Znth (i*9) a 0) (Zrange 0 rows).
Definition simplex_init_coeff (a:list Z) (n i j:Z) : Z := if j <? n then Znth (i*9+j+1) a 0 else 0.
(* Exact full-call refinement. basic must contain the distinct auxiliary
   indices n+i; matrix/RHS denominators are one. No old state is consulted. *)
Theorem simplex_initialize_recompute_exact : forall ib an ad rn rd basic vn vd rows n cols,
 0<=rows -> 0<=n -> n+rows<=cols -> Zlength vn=cols -> Zlength vd=cols ->
 (forall j, 0<=j<cols -> Znth j vn 0=0 /\ Znth j vd 0=1) ->
 (forall j, 0<=j<cols -> Znth j ib 0=0 -> j<n) ->
 (forall i, 0<=i<rows -> Znth i basic 0=n+i /\ Znth (n+i) ib 0<>0 /\ -2147483647<=Znth i rn 0<=2147483647 /\ Znth i rd 0=1 /\ forall j, 0<=j<cols -> -2147483647<=Znth(i*24+j) an 0<=2147483647 /\ Znth(i*24+j) ad 0=1) ->
 exists on od, simplex_recompute_compute ib an ad rn rd basic vn vd rows cols=(1,(on,od)) /\ Zlength on=cols /\ Zlength od=cols /\ forall j, 0<=j<cols -> Znth j on 0=simplex_init_value_at rn n rows j /\ Znth j od 0=1.
Proof.
 intros ib an ad rn rd basic vn vd rows n cols HR HN HC HVN HVD HZERO HIB.
 revert rows HR HC. refine (natlike_ind (fun rows => _) _ _).
 - intros HC HB. exists vn,vd. split; [reflexivity|]. split; [exact HVN|]. split; [exact HVD|].
   intros j HJ. destruct (HZERO j HJ) as [HA HD]. rewrite HA,HD. unfold simplex_init_value_at.
   destruct (n <=? j) eqn:E; simpl; [apply Z.leb_le in E|auto].
   assert (F : (j <? n+0)=false) by (apply Z.ltb_ge; lia). rewrite F. auto.
 - intros k HK IH HC HB.
   destruct (IH ltac:(lia) ltac:(intros; apply HB; lia)) as [cn [cd [HE [HLN [HLD HP]]]]].
   destruct (HB k ltac:(lia)) as [HBA [HBI [HRN [HRD HA]]]].
   assert (HS : simplex_recompute_row ib an ad cn cd rn rd k cols=Some(Znth k rn 0,1)).
   { apply simplex_recompute_row_integer_zero; try lia; auto.
     intros j HJ. destruct (HA j HJ) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
     intros EJ. destruct (HP j HJ) as [EP ED]. rewrite EP,ED. split; [|reflexivity].
     unfold simplex_init_value_at. apply HIB in EJ; [|exact HJ]. assert (F : (n <=? j)=false) by (apply Z.leb_gt; lia). rewrite F. reflexivity. }
   exists (replace_Znth (n+k) (Znth k rn 0) cn),(replace_Znth (n+k) 1 cd).
   split.
   + replace (Z.succ k) with (k+1) by lia. rewrite simplex_recompute_compute_step by lia.
     rewrite HE. unfold simplex_recompute_commit. rewrite HS,HBA. reflexivity.
   + rewrite !Zlength_replace_Znth. split; [exact HLN|]. split; [exact HLD|].
     intros j HJ. destruct (Z.eq_dec (n+k) j) as [E|E].
     * subst j. rewrite !Znth_replace_Znth_Same by lia. unfold simplex_init_value_at.
       assert (F : (n <=? n+k)=true) by (apply Z.leb_le; lia). rewrite F.
       assert (G : (n+k <? n+Z.succ k)=true) by (apply Z.ltb_lt; lia). rewrite G. simpl. replace (n+k-n) with k by lia. auto.
     * rewrite !Znth_replace_Znth_Diff by lia. destruct (HP j HJ) as [EP ED]. rewrite EP,ED.
       unfold simplex_init_value_at. destruct (n <=? j) eqn:EN; simpl; [|auto].
       destruct (j <? n+k) eqn:EK; destruct (j <? n+Z.succ k) eqn:ES; simpl; try auto;
       apply Z.ltb_lt in EK || apply Z.ltb_ge in EK;
       apply Z.ltb_lt in ES || apply Z.ltb_ge in ES; lia.
Qed.

(* Active input ownership follows the declared nine-int row stride; padding
   columns are logical only and require no initialized C cells. *)
Local Open Scope sac.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Definition simplex_init_input_cell (c:Z) (a:list Z) (i j:Z) : Assertion :=
 (c+i*(sizeof(INT)*9)+j*sizeof(INT)) # Int |-> Znth(i*9+j) a 0.
Definition simplex_init_input (c:Z) (a:list Z) (rows n:Z) : Assertion :=
 iter_sepcon(map (fun i=>iter_sepcon(map (simplex_init_input_cell c a i) (Zrange 0 (n+1)))) (Zrange 0 rows)).
Definition simplex_init_input_except (c:Z) (a:list Z) (rows n i j:Z) : Assertion :=
 iter_sepcon(remove_Znth i (map (fun k=>iter_sepcon(map (simplex_init_input_cell c a k) (Zrange 0 (n+1)))) (Zrange 0 rows))) **
 iter_sepcon(remove_Znth j (map (simplex_init_input_cell c a i) (Zrange 0 (n+1)))).
(* Only overwritten variable fields are included. Untouched members/array
   tails remain frame resources with their original initialization state. *)
Definition simplex_init_var (s n upto done vars:Z) (rn:list Z) (finished j:Z) : Assertion :=
 if j <? upto then
 (&((s)#"SxState"->ₛ"is_basic")+j*sizeof(INT)) # Int |-> (if ((n<=?j)&&(j<?n+done))%bool then 1 else 0) **
 (&((s)#"SxState"->ₛ"has_lower")+j*sizeof(INT)) # Int |-> 0 **
 (&((s)#"SxState"->ₛ"has_upper")+j*sizeof(INT)) # Int |-> (if ((n<=?j)&&(j<?n+done))%bool then 1 else 0) **
 simplex_scan_rat_memory s "lower" j true 0 1 ** simplex_scan_rat_memory s "upper" j true 0 1 **
 simplex_scan_rat_memory s "value" j true (if finished =? 1 then simplex_init_value_at rn n done j else 0) 1
 else
 (&((s)#"SxState"->ₛ"is_basic")+j*sizeof(INT)) # Int |->_ **
 (&((s)#"SxState"->ₛ"has_lower")+j*sizeof(INT)) # Int |->_ **
 (&((s)#"SxState"->ₛ"has_upper")+j*sizeof(INT)) # Int |->_ **
 simplex_scan_rat_memory s "lower" j false 0 1 ** simplex_scan_rat_memory s "upper" j false 0 1 **
 simplex_scan_rat_memory s "value" j false 0 1.
Definition simplex_init_vars (s n upto done vars:Z) (rn:list Z) (finished:Z) : Assertion :=
 iter_sepcon(map (simplex_init_var s n upto done vars rn finished) (Zrange 0 vars)).
Definition simplex_init_vars_except (s n upto done vars:Z) (rn:list Z) (finished j:Z) : Assertion :=
 iter_sepcon(remove_Znth j (map (simplex_init_var s n upto done vars rn finished) (Zrange 0 vars))).
Definition simplex_init_a_undef (s i j:Z) : Assertion :=
 (&(((&((s)#"SxState"->ₛ"a")+i*(sizeof("SxRat")*24)+j*sizeof("SxRat")))#"SxRat"->ₛ"num")) # Int |->_ **
 (&(((&((s)#"SxState"->ₛ"a")+i*(sizeof("SxRat")*24)+j*sizeof("SxRat")))#"SxRat"->ₛ"den")) # Int |->_.
Definition simplex_init_a_cell (s:Z) (a:list Z) (n i j:Z) : Assertion :=
 (&(((&((s)#"SxState"->ₛ"a")+i*(sizeof("SxRat")*24)+j*sizeof("SxRat")))#"SxRat"->ₛ"num")) # Int |-> simplex_init_coeff a n i j **
 (&(((&((s)#"SxState"->ₛ"a")+i*(sizeof("SxRat")*24)+j*sizeof("SxRat")))#"SxRat"->ₛ"den")) # Int |-> 1.
Definition simplex_init_a_row (s:Z) (a:list Z) (n i upto vars:Z) : Assertion :=
 iter_sepcon(map (fun j=>if j <? upto then simplex_init_a_cell s a n i j else simplex_init_a_undef s i j) (Zrange 0 vars)).
Definition simplex_init_a_row_except (s:Z) (a:list Z) (n i upto vars j:Z) : Assertion :=
 iter_sepcon(remove_Znth j (map (fun k=>if k <? upto then simplex_init_a_cell s a n i k else simplex_init_a_undef s i k) (Zrange 0 vars))).
Definition simplex_init_row (s:Z) (a:list Z) (n done vars i:Z) : Assertion :=
 if i <? done then
 (&((s)#"SxState"->ₛ"basic")+i*sizeof(INT)) # Int |-> (n+i) **
 simplex_scan_rat_memory s "rhs" i true (Znth(i*9) a 0) 1 ** simplex_init_a_row s a n i vars vars
 else
 (&((s)#"SxState"->ₛ"basic")+i*sizeof(INT)) # Int |->_ **
 simplex_scan_rat_memory s "rhs" i false 0 1 ** simplex_init_a_row s a n i 0 vars.
Definition simplex_init_rows (s:Z) (a:list Z) (n done rows vars:Z) : Assertion :=
 iter_sepcon(map (simplex_init_row s a n done vars) (Zrange 0 rows)).
Definition simplex_init_rows_except (s:Z) (a:list Z) (n done rows vars i:Z) : Assertion :=
 iter_sepcon(remove_Znth i (map (simplex_init_row s a n done vars) (Zrange 0 rows))).
Lemma simplex_init_input_empty : forall c a n, simplex_init_input c a 0 n = emp.
Proof. reflexivity. Qed.

Local Open Scope Z_scope.
Definition simplex_init_an (a:list Z) (rows n:Z) : list Z := map (fun k=>simplex_init_coeff a n (k/24) (k mod 24)) (Zrange 0 (rows*24)).
Definition simplex_init_zeroes (vars:Z) : list Z := map (fun _=>0) (Zrange 0 vars).
Definition simplex_init_ones (vars:Z) : list Z := map (fun _=>1) (Zrange 0 vars).
Definition simplex_init_values (a:list Z) (rows n:Z) : list Z := map (simplex_init_value_at (simplex_init_rhs a rows) n rows) (Zrange 0 (n+rows)).

(* Opaque-to-frontend spelling of an unreachable cut; every use must be proved from path contradictions. *)
Definition simplex_init_unreachable (rows cols:Z) : Prop := False.

Local Open Scope sac.
Local Open Scope Z_scope.
Definition simplex_init_bounds (s n rows vars:Z) : Assertion :=
 iter_sepcon(map (fun j=>
 (&((s)#"SxState"->ₛ"has_lower")+j*sizeof(INT)) # Int |-> 0 **
 (&((s)#"SxState"->ₛ"has_upper")+j*sizeof(INT)) # Int |-> (if j <? n then 0 else 1) **
 simplex_scan_rat_memory s "lower" j true 0 1 ** simplex_scan_rat_memory s "upper" j true 0 1) (Zrange 0 vars)).

(* Frontend-deferred return equality: exceptional symbolic paths may be mathematically impossible through quantified premises. *)
Definition simplex_init_return (q expected:Z) : Prop := q=expected.
Lemma simplex_init_return_exact : forall q e, simplex_init_return q e <-> q=e. Proof. reflexivity. Qed.

Local Open Scope Z_scope.
Lemma simplex_init_reject_scan_unreachable : forall a rows n i,
  i>=rows ->
  (exists x y, 0<=x<rows /\ 0<=y<=n /\ Znth(x*9+y) a 0 = -2147483648) ->
  (forall x y, 0<=x<rows -> 0<=y<=n -> x<i -> Znth(x*9+y) a 0 <> -2147483648) ->
  simplex_init_unreachable rows n.
Proof. intros a rows n i HI [x [y [HX [HY HE]]]] HSCAN.
 unfold simplex_init_unreachable. apply (HSCAN x y HX HY); lia. Qed.
Lemma simplex_init_dimensions_unreachable : forall rows n,
 (rows<0 \/ 16<rows \/ n<0 \/ 8<n) ->
 0<=rows<=16 -> 0<=n<=8 -> simplex_init_unreachable rows n.
Proof. unfold simplex_init_unreachable. intros. lia. Qed.


Lemma range_update__zero_rows : forall (f g:Z->Assertion) v j,
 0<=j<v -> (forall k, 0<=k<v -> k<>j -> f k=g k) ->
 g j ** iter_sepcon(remove_Znth j (map f (Zrange 0 v))) |-- iter_sepcon(map g (Zrange 0 v)).
Proof.
 intros f g v j HJ HE.
 pose proof (iter_sepcon_merge_remove_Znth j (map f (Zrange 0 v)) (g j)) as HM.
 assert (E: replace_Znth j (g j) (map f (Zrange 0 v))=map g (Zrange 0 v)).
 { apply (proj2 (list_eq_ext _ _ emp)). rewrite Zlength_replace_Znth, !Zlength_map. split;[reflexivity|].
 intros k HK. rewrite simplex_scan_range_length in HK by lia.
 destruct (Z.eq_dec j k) as [D|D].
 - subst k. rewrite Znth_replace_Znth_Same by (rewrite Zlength_map,simplex_scan_range_length;lia).
   rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length;lia). rewrite simplex_scan_range_nth by lia. reflexivity.
 - rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_map,?simplex_scan_range_length;lia).
   rewrite !(Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length;lia).
   rewrite !simplex_scan_range_nth by lia. apply HE;lia. }
 rewrite <- E. apply HM. rewrite Zlength_map,simplex_scan_range_length;lia.
Qed.
Lemma zero_flag__zero_rows : forall n k, ((n<=?k)&&(k<?n+0))%bool=false.
Proof. intros. destruct (n<=?k) eqn:E; simpl;auto. apply Z.leb_le in E. apply Z.ltb_ge;lia. Qed.
Lemma vars_focus__zero_rows : forall s n j,
 0<=j<n -> simplex_init_vars s n j 0 n nil 0 |--
 simplex_init_var s n j 0 n nil 0 j ** simplex_init_vars_except s n j 0 n nil 0 j.
Proof.
 intros s n j H. unfold simplex_init_vars,simplex_init_vars_except.
 pose proof (iter_sepcon_split_remove_Znth j (map (simplex_init_var s n j 0 n nil 0) (Zrange 0 n)) emp) as HS.
 rewrite (Znth_map _ _ _ 0 emp) in HS by (rewrite simplex_scan_range_length;lia).
 rewrite simplex_scan_range_nth in HS by lia. apply HS. rewrite Zlength_map,simplex_scan_range_length;lia.
Qed.
Lemma vars_step__zero_rows : forall s n j,
 0<=j<n -> simplex_init_var s n (j+1) 0 n nil 0 j **
 simplex_init_vars_except s n j 0 n nil 0 j |-- simplex_init_vars s n (j+1) 0 n nil 0.
Proof.
 intros s n j H. unfold simplex_init_vars_except,simplex_init_vars.
 apply range_update__zero_rows;auto. intros k HK HD. unfold simplex_init_var.
 destruct (k<?j) eqn:E; destruct (k<?j+1) eqn:F; auto;
 apply Z.ltb_lt in E || apply Z.ltb_ge in E; apply Z.ltb_lt in F || apply Z.ltb_ge in F;lia.
Qed.
Lemma vars_finish__zero_rows : forall s n,
 simplex_init_vars s n n 0 n nil 0 = simplex_init_vars s n n 0 n (simplex_init_rhs nil 0) 1.
Proof.
 intros. unfold simplex_init_vars. f_equal. apply map_ext. intros k.
 unfold simplex_init_var. rewrite zero_flag__zero_rows. destruct (k<?n);auto.
 unfold simplex_init_value_at. rewrite zero_flag__zero_rows. reflexivity.
Qed.
Lemma range_nth__scan_reject : forall (f:Z->Assertion) n i,
 0<=i<n -> Znth i (map f (Zrange 0 n)) emp=f i.
Proof. intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity. Qed.
Lemma range_focus__scan_reject : forall (f:Z->Assertion) n i,
 0<=i<n -> iter_sepcon(map f (Zrange 0 n)) |--
 f i ** iter_sepcon(remove_Znth i (map f (Zrange 0 n))).
Proof. intros. pose proof(iter_sepcon_split_remove_Znth i (map f (Zrange 0 n)) emp) as Hs.
 rewrite range_nth__scan_reject in Hs by auto. apply Hs. rewrite Zlength_map,simplex_scan_range_length;lia. Qed.
Lemma range_merge__scan_reject : forall (f:Z->Assertion) n i,
 0<=i<n -> f i ** iter_sepcon(remove_Znth i (map f (Zrange 0 n))) |-- iter_sepcon(map f (Zrange 0 n)).
Proof. intros. pose proof(iter_sepcon_merge_remove_Znth i (map f (Zrange 0 n)) (f i)) as Hs.
 rewrite <- (range_nth__scan_reject f n i H) in Hs. rewrite replace_Znth_Znth in Hs.
 rewrite range_nth__scan_reject in Hs by auto. apply Hs. rewrite Zlength_map,simplex_scan_range_length;lia. Qed.
Lemma input_focus__scan_reject : forall c a m n i j,
 0<=i<m -> 0<=j<=n -> simplex_init_input c a m n |--
 simplex_init_input_except c a m n i j ** simplex_init_input_cell c a i j.
Proof. intros. unfold simplex_init_input,simplex_init_input_except.
 sep_apply_l_atomic (range_focus__scan_reject (fun k=>iter_sepcon(map (simplex_init_input_cell c a k) (Zrange 0 (n+1)))) m i H).
 sep_apply_l_atomic (range_focus__scan_reject (simplex_init_input_cell c a i) (n+1) j ltac:(lia)).
 sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity. Qed.
Lemma input_merge__scan_reject : forall c a m n i j,
 0<=i<m -> 0<=j<=n -> simplex_init_input_except c a m n i j ** simplex_init_input_cell c a i j |-- simplex_init_input c a m n.
Proof. intros. unfold simplex_init_input,simplex_init_input_except. sepcon_right_assoc.
 sep_apply_r_atomic (range_merge__scan_reject (fun k=>iter_sepcon(map (simplex_init_input_cell c a k) (Zrange 0 (n+1)))) m i H).
 sep_apply_r_atomic (range_merge__scan_reject (simplex_init_input_cell c a i) (n+1) j ltac:(lia)). cancel (simplex_init_input_cell c a i j). cancel (iter_sepcon(remove_Znth j (map (simplex_init_input_cell c a i) (Zrange 0 (n+1))))). reflexivity. Qed.
Lemma input_focus__scan_success : forall c a rows n i j,
 0<=i<rows -> 0<=j<n+1 -> simplex_init_input c a rows n |--
 simplex_init_input_cell c a i j ** simplex_init_input_except c a rows n i j.
Proof.
 intros c a rows n i j HI HJ. unfold simplex_init_input, simplex_init_input_except.
 pose proof (iter_sepcon_split_remove_Znth i (map (fun k => iter_sepcon (map (simplex_init_input_cell c a k) (Zrange 0 (n+1)))) (Zrange 0 rows)) emp) as HO.
 rewrite (Znth_map _ _ _ 0 emp) in HO by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth in HO by lia.
 sep_apply_l_atomic (HO ltac:(rewrite Zlength_map, simplex_scan_range_length; lia)).
 pose proof (iter_sepcon_split_remove_Znth j (map (simplex_init_input_cell c a i) (Zrange 0 (n+1))) emp) as HC.
 rewrite (Znth_map _ _ _ 0 emp) in HC by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth in HC by lia.
 sep_apply_l_atomic (HC ltac:(rewrite Zlength_map, simplex_scan_range_length; lia)).
 cancel. reflexivity.
Qed.
Lemma input_merge__scan_success : forall c a rows n i j,
 0<=i<rows -> 0<=j<n+1 ->
 simplex_init_input_except c a rows n i j ** simplex_init_input_cell c a i j |-- simplex_init_input c a rows n.
Proof.
 intros c a rows n i j HI HJ. unfold simplex_init_input, simplex_init_input_except.
 sepcon_right_assoc.
 sep_apply_r_atomic (range_merge__column_success (fun k=>iter_sepcon (map (simplex_init_input_cell c a k) (Zrange 0 (n+1)))) rows i HI).
 sep_apply_r_atomic (range_merge__column_success (simplex_init_input_cell c a i) (n+1) j HJ).
 sepcon_right_assoc.
 cancel (simplex_init_input_cell c a i j).
 cancel (iter_sepcon(remove_Znth j (map (simplex_init_input_cell c a i) (Zrange 0 (n+1))))). reflexivity.
Qed.
Lemma input_bound__scan_success : forall a m n i j,
 Zlength a=m*9 -> 0<=i<m -> 0<=j<=n -> n<=8 ->
 Forall (Z.le (-2147483647)) a -> -2147483647<=Znth (i*9+j) a 0.
Proof.
 intros a m n i j HL HI HJ HN HA.
 apply (forall_nth__entry_focus _ _ _ HA). nia.
Qed.
Lemma range_update__vars_success : forall (f g:Z->Assertion) v j,
 0<=j<v -> (forall k, 0<=k<v -> k<>j -> f k=g k) ->
 g j ** iter_sepcon(remove_Znth j (map f (Zrange 0 v))) |-- iter_sepcon(map g (Zrange 0 v)).
Proof.
 intros f g v j HJ HE.
 pose proof(iter_sepcon_merge_remove_Znth j (map f (Zrange 0 v)) (g j)) as HM.
 assert (HL:Zlength(map f (Zrange 0 v))=v) by (rewrite Zlength_map,simplex_scan_range_length;lia).
 assert (EQ:replace_Znth j (g j) (map f (Zrange 0 v))=map g (Zrange 0 v)).
 { apply (nth_ext _ _ emp emp).
   - assert (HLL:Zlength (replace_Znth j (g j) (map f (Zrange 0 v)))=Zlength(map g (Zrange 0 v))).
     { rewrite Zlength_replace_Znth, !Zlength_map. reflexivity. }
     rewrite !Zlength_correct in HLL. apply Nat2Z.inj. exact HLL.
   - intros k HK.
     assert (HKZ:0<=Z.of_nat k<Zlength(replace_Znth j (g j) (map f (Zrange 0 v)))) by (rewrite Zlength_correct; split; [apply Nat2Z.is_nonneg|apply Nat2Z.inj_lt;exact HK]).
     rewrite Zlength_replace_Znth, HL in HKZ. rename HKZ into HB.
     assert (ET:Znth (Z.of_nat k) (replace_Znth j (g j) (map f (Zrange 0 v))) emp = Znth (Z.of_nat k) (map g (Zrange 0 v)) emp).
     { destruct (Z.eq_dec j (Z.of_nat k)) as [E|E].
       - rewrite <- E. rewrite Znth_replace_Znth_Same by lia.
         rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length;lia).
         rewrite simplex_scan_range_nth by lia. reflexivity.
       - rewrite Znth_replace_Znth_Diff by lia.
         rewrite !(Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length;lia).
         rewrite simplex_scan_range_nth by lia. apply HE;lia. }
     unfold Znth in ET. rewrite Nat2Z.id in ET. exact ET. }
 rewrite <- EQ. apply iter_sepcon_merge_remove_Znth. rewrite HL;exact HJ.
Qed.
Lemma vars_focus__vars_success : forall s n v a j,
 0<=j<v -> simplex_init_vars s n j 0 v a 0 |--
 simplex_init_var s n j 0 v a 0 j ** simplex_init_vars_except s n j 0 v a 0 j.
Proof.
 intros. unfold simplex_init_vars,simplex_init_vars_except.
 pose proof(iter_sepcon_split_remove_Znth j (map (simplex_init_var s n j 0 v a 0) (Zrange 0 v)) emp) as HS.
 rewrite (Znth_map _ _ _ 0 emp) in HS by (rewrite simplex_scan_range_length;lia).
 rewrite simplex_scan_range_nth in HS by lia. apply HS.
 rewrite Zlength_map,simplex_scan_range_length;lia.
Qed.
Lemma zero_flag__vars_success : forall n k,
 ((n<=?k)&&(k<?n+0))%bool=false.
Proof. intros. destruct (n<=?k) eqn:E; simpl;auto. apply Z.leb_le in E. apply Z.ltb_ge;lia. Qed.
Lemma vars_step__vars_success : forall s n v a j,
 0<=j<v ->
 simplex_init_var s n (j+1) 0 v a 0 j ** simplex_init_vars_except s n j 0 v a 0 j |--
 simplex_init_vars s n (j+1) 0 v a 0.
Proof.
 intros. unfold simplex_init_vars,simplex_init_vars_except.
 apply range_update__vars_success;auto. intros k HK HNE.
 unfold simplex_init_var. assert(E:(k<?j)=(k<?j+1)).
 { destruct (k<?j) eqn:F;destruct (k<?j+1) eqn:G;auto;
   apply Z.ltb_lt in F || apply Z.ltb_ge in F;
   apply Z.ltb_lt in G || apply Z.ltb_ge in G;lia. }
 rewrite E. reflexivity.
Qed.
Lemma range_nth__row_setup : forall (f:Z->Assertion) len j,
 0<=j<len -> Znth j (map f (Zrange 0 len)) emp=f j.
Proof. intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length;lia).
 rewrite simplex_scan_range_nth by lia. reflexivity. Qed.
Lemma range_focus__row_setup : forall (f:Z->Assertion) len j,
 0<=j<len -> iter_sepcon(map f (Zrange 0 len)) |--
 f j ** iter_sepcon(remove_Znth j (map f (Zrange 0 len))).
Proof. intros. pose proof(iter_sepcon_split_remove_Znth j (map f (Zrange 0 len)) emp) as Hs.
 rewrite range_nth__row_setup in Hs by auto. apply Hs. rewrite Zlength_map,simplex_scan_range_length;lia. Qed.
Lemma range_merge__row_setup : forall (f:Z->Assertion) len j,
 0<=j<len -> f j ** iter_sepcon(remove_Znth j (map f (Zrange 0 len))) |-- iter_sepcon(map f (Zrange 0 len)).
Proof. intros. pose proof(iter_sepcon_merge_remove_Znth j (map f (Zrange 0 len)) (Znth j (map f (Zrange 0 len)) emp)) as Hm.
 rewrite replace_Znth_Znth in Hm. rewrite range_nth__row_setup in Hm by auto.
 apply Hm. rewrite Zlength_map,simplex_scan_range_length;lia. Qed.
Lemma range_update__row_setup : forall (f g:Z->Assertion) len j,
 0<=j<len -> (forall k,0<=k<len -> k<>j -> f k=g k) ->
 g j ** iter_sepcon(remove_Znth j (map f (Zrange 0 len))) |-- iter_sepcon(map g (Zrange 0 len)).
Proof. intros f g len j HJ HE.
 assert(E:replace_Znth j (g j) (map f (Zrange 0 len))=map g (Zrange 0 len)).
 { apply (proj2(list_eq_ext _ _ emp)). rewrite Zlength_replace_Znth,!Zlength_map. split;[reflexivity|].
 intros k HK. rewrite simplex_scan_range_length in HK by lia. destruct(Z.eq_dec j k).
 - subst. rewrite Znth_replace_Znth_Same by (rewrite Zlength_map,simplex_scan_range_length;lia). rewrite range_nth__row_setup by lia. reflexivity.
 - rewrite Znth_replace_Znth_Diff by (try (rewrite Zlength_map,simplex_scan_range_length);lia).
   rewrite !range_nth__row_setup by lia. apply HE;lia. }
 rewrite <-E. apply iter_sepcon_merge_remove_Znth. rewrite Zlength_map,simplex_scan_range_length;lia. Qed.
Lemma input_focus__row_setup : forall c a rows n i j,
 0<=i<rows -> 0<=j<n+1 -> simplex_init_input c a rows n |--
 simplex_init_input_cell c a i j ** simplex_init_input_except c a rows n i j.
Proof. intros. unfold simplex_init_input,simplex_init_input_except.
 sep_apply_l_atomic (range_focus__row_setup (fun k=>iter_sepcon(map (simplex_init_input_cell c a k) (Zrange 0 (n+1)))) rows i H).
 sep_apply_l_atomic (range_focus__row_setup (simplex_init_input_cell c a i) (n+1) j H0).
 sepcon_right_assoc. cancel (simplex_init_input_cell c a i j).
 cancel (iter_sepcon(remove_Znth j (map (simplex_init_input_cell c a i) (Zrange 0 (n+1))))). reflexivity. Qed.
Lemma input_merge__row_setup : forall c a rows n i j,
 0<=i<rows -> 0<=j<n+1 -> simplex_init_input_cell c a i j ** simplex_init_input_except c a rows n i j |-- simplex_init_input c a rows n.
Proof. intros. unfold simplex_init_input,simplex_init_input_except.
 sep_apply_r_atomic (range_merge__row_setup (fun k=>iter_sepcon(map (simplex_init_input_cell c a k) (Zrange 0 (n+1)))) rows i H).
 sep_apply_r_atomic (range_merge__row_setup (simplex_init_input_cell c a i) (n+1) j H0).
 sepcon_right_assoc. cancel (simplex_init_input_cell c a i j).
 cancel (iter_sepcon(remove_Znth j (map (simplex_init_input_cell c a i) (Zrange 0 (n+1))))). reflexivity. Qed.
Lemma vars_focus__row_setup : forall s n vars a i,
 0<=n -> 0<=i -> n+i<vars -> simplex_init_vars s n vars i vars a 0 |--
 simplex_init_var s n vars i vars a 0 (n+i) ** simplex_init_vars_except s n vars i vars a 0 (n+i).
Proof. intros. unfold simplex_init_vars,simplex_init_vars_except. apply range_focus__row_setup;lia. Qed.
Lemma vars_mark__row_setup : forall s n vars a i,
 0<=n -> 0<=i -> n+i<vars ->
 simplex_init_var s n vars (i+1) vars a 0 (n+i) ** simplex_init_vars_except s n vars i vars a 0 (n+i) |--
 simplex_init_vars s n vars (i+1) vars a 0.
Proof. intros. unfold simplex_init_vars,simplex_init_vars_except. apply range_update__row_setup;[lia|].
 intros k HK HNE. unfold simplex_init_var.
 assert (E:(k <? n+i)=(k <? n+(i+1))) by (destruct(k <? n+i) eqn:E1;destruct(k <? n+(i+1)) eqn:E2;auto;
 apply Z.ltb_lt in E1 || apply Z.ltb_ge in E1; apply Z.ltb_lt in E2 || apply Z.ltb_ge in E2;lia).
 rewrite E. reflexivity. Qed.
Lemma rows_focus__row_setup : forall s a n i rows vars,
 0<=i<rows -> simplex_init_rows s a n i rows vars |--
 simplex_init_row s a n i vars i ** simplex_init_rows_except s a n i rows vars i.
Proof. intros. unfold simplex_init_rows,simplex_init_rows_except. apply range_focus__row_setup;auto. Qed.
Lemma range_nth__matrix_steps : forall (f:Z->Assertion) v j,
 0<=j<v -> Znth j (map f (Zrange 0 v)) emp=f j.
Proof. intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity. Qed.
Lemma range_focus__matrix_steps : forall (f:Z->Assertion) v j,
 0<=j<v -> iter_sepcon(map f (Zrange 0 v)) |--
 f j ** iter_sepcon(remove_Znth j (map f (Zrange 0 v))).
Proof. intros. pose proof (iter_sepcon_split_remove_Znth j (map f (Zrange 0 v)) emp) as Hs.
 rewrite range_nth__matrix_steps in Hs by auto. apply Hs.
 rewrite Zlength_map,simplex_scan_range_length; lia. Qed.
Lemma range_update__matrix_steps : forall (f g:Z->Assertion) v j,
 0<=j<v -> (forall k,0<=k<v -> k<>j -> f k=g k) ->
 g j ** iter_sepcon(remove_Znth j (map f (Zrange 0 v))) |-- iter_sepcon(map g (Zrange 0 v)).
Proof. intros f g v j HJ HE.
 pose proof (iter_sepcon_merge_remove_Znth j (map f (Zrange 0 v)) (g j)) as HM.
 assert (E:replace_Znth j (g j) (map f (Zrange 0 v))=map g (Zrange 0 v)).
 { apply (proj2 (list_eq_ext _ _ emp)). split.
 - rewrite Zlength_replace_Znth,!Zlength_map. reflexivity.
 - intros k HK. rewrite Zlength_replace_Znth,Zlength_map,simplex_scan_range_length in HK by lia.
   destruct (Z.eq_dec j k); subst.
   + rewrite Znth_replace_Znth_Same by (rewrite Zlength_map,simplex_scan_range_length; lia).
     rewrite range_nth__matrix_steps by lia. reflexivity.
   + rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_map, ?simplex_scan_range_length; lia).
     rewrite !range_nth__matrix_steps by lia. apply HE; lia. }
 specialize (HM ltac:(rewrite Zlength_map,simplex_scan_range_length; lia)). exact (eq_ind _ (fun l => g j ** iter_sepcon(remove_Znth j (map f (Zrange 0 v))) |-- iter_sepcon l) HM _ E).
Qed.
Lemma a_focus__matrix_steps : forall s a n i j v,
 0<=j<v -> simplex_init_a_row s a n i j v |--
 simplex_init_a_undef s i j ** simplex_init_a_row_except s a n i j v j.
Proof. intros. unfold simplex_init_a_row,simplex_init_a_row_except.
 pose proof (range_focus__matrix_steps (fun k=>if k <? j then simplex_init_a_cell s a n i k else simplex_init_a_undef s i k) v j H) as HH.
 cbn beta in HH. rewrite Z.ltb_irrefl in HH. exact HH. Qed.
Lemma matrix_prefix_step__matrix_steps : forall s a n i j v,
 0<=j<v -> simplex_init_a_cell s a n i j ** simplex_init_a_row_except s a n i j v j |--
 simplex_init_a_row s a n i (j+1) v.
Proof. intros. unfold simplex_init_a_row,simplex_init_a_row_except.
 assert (E:(j <? j+1)=true) by (apply Z.ltb_lt;lia).
 assert (HE: forall k,0<=k<v -> k<>j ->
 (if k <? j then simplex_init_a_cell s a n i k else simplex_init_a_undef s i k)=
 (if k <? j+1 then simplex_init_a_cell s a n i k else simplex_init_a_undef s i k)).
 { intros k HK HNE. destruct (k <? j) eqn:H1; destruct (k <? j+1) eqn:H2; try reflexivity;
 apply Z.ltb_lt in H1 || apply Z.ltb_ge in H1;
 apply Z.ltb_lt in H2 || apply Z.ltb_ge in H2; lia. }
 pose proof (range_update__matrix_steps
 (fun k=>if k <? j then simplex_init_a_cell s a n i k else simplex_init_a_undef s i k)
 (fun k=>if k <? j+1 then simplex_init_a_cell s a n i k else simplex_init_a_undef s i k) v j H HE) as HH.
 cbn beta in HH. rewrite E in HH. exact HH.
Qed.
Lemma input_focus__matrix_steps : forall c a m n i j,
 0<=i<m -> 0<=j<n+1 -> simplex_init_input c a m n |--
 simplex_init_input_cell c a i j ** simplex_init_input_except c a m n i j.
Proof. intros. unfold simplex_init_input,simplex_init_input_except.
 sep_apply_l_atomic (range_focus__matrix_steps (fun k=>iter_sepcon(map (simplex_init_input_cell c a k)(Zrange 0 (n+1)))) m i H).
 sep_apply_l_atomic (range_focus__matrix_steps (simplex_init_input_cell c a i) (n+1) j H0).
 cancel (simplex_init_input_cell c a i j).
 cancel (iter_sepcon(remove_Znth j (map (simplex_init_input_cell c a i)(Zrange 0 (n+1))))). reflexivity.
Qed.
Lemma input_merge__matrix_steps : forall c a m n i j,
 0<=i<m -> 0<=j<n+1 -> simplex_init_input_cell c a i j ** simplex_init_input_except c a m n i j |-- simplex_init_input c a m n.
Proof. intros. unfold simplex_init_input,simplex_init_input_except. sepcon_right_assoc.
 sep_apply_r_atomic (range_update__matrix_steps (fun k=>iter_sepcon(map (simplex_init_input_cell c a k)(Zrange 0 (n+1)))) (fun k=>iter_sepcon(map (simplex_init_input_cell c a k)(Zrange 0 (n+1)))) m i H ltac:(auto)).
 sepcon_right_assoc.
 sep_apply_r_atomic (range_update__matrix_steps (simplex_init_input_cell c a i) (simplex_init_input_cell c a i) (n+1) j H0 ltac:(auto)).
 cancel (simplex_init_input_cell c a i j).
 cancel (iter_sepcon(remove_Znth j (map (simplex_init_input_cell c a i)(Zrange 0 (n+1))))). reflexivity.
Qed.
Lemma row_finish__matrix_steps : forall s a n i m v,
 0<=i<m ->
 simplex_init_row s a n (i+1) v i ** simplex_init_rows_except s a n i m v i |-- simplex_init_rows s a n (i+1) m v.
Proof. intros. unfold simplex_init_rows_except,simplex_init_rows. apply range_update__matrix_steps; auto.
 intros k HK HNE. unfold simplex_init_row.
 destruct (k <? i) eqn:H1; destruct (k <? i+1) eqn:H2; try reflexivity;
 apply Z.ltb_lt in H1 || apply Z.ltb_ge in H1;
 apply Z.ltb_lt in H2 || apply Z.ltb_ge in H2; lia.
Qed.
Lemma bounds_nth__callee_bridge : forall a k,
 Forall (Z.le (-2147483647)) a -> Forall (Z.ge 2147483647) a ->
 0<=k<Zlength a -> -2147483647<=Znth k a 0<=2147483647.
Proof.
 intros a k H1 H2 HK. split.
 - rewrite Forall_forall in H1. apply H1. unfold Znth. apply nth_In. rewrite Zlength_correct in HK. lia.
 - rewrite Forall_forall in H2. apply Z.ge_le. apply H2. unfold Znth. apply nth_In. rewrite Zlength_correct in HK. lia.
Qed.
Lemma coeff_bounds__callee_bridge : forall a m n i j,
 0<=m -> 0<=n<=8 -> Zlength a=m*9 ->
 Forall (Z.le (-2147483647)) a -> Forall (Z.ge 2147483647) a ->
 0<=i<m -> 0<=j<24 -> -2147483647<=simplex_init_coeff a n i j<=2147483647.
Proof.
 intros. unfold simplex_init_coeff. destruct (j <? n) eqn:E.
 - apply Z.ltb_lt in E. apply bounds_nth__callee_bridge; auto; lia.
 - lia.
Qed.
Lemma range_aux_length__callee_bridge : forall k lo,
 Zlength (Zrange_aux lo k)=Z.of_nat k.
Proof. induction k; intros; simpl; [reflexivity|]. rewrite Zlength_cons, IHk. lia. Qed.
Lemma range_length__callee_bridge : forall lo hi, lo<=hi -> Zlength(Zrange lo hi)=hi-lo.
Proof. intros. unfold Zrange. rewrite range_aux_length__callee_bridge, Z2Nat.id; lia. Qed.
Lemma map_nth__callee_bridge : forall (f:Z->Z) k len,
 0<=k<len -> Znth k (map f (Zrange 0 len)) 0=f k.
Proof. intros. rewrite (Znth_map _ _ _ 0 0) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity. Qed.
Lemma dist__callee_bridge : forall (P Q:Z->Assertion) l,
 iter_sepcon(map(fun j=>P j ** Q j)l) |-- iter_sepcon(map P l) ** iter_sepcon(map Q l).
Proof. intros P Q l. induction l; simpl.
 - apply derivable1_sepcon_emp_r.
 - rewrite !logic_equiv_iter_sepcon_cons. sepcon_right_assoc. sep_apply_l_atomic IHl; sepcon_right_assoc; cancel (P a); cancel (Q a); cancel; reflexivity.
Qed.
Lemma array_aux__callee_bridge : forall k x lo f,
 iter_sepcon(map(fun j=>(x+j*sizeof(INT))#Int|-> f j)(Zrange_aux lo k)) |--
 store_array_rec StoreIntAsElement.storeA x lo (lo+Z.of_nat k) (map f (Zrange_aux lo k)).
Proof.
 induction k; intros; simpl.
 - split_pure_spatial; [reflexivity|split_pures; dump_pre_spatial; (reflexivity || lia)].
 - rewrite logic_equiv_iter_sepcon_cons. unfold StoreIntAsElement.storeA at 1.
   replace (lo+Z.of_nat(S k)) with ((lo+1)+Z.of_nat k) by lia.
   sepcon_right_assoc. cancel ((x+lo*sizeof(INT))#Int|->f lo).
   replace (lo + Z.pos (Pos.of_succ_nat k)) with ((lo+1)+Z.of_nat k) by lia. apply IHk.
Qed.
Lemma array_full__callee_bridge : forall x n f, 0<=n ->
 iter_sepcon(map(fun j=>(x+j*sizeof(INT))#Int|->f j)(Zrange 0 n)) |--
 IntArray.full x n (map f (Zrange 0 n)).
Proof. intros. unfold IntArray.full, store_array, Zrange.
 pose proof (array_aux__callee_bridge (Z.to_nat(n-0)) x 0 f) as E.
 rewrite Z2Nat.id in E by lia. replace (0+(n-0)) with n in E by lia. exact E.
Qed.
Lemma iter_mono__callee_bridge : forall (P Q:Z->Assertion) l,
 (forall j, In j l -> P j |-- Q j) -> iter_sepcon(map P l) |-- iter_sepcon(map Q l).
Proof. intros P Q l. induction l; intros H; simpl.
 - reflexivity.
 - rewrite !logic_equiv_iter_sepcon_cons. sepcon_right_assoc.
   sep_apply_l_atomic (H a (or_introl eq_refl)).
   sep_apply_l_atomic (IHl ltac:(intros; apply H; right; auto)). cancel (Q a). reflexivity.
Qed.
Lemma array_Zrange__callee_bridge : forall x n f l, 0<=n ->
 l=map f (Zrange 0 n) ->
 iter_sepcon(map(fun j=>(x+j*sizeof(INT))#Int|->f j)(Zrange 0 n)) |-- IntArray.full x n l.
Proof. intros. subst. apply array_full__callee_bridge; auto. Qed.
Lemma pack3__callee_bridge : forall (P Q R T:Z->Assertion) l,
 (forall j, In j l -> P j |-- Q j ** R j ** T j) ->
 iter_sepcon(map P l) |-- iter_sepcon(map Q l) ** (iter_sepcon(map R l) ** iter_sepcon(map T l)).
Proof. intros P Q R T l. induction l; intros H; simpl.
 - apply (derivable1s_emp_sepcon_unfold emp (emp ** emp) emp); [reflexivity|apply derivable1_sepcon_emp_r].
 - rewrite !logic_equiv_iter_sepcon_cons. sepcon_right_assoc.
   sep_apply_l_atomic (H a (or_introl eq_refl)).
   sep_apply_l_atomic (IHl ltac:(intros; apply H; right; auto)).
   sepcon_right_assoc. cancel (Q a); cancel (R a); cancel (T a); cancel; reflexivity.
Qed.
Lemma vars_to_recompute__callee_bridge : forall s n r, 0<=n -> 0<=r ->
 simplex_init_vars s n (n+r) r (n+r) nil 0 |--
 IntArray.full (&((s)#"SxState"->ₛ"is_basic")) (n+r) (simplex_init_flags n (n+r)) **
 simplex_init_bounds s n r (n+r) **
 simplex_recompute_values s (n+r) (simplex_init_zeroes(n+r)) (simplex_init_ones(n+r)).
Proof.
 intros s n r HN HR. unfold simplex_init_vars, simplex_init_flags, simplex_init_bounds, simplex_recompute_values.
 sepcon_right_assoc. sep_apply_r_atomic (array_full__callee_bridge (&((s)#"SxState"->ₛ"is_basic")) (n+r) (fun j=>if j <? n then 0 else 1) ltac:(lia)).
 apply pack3__callee_bridge. intros j HJ. apply In_Zrange in HJ.
 unfold simplex_init_var. assert (E:(j <? n+r)=true) by (apply Z.ltb_lt;lia). rewrite E.
 unfold simplex_init_zeroes, simplex_init_ones.
 rewrite (map_nth__callee_bridge (fun _=>0) j (n+r) HJ), (map_nth__callee_bridge (fun _=>1) j (n+r) HJ).
 destruct (j <? n) eqn:EN.
 - apply Z.ltb_lt in EN. assert (F:(n<=?j)=false) by (apply Z.leb_gt;lia). rewrite F. simpl.
   sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
 - apply Z.ltb_ge in EN. assert (F:(n<=?j)=true) by (apply Z.leb_le;lia). rewrite F. simpl.
   sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end. reflexivity.
Qed.
Lemma range_shift__callee_bridge : forall k n lo,
 map(fun j=>n+j)(Zrange_aux lo k)=Zrange_aux (n+lo) k.
Proof. induction k; intros; simpl; [reflexivity|]. rewrite IHk. f_equal. f_equal. lia. Qed.
Lemma basic_map__callee_bridge : forall n r,
 simplex_init_basic n r=map(fun j=>n+j)(Zrange 0 r).
Proof. intros. unfold simplex_init_basic, Zrange. rewrite range_shift__callee_bridge.
 replace (n+r-n) with r by lia. replace (r-0) with r by lia. replace (n+0) with n by lia. reflexivity. Qed.
Lemma rows_to_recompute__callee_bridge : forall s a n r v,
 0<=r -> 0<=v<=24 ->
 simplex_init_rows s a n r r v |--
 IntArray.full (&((s)#"SxState"->ₛ"basic")) r (simplex_init_basic n r) **
 (simplex_recompute_rhs s r (simplex_init_rhs a r) (simplex_init_ones r) **
 simplex_recompute_matrix s r v (simplex_init_an a r n) (simplex_init_ones(r*24))).
Proof.
 intros s a n r v HR HV. rewrite basic_map__callee_bridge.
 unfold simplex_init_rows, simplex_recompute_rhs, simplex_recompute_matrix.
 sep_apply_r_atomic (array_full__callee_bridge (&((s)#"SxState"->ₛ"basic")) r (fun j=>n+j) HR).
 apply pack3__callee_bridge. intros i HI. apply In_Zrange in HI.
 unfold simplex_init_row. assert(E:(i <? r)=true) by (apply Z.ltb_lt;lia). rewrite E.
 unfold simplex_init_rhs, simplex_init_ones.
 rewrite (map_nth__callee_bridge (fun k=>Znth(k*9) a 0) i r HI), (map_nth__callee_bridge (fun _=>1) i r HI).
 sepcon_right_assoc. cancel ((&((s)#"SxState"->ₛ"basic")+i*sizeof(INT))#Int|->(n+i)).
 unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
 repeat match goal with |- ?L |-- _ => match L with context[?P ** _] => progress(cancel P) end end.
 unfold simplex_init_a_row. apply iter_mono__callee_bridge. intros j HJ. apply In_Zrange in HJ.
 assert(F:(j <? v)=true) by (apply Z.ltb_lt;lia). rewrite F.
 unfold simplex_recompute_cell, simplex_init_a_cell, simplex_init_an.
 assert(HK:0<=i*24+j<r*24) by nia.
 rewrite (map_nth__callee_bridge (fun k=>simplex_init_coeff a n (k/24)(k mod 24)) (i*24+j) (r*24) HK), (map_nth__callee_bridge (fun _=>1) (i*24+j) (r*24) HK).
 replace ((i*24+j)/24) with i by (rewrite Z.div_add_l by lia; rewrite Z.div_small by lia;lia).
 replace ((i*24+j) mod 24) with j by (rewrite Z.add_comm, Z.mod_add by lia; symmetry; apply Z.mod_small;lia).
 reflexivity.
Qed.
Lemma mapnth__final_result : forall (f:Z->Z) k j,
 0<=k -> 0<=j<k -> Znth j (map f (Zrange 0 k)) 0=f j.
Proof. intros. rewrite (Znth_map _ _ _ 0 0) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity. Qed.
Lemma range_nth__final_result : forall k low j,
 (j<Z.of_nat k)%Z -> 0<=j -> Znth j (Zrange_aux low k) 0=low+j.
Proof. induction k; intros; [lia|]. destruct (Z.eq_dec j 0).
 - subst; simpl; replace (low+0) with low by lia; reflexivity.
 - simpl. rewrite Znth_cons by lia. rewrite (IHk (low+1) (j-1)) by lia. lia.
Qed.
Lemma closed__final_result : forall a m n q on od,
 0<=m -> 0<=n -> m+n<=24 ->
 Forall (Z.le (-2147483647)) (simplex_init_an a m n) ->
 Forall (Z.ge 2147483647) (simplex_init_an a m n) ->
 Forall (Z.le (-2147483647)) (simplex_init_rhs a m) ->
 Forall (Z.ge 2147483647) (simplex_init_rhs a m) ->
 simplex_recompute_prefix (simplex_init_flags n (m+n)) (simplex_init_an a m n) (simplex_init_ones(m*24)) (simplex_init_rhs a m) (simplex_init_ones m) (simplex_init_basic n m) (simplex_init_zeroes(m+n)) (simplex_init_ones(m+n)) m (m+n) q on od ->
 q=1 /\ on=simplex_init_values a m n /\ od=simplex_init_ones(m+n).
Proof.
 intros a m n q on od HM HN HC HAL HAU HRL HRU HP.
 assert (LEN : forall k, 0<=k -> Zlength(simplex_init_zeroes k)=k /\ Zlength(simplex_init_ones k)=k).
 { intros; unfold simplex_init_zeroes,simplex_init_ones; rewrite !Zlength_map,!simplex_scan_range_length by lia; auto. }
 destruct (LEN (m+n) ltac:(lia)) as [LZ LO].
 assert (ONES : forall k j, 0<=k -> 0<=j<k -> Znth j (simplex_init_ones k) 0=1).
 { intros; unfold simplex_init_ones; apply mapnth__final_result; auto. }
 assert (BN : forall i, 0<=i<m -> Znth i (simplex_init_basic n m) 0=n+i).
 { intros. unfold simplex_init_basic,Zrange. apply range_nth__final_result; rewrite ?Z2Nat.id by lia; lia. }
 assert (FL : forall j, 0<=j<m+n -> Znth j (simplex_init_flags n (m+n)) 0= if j<?n then 0 else 1).
 { intros; unfold simplex_init_flags; apply mapnth__final_result; lia. }
 destruct (simplex_initialize_recompute_exact
 (simplex_init_flags n (m+n)) (simplex_init_an a m n) (simplex_init_ones(m*24))
 (simplex_init_rhs a m) (simplex_init_ones m) (simplex_init_basic n m)
 (simplex_init_zeroes(m+n)) (simplex_init_ones(m+n)) m n (m+n)
 HM HN ltac:(lia) LZ LO) as [x [y [HE [LX [LY HV]]]]].
 - intros j HJ; split; [unfold simplex_init_zeroes; apply mapnth__final_result; lia|apply ONES; lia].
 - intros j HJ HJ0. rewrite FL in HJ0 by auto. destruct (j<?n) eqn:E; [apply Z.ltb_lt; auto|discriminate].
 - intros i HI. rewrite BN by auto. split; [reflexivity|]. split.
   + rewrite FL by lia. assert (E : (n+i <? n)=false) by (apply Z.ltb_ge; lia). rewrite E. discriminate.
   + split.
     * pose proof (Forall_Znth_Zlength _ _ 0 i HRL ltac:(unfold simplex_init_rhs; rewrite Zlength_map,simplex_scan_range_length by lia; lia)).
       pose proof (Forall_Znth_Zlength _ _ 0 i HRU ltac:(unfold simplex_init_rhs; rewrite Zlength_map,simplex_scan_range_length by lia; lia)). lia.
     * split; [apply ONES; lia|]. intros j HJ. split.
       -- pose proof (Forall_Znth_Zlength _ _ 0 (i*24+j) HAL ltac:(unfold simplex_init_an; rewrite Zlength_map,simplex_scan_range_length by lia; nia)).
          pose proof (Forall_Znth_Zlength _ _ 0 (i*24+j) HAU ltac:(unfold simplex_init_an; rewrite Zlength_map,simplex_scan_range_length by lia; nia)). lia.
       -- apply ONES; nia.
 - unfold simplex_recompute_prefix in HP. rewrite HE in HP. inversion HP; subst q on od.
   split; [reflexivity|]. split; apply (proj2 (list_eq_ext _ _ 0)); split; try (unfold simplex_init_values,simplex_init_ones; rewrite Zlength_map,simplex_scan_range_length by lia; lia).
   + intros j HJ. destruct(HV j ltac:(lia)) as [E _]. rewrite E. symmetry. unfold simplex_init_values. apply mapnth__final_result; lia.
   + intros j HJ. destruct(HV j ltac:(lia)) as [_ E]. rewrite E. symmetry. apply ONES; lia.
Qed.
Lemma iter_merge__final_result : forall (xs:list Z) (p q:Z->Assertion),
 naive_C_Rules.iter_sepcon(map p xs) ** naive_C_Rules.iter_sepcon(map q xs) |-- naive_C_Rules.iter_sepcon(map(fun j=>p j ** q j) xs).
Proof. induction xs; intros; simpl.
 - unfold naive_C_Rules.iter_sepcon. simpl. apply derivable1_sepcon_emp_l.
 - rewrite !logic_equiv_iter_sepcon_cons. sepcon_right_assoc. cancel (p a). cancel(q a). apply IHxs. Qed.
Lemma iter_mono__final_result : forall (xs:list Z) (p q:Z->Assertion),
 (forall j, In j xs -> p j |-- q j) -> naive_C_Rules.iter_sepcon(map p xs) |-- naive_C_Rules.iter_sepcon(map q xs).
Proof. induction xs; intros; simpl; [reflexivity|].
 rewrite !logic_equiv_iter_sepcon_cons. sep_apply_l_atomic (H a ltac:(simpl; auto)). cancel(q a). apply IHxs. intros; apply H; simpl; auto. Qed.
Lemma aux_shift__final_result : forall k low off,
 Zrange_aux (low+off) k=map(fun j=>off+j)(Zrange_aux low k).
Proof. induction k; intros; simpl; [reflexivity|]. f_equal; [lia|].
 replace (low+off+1) with ((low+1)+off) by lia. apply IHk. Qed.
Lemma basic_map__final_result : forall n m,
 simplex_init_basic n m=map(fun i=>n+i)(Zrange 0 m).
Proof. intros; unfold simplex_init_basic,Zrange. replace (n+m-n) with m by lia. replace (m-0) with m by lia.
 replace n with (0+n) at 1 by lia. apply aux_shift__final_result. Qed.
Lemma array_aux__final_result : forall k low x (f:Z->Z),
 store_array_rec (fun x j v=>(x+j*sizeof(INT))#Int|->v) x low (low+Z.of_nat k) (map f (Zrange_aux low k)) |--
 naive_C_Rules.iter_sepcon(map(fun j=>(x+j*sizeof(INT))#Int|->f j)(Zrange_aux low k)).
Proof. induction k; intros; simpl.
 - Intros. reflexivity.
 - replace (low+Z.pos(Pos.of_succ_nat k)) with (low+1+Z.of_nat k) by lia.
   rewrite logic_equiv_iter_sepcon_cons. cancel ((x+low*sizeof(INT))#Int|->f low). apply IHk.
Qed.
Lemma array_map__final_result : forall x k (f:Z->Z), 0<=k ->
 IntArray.full x k (map f (Zrange 0 k)) |-- naive_C_Rules.iter_sepcon(map(fun j=>(x+j*sizeof(INT))#Int|->f j)(Zrange 0 k)).
Proof. intros. unfold IntArray.full,store_array,StoreIntAsElement.storeA,Zrange. replace (k-0) with k by lia.
 replace k with (0+Z.of_nat(Z.to_nat k)) at 1 by (rewrite Z2Nat.id by lia; lia).
 apply array_aux__final_result. Qed.
Lemma iter_three__final_result : forall xs (p q r:Z->Assertion),
 naive_C_Rules.iter_sepcon(map p xs) ** (naive_C_Rules.iter_sepcon(map q xs) ** naive_C_Rules.iter_sepcon(map r xs)) |-- naive_C_Rules.iter_sepcon(map(fun j=>p j ** (q j ** r j)) xs).
Proof. intros. sep_apply_l_atomic(iter_merge__final_result xs q r).
 sep_apply_r_atomic(iter_merge__final_result xs p (fun j=>q j ** r j)). cancel (naive_C_Rules.iter_sepcon(map p xs)). reflexivity. Qed.
Lemma an_nth__final_result : forall a m n i j, 0<=m -> 0<=i<m -> 0<=j<24 ->
 Znth(i*24+j)(simplex_init_an a m n)0=simplex_init_coeff a n i j.
Proof. intros. unfold simplex_init_an. rewrite mapnth__final_result by nia.
 assert (ED : (i*24+j)/24=i) by (symmetry; apply Z.div_unique with (r:=j); [left; lia|ring]).
 assert (EM : (i*24+j) mod 24=j) by (symmetry; apply Z.mod_unique with (q:=i); [left; lia|ring]).
 rewrite ED,EM. reflexivity. Qed.
Lemma vars_pack__final_result : forall s a m n, 0<=m -> 0<=n ->
 IntArray.full (&(s#"SxState"->ₛ"is_basic")) (m+n) (simplex_init_flags n (m+n)) **
 simplex_init_bounds s n m (m+n) ** simplex_recompute_values s (m+n) (simplex_init_values a m n) (simplex_init_ones(m+n)) |--
 simplex_init_vars s n (m+n) m (m+n) (simplex_init_rhs a m) 1.
Proof.
 intros. unfold simplex_init_flags.
 sep_apply_l_atomic(array_map__final_result (&(s#"SxState"->ₛ"is_basic")) (m+n) (fun j=>if j<?n then 0 else 1) ltac:(lia)).
 unfold simplex_init_bounds,simplex_recompute_values,simplex_init_vars.
 lazymatch goal with |- (?P ** (?Q ** ?R)) |-- ?T =>
 lazymatch P with naive_C_Rules.iter_sepcon(map ?p ?xs) =>
 lazymatch Q with naive_C_Rules.iter_sepcon(map ?q xs) =>
 lazymatch R with naive_C_Rules.iter_sepcon(map ?r xs) =>
 lazymatch T with naive_C_Rules.iter_sepcon(map ?t xs) =>
 assert (HE: forall j, In j xs -> p j ** (q j ** r j) |-- t j)
 end end end end end.
 { intros j HJ. apply In_Zrange in HJ.
 unfold simplex_init_var.
 assert (E:(j<?m+n)=true) by (apply Z.ltb_lt; lia). rewrite E.
 unfold simplex_init_values,simplex_init_ones. rewrite !mapnth__final_result by lia.
 replace (n+m) with (m+n) by lia. rewrite E. simpl.
 destruct (j<?n) eqn:EN.
 - assert (F:(n<=?j)=false) by (apply Z.leb_gt; apply Z.ltb_lt in EN; lia). rewrite F; simpl.
   sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _]=>progress(cancel P) end end. reflexivity.
 - assert (F:(n<=?j)=true) by (apply Z.leb_le; apply Z.ltb_ge in EN; lia). rewrite F; simpl.
   sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _]=>progress(cancel P) end end. reflexivity.
 }
 sep_apply_r_atomic(iter_mono__final_result _ _ _ HE). apply iter_three__final_result.
Qed.
Lemma cell_pack__final_result : forall s a m n i j,
 0<=m -> 0<=n -> m+n<=24 -> 0<=i<m -> 0<=j<m+n ->
 simplex_recompute_cell s (simplex_init_an a m n) (simplex_init_ones(m*24)) i j |--
 (if j<?m+n then simplex_init_a_cell s a n i j else simplex_init_a_undef s i j).
Proof. intros. assert(E:(j<?m+n)=true) by(apply Z.ltb_lt;lia). rewrite E.
 unfold simplex_recompute_cell,simplex_init_a_cell. rewrite an_nth__final_result by lia.
 unfold simplex_init_ones. rewrite mapnth__final_result by nia. reflexivity. Qed.
Lemma rows_pack__final_result : forall s a m n, 0<=m -> 0<=n -> m+n<=24 ->
 IntArray.full (&(s#"SxState"->ₛ"basic")) m (simplex_init_basic n m) **
 (simplex_recompute_rhs s m (simplex_init_rhs a m) (simplex_init_ones m) **
 simplex_recompute_matrix s m (m+n) (simplex_init_an a m n) (simplex_init_ones(m*24))) |--
 simplex_init_rows s a n m m (m+n).
Proof.
 intros. rewrite basic_map__final_result.
 sep_apply_l_atomic(array_map__final_result (&(s#"SxState"->ₛ"basic")) m (fun i=>n+i) H).
 unfold simplex_recompute_rhs,simplex_recompute_matrix,simplex_init_rows.
 lazymatch goal with |- (?P ** (?Q ** ?R)) |-- ?T =>
 lazymatch P with naive_C_Rules.iter_sepcon(map ?p ?xs) =>
 lazymatch Q with naive_C_Rules.iter_sepcon(map ?q xs) =>
 lazymatch R with naive_C_Rules.iter_sepcon(map ?r xs) =>
 lazymatch T with naive_C_Rules.iter_sepcon(map ?t xs) =>
 assert (HE: forall j, In j xs -> p j ** (q j ** r j) |-- t j)
 end end end end end.
 { intros i HI. apply In_Zrange in HI. unfold simplex_init_row.
 assert(E:(i<?m)=true) by(apply Z.ltb_lt;lia). rewrite E.
 unfold simplex_init_rhs,simplex_init_ones. rewrite !mapnth__final_result by lia.
 unfold simplex_init_a_row.
 assert(HC:forall j, In j (Zrange 0 (m+n)) -> simplex_recompute_cell s (simplex_init_an a m n) (simplex_init_ones(m*24)) i j |--
 (if j<?m+n then simplex_init_a_cell s a n i j else simplex_init_a_undef s i j)).
 { intros;apply cell_pack__final_result;try lia; apply In_Zrange;auto. }
 csimpl. sepcon_right_assoc. repeat match goal with |- ?L |-- _ => match L with context[?P ** _]=>progress(cancel P) end end. apply iter_mono__final_result. exact HC.
 }
 sep_apply_r_atomic(iter_mono__final_result _ _ _ HE). apply iter_three__final_result.
Qed.
Lemma range_nth__rejected_returns : forall (f:Z->Assertion) k i,
 0<=k -> 0<=i<k -> Znth i (map f (Zrange 0 k)) emp=f i.
Proof. intros. rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length; lia).
 rewrite simplex_scan_range_nth by lia. reflexivity. Qed.
Lemma range_merge__rejected_returns : forall (f:Z->Assertion) k i,
 0<=k -> 0<=i<k ->
 f i ** iter_sepcon(remove_Znth i (map f (Zrange 0 k))) |-- iter_sepcon(map f (Zrange 0 k)).
Proof. intros f k i HK HI.
 pose proof (iter_sepcon_merge_remove_Znth i (map f (Zrange 0 k)) (f i)) as HM.
 rewrite <- (range_nth__rejected_returns f k i HK HI) in HM.
 rewrite replace_Znth_Znth in HM. rewrite range_nth__rejected_returns in HM by auto.
 apply HM. rewrite Zlength_map,simplex_scan_range_length; lia. Qed.
Lemma input_merge__rejected_returns : forall c a m n i j,
 0<=m -> 0<=n -> 0<=i<m -> 0<=j<=n ->
 simplex_init_input_except c a m n i j ** simplex_init_input_cell c a i j |-- simplex_init_input c a m n.
Proof. intros c a m n i j HM HN HI HJ.
 unfold simplex_init_input, simplex_init_input_except. sepcon_right_assoc.
 sep_apply_r_atomic (range_merge__rejected_returns
  (fun k=>iter_sepcon(map (simplex_init_input_cell c a k) (Zrange 0 (n+1)))) m i HM HI).
 sep_apply_r_atomic (range_merge__rejected_returns (simplex_init_input_cell c a i) (n+1) j ltac:(lia) ltac:(lia)).
 sepcon_right_assoc.
 cancel (simplex_init_input_cell c a i j).
 cancel (iter_sepcon(remove_Znth j (map (simplex_init_input_cell c a i) (Zrange 0 (n+1))))).
 reflexivity.
Qed.
