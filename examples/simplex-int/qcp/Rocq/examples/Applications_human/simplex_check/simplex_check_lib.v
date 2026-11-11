From Coq Require Import ZArith List Lia String Bool.
From SimpleC.EE.Applications_human.simplex_initialize Require Export simplex_initialize_lib.
From SimpleC.EE.Applications_human.simplex_solve Require Export simplex_solve_lib.
Import ListNotations naive_C_Rules.
Local Open Scope Z_scope.
(* Fixed entrance A, physical row stride9. The 400-slot solver view uses
   safe logical fillers; it makes no assertion about inactive physical cells. *)
Definition simplex_check_initial_num (a:list Z) (m n:Z) : list Z :=
 map (fun k => if k <? 16 then Znth (k*9) a 0
              else simplex_init_coeff a n ((k-16)/24) ((k-16) mod 24))
 (Zrange 0 400).
Definition simplex_check_initial (a:list Z) (m n:Z) : simplex_solve_snapshot :=
 simplex_solve_pack (simplex_check_initial_num a m n) (simplex_init_ones 400)
 (simplex_init_basic n m) (simplex_init_flags n (m+n))
 (simplex_init_values a m n) (simplex_init_ones (m+n)).
(* The specified exact Check result is composition of the two proved APIs.
   Rejection has no update; accepted input initializes before any budget test. *)
Definition simplex_check_compute (a:list Z) (m n limit:Z) :=
 if existsb (fun i => existsb (fun j => Znth(i*9+j) a 0 =? -2147483648)
                   (Zrange 0 (n+1))) (Zrange 0 m)
 then (-1,None)
 else let '(q,s) := simplex_solve_compute
  (simplex_init_zeroes (m+n)) (simplex_init_flags n (m+n))
  (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))
  (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))
  m (m+n) limit (simplex_check_initial a m n) in (q,Some s).

Lemma check_initial_num_length : forall a m n,
 Zlength (simplex_check_initial_num a m n)=400.
Proof. intros. unfold simplex_check_initial_num.
 rewrite Zlength_map,simplex_scan_range_length by lia. reflexivity. Qed.
Lemma check_initial_num_rhs : forall a m n i,
 0<=i<m -> m<=16 ->
 Znth i (simplex_check_initial_num a m n) 0=Znth(i*9) a 0.
Proof. intros. unfold simplex_check_initial_num.
 rewrite (Znth_map _ _ _ 0 0) by (rewrite simplex_scan_range_length;lia).
 rewrite simplex_scan_range_nth by lia.
 rewrite (proj2 (Z.ltb_lt i 16) ltac:(lia)). reflexivity. Qed.
Lemma check_initial_num_matrix : forall a m n i j,
 0<=i<m -> m<=16 -> 0<=j<24 ->
 Znth (16+i*24+j) (simplex_check_initial_num a m n) 0 =
 simplex_init_coeff a n i j.
Proof. intros. unfold simplex_check_initial_num.
 rewrite (Znth_map _ _ _ 0 0) by (rewrite simplex_scan_range_length;lia).
 rewrite simplex_scan_range_nth by lia.
 rewrite (proj2 (Z.ltb_ge (16+i*24+j) 16) ltac:(lia)).
 replace (16+i*24+j-16) with (i*24+j) by lia.
 replace (i*24+j) with (j+i*24) by ring. rewrite Z.div_add,Z.mod_add by lia.
 rewrite Z.div_small,Z.mod_small by lia. replace (0+i) with i by lia. reflexivity. Qed.

(* Address-indexed logical snapshots allow an independent Some/None choice
   for every scalar member. None is unknown ownership, never an old C value
   or a physical initialization-tag/byte snapshot. *)
Local Open Scope sac.
Local Open Scope string_scope.
Local Open Scope list_scope.
Definition simplex_check_member (p:Z) (old:Z->option Z) : Assertion :=
 match old p with Some v => p # Int |-> v | None => p # Int |->_ end.
Definition simplex_check_members (ps:list Z) (old:Z->option Z) : Assertion :=
 iter_sepcon (map (fun p=>simplex_check_member p old) ps).
Definition simplex_check_rat_addresses (p:Z) : list Z :=
 [ &(p #"SxRat" ->ₛ "num"); &(p #"SxRat" ->ₛ "den") ].
Definition simplex_check_var_addresses (s j:Z) : list Z :=
 [ &(s #"SxState" ->ₛ "is_basic") + j*sizeof(INT);
   &(s #"SxState" ->ₛ "has_lower") + j*sizeof(INT);
   &(s #"SxState" ->ₛ "has_upper") + j*sizeof(INT) ] ++
 simplex_check_rat_addresses (&(s #"SxState" ->ₛ "lower")+j*sizeof("SxRat")) ++
 simplex_check_rat_addresses (&(s #"SxState" ->ₛ "upper")+j*sizeof("SxRat")) ++
 simplex_check_rat_addresses (&(s #"SxState" ->ₛ "value")+j*sizeof("SxRat")).
Definition simplex_check_a_addresses (s i j:Z) : list Z :=
 simplex_check_rat_addresses
 (&(s #"SxState" ->ₛ "a")+i*(sizeof("SxRat")*24)+j*sizeof("SxRat")).
Definition simplex_check_row_addresses (s i:Z) : list Z :=
 [ &(s #"SxState" ->ₛ "basic")+i*sizeof(INT) ] ++
 simplex_check_rat_addresses (&(s #"SxState" ->ₛ "rhs")+i*sizeof("SxRat")).
Definition simplex_check_scalars (s:Z) : list Z :=
 [ &(s #"SxState" ->ₛ "rows"); &(s #"SxState" ->ₛ "inputs");
   &(s #"SxState" ->ₛ "vars") ].
Definition simplex_check_active_addresses (s m n:Z) : list Z :=
 simplex_check_scalars s ++
 flat_map (simplex_check_var_addresses s) (Zrange 0 (m+n)) ++
 flat_map (fun i=>simplex_check_row_addresses s i ++
 flat_map (simplex_check_a_addresses s i) (Zrange 0 (m+n))) (Zrange 0 m).
Definition simplex_check_frame_addresses (s m n:Z) : list Z :=
 flat_map (simplex_check_var_addresses s) (Zrange (m+n) 24) ++
 flat_map (fun i=>simplex_check_row_addresses s i ++
 flat_map (simplex_check_a_addresses s i) (Zrange 0 24)) (Zrange m 16) ++
 flat_map (fun i=>flat_map (simplex_check_a_addresses s i) (Zrange (m+n) 24)) (Zrange 0 m).
Definition simplex_check_old (s m n:Z) (old:Z->option Z) : Assertion :=
 simplex_check_members (simplex_check_active_addresses s m n) old.
Definition simplex_check_frame (s m n:Z) (old:Z->option Z) : Assertion :=
 simplex_check_members (simplex_check_frame_addresses s m n) old.
(* Complete 16x9 input complement; active cells are carried by Init's public
   stride9 assertion. Snapshot choices here are independent per inactive cell. *)
Definition simplex_check_input_frame (c m n:Z) (old:Z->option Z) : Assertion :=
 simplex_check_members
 (flat_map (fun i=>map (fun j=>c+i*(sizeof(INT)*9)+j*sizeof(INT))
                    (Zrange (n+1) 9)) (Zrange 0 m) ++
  flat_map (fun i=>map (fun j=>c+i*(sizeof(INT)*9)+j*sizeof(INT))
                    (Zrange 0 9)) (Zrange m 16)) old.

Lemma check_member_forget : forall p old,
 simplex_check_member p old |-- p # Int |->_.
Proof. intros. unfold simplex_check_member. destruct (old p).
 - apply store_int_undef_store_int.
 - reflexivity.
Qed.
Lemma check_members_forget : forall ps old,
 simplex_check_members ps old |--
 iter_sepcon (map (fun p=>p # Int |->_) ps).
Proof.
 induction ps; intros; unfold simplex_check_members in *; simpl.
 - reflexivity.
 - rewrite !logic_equiv_iter_sepcon_cons.
   sep_apply_l_atomic (check_member_forget a old).
   sep_apply_l_atomic (IHps old). cancel; reflexivity.
Qed.
Lemma check_members_app : forall ps qs old,
 simplex_check_members (ps++qs) old --||--
 simplex_check_members ps old ** simplex_check_members qs old.
Proof. intros. unfold simplex_check_members. rewrite map_app.
 apply logic_equiv_iter_sepcon_app. Qed.


Local Open Scope Z_scope.
Lemma check_map_nth : forall (f:Z->Z) len j default,
 0<=j<len -> Znth j (map f (Zrange 0 len)) default=f j.
Proof. intros. rewrite (Znth_map _ _ _ 0 default)
 by (rewrite simplex_scan_range_length;lia).
 rewrite simplex_scan_range_nth by lia. reflexivity. Qed.
Lemma check_initial_initialized : forall a m n,
 0<=m<=16 -> 0<=n<=8 ->
 simplex_solve_initialized a
 (simplex_init_zeroes (m+n)) (simplex_init_flags n (m+n))
 (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))
 (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))
 m n (simplex_check_initial a m n).
Proof.
 intros a m n HM HN.
 unfold simplex_check_initial,simplex_solve_pack,simplex_solve_initialized.
 cbn zeta.
 rewrite check_initial_num_length.
 unfold simplex_init_ones,simplex_init_zeroes,simplex_init_flags,
 simplex_init_values,simplex_init_basic.
 rewrite !Zlength_map,!simplex_scan_range_length by lia.
 rewrite range_length__callee_bridge by lia.
 do 12 (split; [lia|]).
 split.
 - intros i HI. assert (E:Znth i (Zrange n (n+m)) 0=n+i).
   { unfold Zrange. apply range_nth__final_result; rewrite ?Z2Nat.id;lia. } rewrite E.
   rewrite check_initial_num_rhs by lia.
   rewrite check_map_nth by lia. repeat split; lia.
 - split.
   + intros i j HI HJ. rewrite check_initial_num_matrix by lia.
     rewrite check_map_nth by lia. auto.
   + intros j HJ. rewrite !check_map_nth by lia.
     unfold simplex_init_value_at. rewrite (proj2 (Z.ltb_lt j (n+m)) ltac:(lia)).
     destruct (j <? n) eqn:E.
     * apply Z.ltb_lt in E. rewrite (proj2 (Z.leb_gt n j) E). simpl. repeat split; auto.
     * apply Z.ltb_ge in E. rewrite (proj2 (Z.leb_le n j) E).
       unfold simplex_init_rhs. rewrite check_map_nth by lia.
       simpl. repeat split; auto.
Qed.
Lemma check_initial_origin : forall a m n,
 0<=m<=16 -> 0<=n<=8 ->
 simplex_solve_origin a
 (simplex_init_zeroes (m+n)) (simplex_init_flags n (m+n))
 (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))
 (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))
 m n (simplex_check_initial a m n).
Proof.
 intros. exists (simplex_check_initial a m n). split.
 - apply check_initial_initialized; auto.
 - exists O. reflexivity.
Qed.
Lemma check_initial_normal : forall a m n,
 0<=m<=16 -> 0<=n<=8 ->
 (forall i j,0<=i<m -> 0<=j<=n ->
 -2147483647<=Znth(i*9+j) a 0<=2147483647) ->
 simplex_solve_normal a
 (simplex_init_zeroes (m+n)) (simplex_init_flags n (m+n))
 (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))
 (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))
 m n (simplex_check_initial a m n).
Proof. intros. apply solve_initialized_normal; try lia; auto.
 apply check_initial_initialized; auto. Qed.


Local Open Scope sac.
Local Open Scope Z_scope.
Lemma check_unknown_var : forall s n m j,
 0<=j<m+n ->
 iter_sepcon (map (fun p=>p # Int |->_) (simplex_check_var_addresses s j))
 --||-- simplex_init_var s n 0 0 (m+n) nil 0 j.
Proof.
 intros. unfold simplex_check_var_addresses,simplex_check_rat_addresses,
 simplex_init_var. rewrite (proj2 (Z.ltb_ge j 0) ltac:(lia)).
 cbn [app map]. rewrite !logic_equiv_iter_sepcon_cons,logic_equiv_iter_sepcon_nil.
 unfold simplex_scan_rat_memory. split; csimpl; elim_emp; sepcon_right_assoc; cancel; reflexivity.
Qed.
Lemma check_unknown_a : forall s i j,
 iter_sepcon (map (fun p=>p # Int |->_) (simplex_check_a_addresses s i j))
 --||-- simplex_init_a_undef s i j.
Proof.
 intros. unfold simplex_check_a_addresses,simplex_check_rat_addresses,simplex_init_a_undef.
 cbn [map]. rewrite !logic_equiv_iter_sepcon_cons,logic_equiv_iter_sepcon_nil.
 elim_emp. reflexivity.
Qed.
Lemma check_unknown_row : forall s m n i,
 0<=i<m -> 0<=m+n ->
 iter_sepcon (map (fun p=>p # Int |->_)
 (simplex_check_row_addresses s i ++
 flat_map (simplex_check_a_addresses s i) (Zrange 0 (m+n))))
 --||-- simplex_init_row s nil n 0 (m+n) i.
Proof.
 intros. rewrite map_app,logic_equiv_iter_sepcon_app,solve_iter_flat.
 unfold simplex_init_row. rewrite (proj2 (Z.ltb_ge i 0) ltac:(lia)).
 unfold simplex_init_a_row.
 assert (E:iter_sepcon
 (map (fun x=>iter_sepcon (map (fun p=>p # Int |->_) (simplex_check_a_addresses s i x))) (Zrange 0 (m+n)))
 --||-- iter_sepcon (map (fun j=>if j <? 0 then simplex_init_a_cell s nil n i j else simplex_init_a_undef s i j) (Zrange 0 (m+n)))).
 { apply solve_iter_equiv. intros j HJ. apply In_Zrange in HJ.
   rewrite (proj2 (Z.ltb_ge j 0) ltac:(lia)). apply check_unknown_a. }
 rewrite E. unfold simplex_check_row_addresses,simplex_check_rat_addresses.
 cbn [app map]. rewrite !logic_equiv_iter_sepcon_cons,logic_equiv_iter_sepcon_nil.
 unfold simplex_scan_rat_memory. split; csimpl; elim_emp; sepcon_right_assoc; cancel; reflexivity.
Qed.
Lemma check_old_initialize : forall s m n old,
 0<=m -> 0<=n ->
 simplex_check_old s m n old |--
 (&(s #"SxState" ->ₛ "rows")) # Int |->_ **
 (&(s #"SxState" ->ₛ "inputs")) # Int |->_ **
 (&(s #"SxState" ->ₛ "vars")) # Int |->_ **
 simplex_init_vars s n 0 0 (m+n) nil 0 **
 simplex_init_rows s nil n 0 m (m+n).
Proof.
 intros. unfold simplex_check_old.
 sep_apply_l_atomic (check_members_forget (simplex_check_active_addresses s m n) old).
 unfold simplex_check_active_addresses.
 rewrite !map_app,!logic_equiv_iter_sepcon_app,!solve_iter_flat.
 assert (EV:iter_sepcon
 (map (fun j=>iter_sepcon (map (fun p=>p # Int |->_) (simplex_check_var_addresses s j))) (Zrange 0 (m+n)))
 --||-- simplex_init_vars s n 0 0 (m+n) nil 0).
 { unfold simplex_init_vars. apply solve_iter_equiv. intros j HJ.
   apply In_Zrange in HJ. apply check_unknown_var;lia. }
 rewrite EV.
 assert (ER:iter_sepcon
 (map (fun i=>iter_sepcon (map (fun p=>p # Int |->_)
 (simplex_check_row_addresses s i ++ flat_map (simplex_check_a_addresses s i) (Zrange 0 (m+n))))) (Zrange 0 m))
 --||-- simplex_init_rows s nil n 0 m (m+n)).
 { unfold simplex_init_rows. apply solve_iter_equiv. intros i HI.
   apply In_Zrange in HI. apply check_unknown_row;lia. }
 rewrite ER. unfold simplex_check_scalars.
 cbn [map]. rewrite !logic_equiv_iter_sepcon_cons,logic_equiv_iter_sepcon_nil.
 elim_emp. cancel; reflexivity.
Qed.


Lemma check_list_length : forall k,
 0<=k -> Zlength (simplex_init_zeroes k)=k /\ Zlength (simplex_init_ones k)=k.
Proof. intros. unfold simplex_init_zeroes,simplex_init_ones.
 rewrite !Zlength_map,!simplex_scan_range_length by lia. auto. Qed.
Lemma check_init_vars_solver : forall s a m n,
 0<=m<=16 -> 0<=n<=8 ->
 simplex_init_vars s n (m+n) m (m+n) (simplex_init_rhs a m) 1 |--
 IntArray.full (&(s #"SxState" ->ₛ "is_basic")) (m+n) (simplex_init_flags n (m+n)) **
 simplex_solve_variables s (m+n)
 (simplex_init_zeroes (m+n)) (simplex_init_flags n (m+n))
 (simplex_init_values a m n) (simplex_init_ones (m+n))
 (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))
 (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n)).
Proof.
 intros s a m n HM HN.
 unfold simplex_init_vars.
 set (F:=simplex_solve_var_slot s (m+n)
 (simplex_init_zeroes (m+n)) (simplex_init_flags n (m+n))
 (simplex_init_values a m n) (simplex_init_ones (m+n))
 (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))
 (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))).
 set (G:=fun j => (&(s #"SxState" ->ₛ "is_basic")+j*sizeof(INT)) # Int |-> Znth j (simplex_init_flags n (m+n)) 0).
 assert (HS:forall j, In j (Zrange 0 (m+n)) ->
 simplex_init_var s n (m+n) m (m+n) (simplex_init_rhs a m) 1 j |-- G j ** F j).
 { intros j HJ. apply In_Zrange in HJ.
   unfold G,F,simplex_init_var,simplex_solve_var_slot.
   rewrite (proj2 (Z.ltb_lt j (m+n)) ltac:(lia)).
   unfold simplex_init_zeroes,simplex_init_ones,simplex_init_flags,simplex_init_values.
   rewrite !check_map_nth by lia. replace (n+m) with (m+n) by lia.
   rewrite (proj2 (Z.ltb_lt j (m+n)) ltac:(lia)).
   destruct (j <? n) eqn:E.
   - apply Z.ltb_lt in E. rewrite (proj2 (Z.leb_gt n j) E). simpl.
     sepcon_right_assoc. cancel; reflexivity.
   - apply Z.ltb_ge in E. rewrite (proj2 (Z.leb_le n j) E). simpl.
     sepcon_right_assoc. cancel; reflexivity. }
 sep_apply_l_atomic (solve_iter_split (Zrange 0 (m+n)) _ G F HS).
 assert (HG:iter_sepcon(map G (Zrange 0 (m+n))) |--
 IntArray.full (&(s #"SxState" ->ₛ "is_basic")) (m+n) (simplex_init_flags n (m+n))).
 { unfold G. apply iter_full__success_math.
   unfold simplex_init_flags. rewrite Zlength_map,simplex_scan_range_length by lia. reflexivity. }
 sep_apply_l_atomic HG.
 unfold simplex_solve_variables.
 fold F.
 rewrite (range_split__failure_rhs 0 (m+n) 24 ltac:(lia)),map_app,logic_equiv_iter_sepcon_app.
 assert (HE: emp |-- iter_sepcon(map F (Zrange (m+n) 24))).
 { apply solve_iter_emp_build. intros j HJ. apply In_Zrange in HJ.
   unfold F,simplex_solve_var_slot. rewrite (proj2 (Z.ltb_ge j (m+n)) ltac:(lia)). reflexivity. }
 sep_apply_r_atomic HE. elim_emp. cancel; reflexivity.
Qed.


Lemma check_init_pivot_rhs : forall s a m n i,
 0<=m<=16 -> 0<=i<m ->
 simplex_pivot_memory_cell s i
 (Znth i (simplex_check_initial_num a m n) 0)
 (Znth i (simplex_init_ones 400) 1) =
 simplex_scan_rat_memory s "rhs" i true (Znth(i*9) a 0) 1.
Proof.
 intros. unfold simplex_pivot_memory_cell.
 rewrite (proj2 (Z.ltb_lt i 16) ltac:(lia)),check_initial_num_rhs by lia.
 unfold simplex_init_ones. rewrite check_map_nth by lia. reflexivity.
Qed.
Lemma check_init_pivot_a : forall s a m n i j,
 0<=m<=16 -> 0<=i<m -> 0<=j<24 ->
 simplex_pivot_memory_cell s (16+i*24+j)
 (Znth (16+i*24+j) (simplex_check_initial_num a m n) 0)
 (Znth (16+i*24+j) (simplex_init_ones 400) 1) =
 simplex_init_a_cell s a n i j.
Proof.
 intros. unfold simplex_pivot_memory_cell.
 rewrite (proj2 (Z.ltb_ge (16+i*24+j) 16) ltac:(lia)).
 rewrite check_initial_num_matrix by lia.
 unfold simplex_init_ones. rewrite check_map_nth by lia.
 replace (16+i*24+j-16) with (j+i*24) by ring.
 rewrite Z.div_add,Z.mod_add by lia. rewrite Z.div_small,Z.mod_small by lia.
 replace (0+i) with i by lia. reflexivity.
Qed.
Lemma check_init_rows_solver : forall s a m n,
 0<=m<=16 -> 0<=n<=8 ->
 simplex_init_rows s a n m m (m+n) |--
 IntArray.full (&(s #"SxState" ->ₛ "basic")) m (simplex_init_basic n m) **
 simplex_pivot_memory s m (m+n) (simplex_check_initial_num a m n) (simplex_init_ones 400).
Proof.
 intros s a m n HM HN.
 unfold simplex_init_rows.
 set (B:=fun i=> (&(s #"SxState" ->ₛ "basic")+i*sizeof(INT)) # Int |-> Znth i (simplex_init_basic n m) 0).
 set (R:=fun i=>simplex_scan_rat_memory s "rhs" i true (Znth (i*9) a 0) 1).
 set (T:=fun i=>simplex_init_a_row s a n i (m+n) (m+n)).
 assert (HS:forall i,In i (Zrange 0 m) ->
 simplex_init_row s a n m (m+n) i |-- B i ** (R i ** T i)).
 { intros i HI. apply In_Zrange in HI.
   unfold simplex_init_row,B,R,T.
   rewrite (proj2 (Z.ltb_lt i m) ltac:(lia)).
   rewrite basic_map__final_result. rewrite check_map_nth by lia.
   sepcon_right_assoc. reflexivity. }
 sep_apply_l_atomic (solve_iter_split (Zrange 0 m) _ B (fun i=>R i ** T i) HS).
 assert (HB:iter_sepcon(map B (Zrange 0 m)) |--
 IntArray.full (&(s #"SxState" ->ₛ "basic")) m (simplex_init_basic n m)).
 { unfold B. apply iter_full__success_math. unfold simplex_init_basic.
   rewrite range_length__callee_bridge by lia. lia. }
 sep_apply_l_atomic HB.
 assert (HRT:iter_sepcon(map (fun i=>R i ** T i) (Zrange 0 m)) |--
 iter_sepcon(map R (Zrange 0 m)) ** iter_sepcon(map T (Zrange 0 m))).
 { apply solve_iter_split. intros; reflexivity. }
 sep_apply_l_atomic HRT.
 unfold simplex_pivot_memory,simplex_pivot_slots.
 rewrite map_app,logic_equiv_iter_sepcon_app,solve_iter_flat.
 assert (ER:iter_sepcon(map R (Zrange 0 m)) --||--
 iter_sepcon(map (fun k=>simplex_pivot_memory_cell s k
 (Znth k (simplex_check_initial_num a m n) 0) (Znth k (simplex_init_ones 400) 1)) (Zrange 0 m))).
 { apply solve_iter_equiv. intros i HI. apply In_Zrange in HI.
   rewrite check_init_pivot_rhs by lia. reflexivity. }
 rewrite <- ER.
 assert (ET:iter_sepcon(map T (Zrange 0 m)) --||--
 iter_sepcon(map (fun i=>iter_sepcon(map (fun k=>simplex_pivot_memory_cell s k
 (Znth k (simplex_check_initial_num a m n) 0) (Znth k (simplex_init_ones 400) 1))
 (map (fun j=>16+i*24+j) (Zrange 0 (m+n))))) (Zrange 0 m))).
 { apply solve_iter_equiv. intros i HI. apply In_Zrange in HI.
   unfold T,simplex_init_a_row. rewrite map_map.
   apply solve_iter_equiv. intros j HJ. apply In_Zrange in HJ.
   rewrite (proj2 (Z.ltb_lt j (m+n)) ltac:(lia)),check_init_pivot_a by lia.
   reflexivity. }
 rewrite <- ET. sepcon_right_assoc. cancel; reflexivity.
Qed.


Local Open Scope Z_scope.
Definition simplex_check_result (a:list Z) (m n limit q:Z)
 (on od ob oib ovn ovd:list Z) : Prop :=
 simplex_check_compute a m n limit =
 (q,Some (simplex_solve_pack on od ob oib ovn ovd)).
Lemma check_min_test : forall a m n,
 existsb (fun i=>existsb (fun j=>Znth(i*9+j) a 0 =? -2147483648)
 (Zrange 0 (n+1))) (Zrange 0 m)=true <->
 exists i j,0<=i<m /\ 0<=j<=n /\ Znth(i*9+j) a 0= -2147483648.
Proof.
 intros. rewrite existsb_exists. split.
 - intros [i [HI HE]]. apply In_Zrange in HI.
   apply existsb_exists in HE. destruct HE as [j [HJ HE]].
   apply In_Zrange in HJ. apply Z.eqb_eq in HE. exists i,j. repeat split;lia.
 - intros [i [j [HI [HJ HE]]]]. exists i. split; [apply In_Zrange;lia|].
   apply existsb_exists. exists j. split; [apply In_Zrange;lia|].
   apply Z.eqb_eq. exact HE.
Qed.
Lemma check_nonmin_test : forall a m n,
 (forall i j,0<=i<m -> 0<=j<=n -> Znth(i*9+j) a 0<> -2147483648) ->
 existsb (fun i=>existsb (fun j=>Znth(i*9+j) a 0 =? -2147483648)
 (Zrange 0 (n+1))) (Zrange 0 m)=false.
Proof.
 intros a m n H. apply Bool.not_true_is_false.
 rewrite check_min_test. intros [i [j [HI [HJ HE]]]]. apply (H i j HI HJ); auto.
Qed.
Lemma check_rejected_compute : forall a m n limit,
 (exists i j,0<=i<m /\ 0<=j<=n /\ Znth(i*9+j) a 0= -2147483648) ->
 simplex_check_compute a m n limit=(-1,None).
Proof. intros. unfold simplex_check_compute.
 rewrite (proj2 (check_min_test a m n) H). reflexivity. Qed.
Lemma check_solver_composition : forall a m n limit q on od ob oib ovn ovd,
 (forall i j,0<=i<m -> 0<=j<=n -> Znth(i*9+j) a 0<> -2147483648) ->
 simplex_solve_result
 (simplex_init_zeroes (m+n)) (simplex_init_flags n (m+n))
 (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))
 (simplex_init_zeroes (m+n)) (simplex_init_ones (m+n))
 m (m+n) limit (simplex_check_initial_num a m n) (simplex_init_ones 400)
 (simplex_init_basic n m) (simplex_init_flags n (m+n))
 (simplex_init_values a m n) (simplex_init_ones (m+n))
 q on od ob oib ovn ovd ->
 simplex_check_result a m n limit q on od ob oib ovn ovd.
Proof.
 intros a m n limit q on od ob oib ovn ovd HA HS.
 unfold simplex_check_result,simplex_check_compute.
 rewrite check_nonmin_test by auto. unfold simplex_solve_result in HS.
 unfold simplex_check_initial. rewrite HS. reflexivity.
Qed.
(* Six independent caller partitions are exhaustive: invalid dimensions;
   valid active MIN; otherwise zero/positive rows, each split by budget sign.
   No restriction is made on rawINT_MIN, zero inputs, or the int32 budget. *)
Lemma check_caller_partitions_exhaustive : forall a m n limit,
 (m<0 \/ 16<m \/ n<0 \/ 8<n) \/
 ((0<=m<=16 /\ 0<=n<=8) /\
 ((exists i j,0<=i<m /\ 0<=j<=n /\ Znth(i*9+j) a 0= -2147483648) \/
 ((forall i j,0<=i<m -> 0<=j<=n -> Znth(i*9+j) a 0<> -2147483648) /\
 ((m=0 /\ limit<0) \/ (m=0 /\ 0<=limit) \/
  (1<=m /\ limit<0) \/ (1<=m /\ 0<=limit))))).
Proof.
 intros. destruct (Z_lt_ge_dec m 0), (Z_lt_ge_dec 16 m),
 (Z_lt_ge_dec n 0), (Z_lt_ge_dec 8 n); try (left;lia).
 right. split; [lia|].
 destruct (existsb (fun i=>existsb (fun j=>Znth(i*9+j) a 0 =? -2147483648)
 (Zrange 0 (n+1))) (Zrange 0 m)) eqn:E.
 - left. apply check_min_test. exact E.
 - right. split.
   + intros i j HI HJ HE. assert (T: existsb (fun i=>existsb (fun j=>Znth(i*9+j) a 0 =? -2147483648)
     (Zrange 0 (n+1))) (Zrange 0 m)=true).
     { apply check_min_test. exists i,j. auto. } congruence.
   + destruct (Z.eq_dec m 0), (Z_lt_ge_dec limit 0); tauto || lia.
Qed.


Definition simplex_check_memory_snapshot := Z -> option Z.

Definition simplex_check_invalid_dimensions (m n:Z) : Prop :=
 m<0 \/ 16<m \/ n<0 \/ 8<n.
Lemma check_invalid_dimensions_exact : forall m n,
 simplex_check_invalid_dimensions m n <-> m<0 \/ 16<m \/ n<0 \/ 8<n.
Proof. reflexivity. Qed.

Local Open Scope Z_scope.
Lemma check_negative_compute : forall a m n limit,
 limit<0 ->
 (forall i j,0<=i<m -> 0<=j<=n -> Znth(i*9+j) a 0<> -2147483648) ->
 simplex_check_compute a m n limit=(-1,Some(simplex_check_initial a m n)).
Proof.
 intros. unfold simplex_check_compute. rewrite check_nonmin_test by auto.
 unfold simplex_solve_compute. rewrite (proj2 (Z.ltb_lt limit 0) H). reflexivity.
Qed.
Lemma check_zero_compute : forall a n limit,
 0<=limit -> simplex_check_compute a 0 n limit=(0,Some(simplex_check_initial a 0 n)).
Proof.
 intros a n limit HL.
 unfold simplex_check_compute. cbn [Zrange Zrange_aux existsb].
 assert (E:simplex_solve_compute
 (simplex_init_zeroes (0+n)) (simplex_init_flags n (0+n))
 (simplex_init_zeroes (0+n)) (simplex_init_ones (0+n))
 (simplex_init_zeroes (0+n)) (simplex_init_ones (0+n))
 0 (0+n) limit (simplex_check_initial a 0 n) =
 (0,simplex_check_initial a 0 n)).
 { apply solve_terminal_complete with (count:=0); try lia.
   unfold simplex_solve_tick,simplex_solve_prefix. cbn [Zrange Zrange_aux fold_left].
   unfold simplex_check_initial,simplex_solve_pack,simplex_solve_iteration,
    simplex_scan_compute. cbn [Zrange Zrange_aux fold_left].
   reflexivity. }
 rewrite E. reflexivity.
Qed.

(* Canonical padding is a logical projection of active input coefficients,
   independent of the physical inactive snapshot CO. Inactive C may contain
   INT_MIN or be unknown. This projection never loads those physical cells. *)
Definition simplex_check_coefficients (raw:list Z) (m n:Z) : list Z :=
 map (fun k=>if k mod 9 <=? n then Znth k raw 0 else 0) (Zrange 0 (m*9)).
Lemma check_coefficients_active : forall raw m n i j,
 0<=i<m -> 0<=j<=n -> n<=8 ->
 Znth(i*9+j) (simplex_check_coefficients raw m n) 0=Znth(i*9+j) raw 0.
Proof.
 intros. unfold simplex_check_coefficients. rewrite check_map_nth by lia.
 replace (i*9+j) with (j+i*9) at 1 by ring.
 rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
 rewrite (proj2 (Z.leb_le j n) ltac:(lia)). reflexivity.
Qed.
Lemma check_coefficients_range : forall raw m n lo hi,
 0<=m -> 0<=n<=8 -> lo<=0<=hi ->
 (forall i j,0<=i<m -> 0<=j<=n -> lo<=Znth(i*9+j) raw 0<=hi) ->
 Zlength(simplex_check_coefficients raw m n)=m*9 /\
 Forall (Z.le lo) (simplex_check_coefficients raw m n) /\
 Forall (Z.ge hi) (simplex_check_coefficients raw m n).
Proof.
 intros raw m n lo hi HM HN HB HA.
 unfold simplex_check_coefficients. rewrite Zlength_map,simplex_scan_range_length by lia.
 split; [reflexivity|].
 assert (HP:forall x,In x (map (fun k=>if k mod 9 <=? n then Znth k raw 0 else 0) (Zrange 0 (m*9))) -> lo<=x<=hi).
 { intros x HX. apply in_map_iff in HX. destruct HX as [k [<- HK]].
   apply In_Zrange in HK. destruct (k mod 9 <=? n) eqn:E; [apply Z.leb_le in E|lia].
   assert (HI:0<=k/9<m) by (split; [apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]).
   assert (HJ:0<=k mod 9<=n) by (pose proof (Z.mod_pos_bound k 9 ltac:(lia));lia).
   replace k with ((k/9)*9+k mod 9) by (pose proof (Z.div_mod k 9 ltac:(lia));nia).
   apply HA; auto. }
 split; apply Forall_forall; intros x HX; specialize (HP x HX); lia.
Qed.


Local Open Scope sac.
Lemma check_initial_unknown_vars_independent : forall s n v a,
 0<=v ->
 simplex_init_vars s n 0 0 v a 0 --||--
 simplex_init_vars s n 0 0 v nil 0.
Proof.
 intros. unfold simplex_init_vars. apply solve_iter_equiv.
 intros j HJ. apply In_Zrange in HJ. unfold simplex_init_var.
 rewrite (proj2 (Z.ltb_ge j 0) ltac:(lia)). reflexivity.
Qed.
Lemma check_initial_unknown_rows_independent : forall s n m v a,
 0<=m -> 0<=v ->
 simplex_init_rows s a n 0 m v --||-- simplex_init_rows s nil n 0 m v.
Proof.
 intros. unfold simplex_init_rows. apply solve_iter_equiv.
 intros i HI. apply In_Zrange in HI. unfold simplex_init_row.
 rewrite (proj2 (Z.ltb_ge i 0) ltac:(lia)).
 unfold simplex_init_a_row.
 assert (E:iter_sepcon(map (fun j=>if j<?0 then simplex_init_a_cell s a n i j else simplex_init_a_undef s i j) (Zrange 0 v)) --||--
 iter_sepcon(map (fun j=>if j<?0 then simplex_init_a_cell s nil n i j else simplex_init_a_undef s i j) (Zrange 0 v))).
 { apply solve_iter_equiv. intros j HJ. apply In_Zrange in HJ.
   rewrite (proj2 (Z.ltb_ge j 0) ltac:(lia)). reflexivity. }
 rewrite E. reflexivity.
Qed.
Lemma check_old_initialize_matrix : forall s m n old a,
 0<=m -> 0<=n ->
 simplex_check_old s m n old |--
 (&(s #"SxState" ->ₛ "rows")) # Int |->_ **
 (&(s #"SxState" ->ₛ "inputs")) # Int |->_ **
 (&(s #"SxState" ->ₛ "vars")) # Int |->_ **
 simplex_init_vars s n 0 0 (m+n) a 0 **
 simplex_init_rows s a n 0 m (m+n).
Proof.
 intros. rewrite check_initial_unknown_vars_independent by lia.
 rewrite check_initial_unknown_rows_independent by lia.
 apply check_old_initialize; auto.
Qed.


(* Rejected input exposes the empty-update result with no state snapshot
   payload. The old object remains outside the accessed footprint. *)
Definition simplex_check_rejected_result (a:list Z) (m n limit q:Z) : Prop :=
 simplex_check_compute a m n limit=(q,None).

(* Footprint completeness: all 1035 named int members, and all 144 input
   cells, are partitioned by the displayed active/inactive index ranges.
   This counts members only; no struct padding-byte claim is introduced. *)
Local Open Scope Z_scope.
Lemma check_flat_map_length : forall (xs:list Z) (f:Z->list Z) k,
 (forall x,In x xs -> Zlength(f x)=k) ->
 Zlength(flat_map f xs)=k*Zlength xs.
Proof.
 induction xs as [|x xs IH]; intros f k H.
 - cbn [flat_map]. rewrite Zlength_nil. ring.
 - cbn [flat_map]. rewrite Zlength_app,Zlength_cons.
   rewrite (H x (or_introl eq_refl)), (IH f k ltac:(intros;apply H;right;auto)).
   ring.
Qed.
Lemma check_var_addresses_length : forall s j,
 Zlength(simplex_check_var_addresses s j)=9.
Proof. reflexivity. Qed.
Lemma check_a_addresses_length : forall s i j,
 Zlength(simplex_check_a_addresses s i j)=2.
Proof. reflexivity. Qed.
Lemma check_row_addresses_length : forall s i,
 Zlength(simplex_check_row_addresses s i)=3.
Proof. reflexivity. Qed.
Lemma check_a_rows_length : forall s i lo hi,
 lo<=hi ->
 Zlength(flat_map (simplex_check_a_addresses s i) (Zrange lo hi))=2*(hi-lo).
Proof.
 intros. rewrite (check_flat_map_length _ _ 2 ltac:(intros;apply check_a_addresses_length)).
 rewrite range_length__callee_bridge by auto. reflexivity.
Qed.
Lemma check_state_footprint_count : forall s m n,
 0<=m<=16 -> 0<=n<=8 ->
 Zlength(simplex_check_active_addresses s m n)+
 Zlength(simplex_check_frame_addresses s m n)=1035.
Proof.
 intros s m n HM HN.
 unfold simplex_check_active_addresses,simplex_check_frame_addresses.
 rewrite !Zlength_app.
 rewrite (check_flat_map_length _ (simplex_check_var_addresses s) 9 ltac:(intros;apply check_var_addresses_length)).
 rewrite (check_flat_map_length _ (simplex_check_var_addresses s) 9 ltac:(intros;apply check_var_addresses_length)).
 rewrite (check_flat_map_length _ (fun i=>simplex_check_row_addresses s i ++ flat_map (simplex_check_a_addresses s i) (Zrange 0 (m+n))) (3+2*(m+n))
 ltac:(intros;cbn beta;rewrite Zlength_app,check_row_addresses_length,check_a_rows_length by lia;lia)).
 rewrite (check_flat_map_length _ (fun i=>simplex_check_row_addresses s i ++ flat_map (simplex_check_a_addresses s i) (Zrange 0 24)) 51
 ltac:(intros;cbn beta;rewrite Zlength_app,check_row_addresses_length,check_a_rows_length by lia;lia)).
 rewrite (check_flat_map_length _ (fun i=>flat_map (simplex_check_a_addresses s i) (Zrange (m+n) 24)) (2*(24-(m+n)))
 ltac:(intros;apply check_a_rows_length;lia)).
 rewrite !range_length__callee_bridge by lia.
 change (Zlength (simplex_check_scalars s)) with 3.
 ring.
Qed.



Lemma init_identity_wand__initialize_adapters : forall (k:Z),
 emp |-- ALL retval:Z, (“ simplex_init_return retval k ” && emp) -* (“ simplex_init_return retval k ” && emp).
Proof.
 intros k. Intros_r retval. apply_sepcon_adjoint. elim_emp. cancel; reflexivity.
Qed.
