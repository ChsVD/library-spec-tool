From Coq Require Import ZArith List Lia String.
From SimpleC.EE.Applications_human.simplex_check Require Export simplex_check_lib.
Import ListNotations naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string_scope.
(* Finite typed read support enumerates physical cells once; traversal may
   revisit them. Only existing iter_sepcon/store primitives are used. *)
Definition simplex_deduction_ptrs (ps:list Z) (v:Z->Z) : Assertion :=
 iter_sepcon (map (fun p=>p # Ptr |-> (v p)) ps).
Definition simplex_deduction_ints (ps:list Z) (v:Z->Z) : Assertion :=
 iter_sepcon (map (fun p=>p # Int |-> (v p)) ps).
Definition simplex_deduction_coef_address (p:Z) := &(p #"InequList" ->ₛ "coef").
Definition simplex_deduction_next_address (p:Z) := &(p #"InequList" ->ₛ "next").
(* Reversible focus preserves the whole support after each typed read. *)
Lemma deduction_support_focus : forall (f:Z->Assertion) ps p,
 In p ps -> iter_sepcon(map f ps) |--
 f p ** (f p -* iter_sepcon(map f ps)).
Proof.
 intros f ps p H. apply in_split in H. destruct H as [xs [ys ->]].
 rewrite map_app,logic_equiv_iter_sepcon_app.
 cbn [map]. rewrite logic_equiv_iter_sepcon_cons.
 sepcon_right_assoc.
 assert (HR:iter_sepcon(map f xs) ** iter_sepcon(map f ys) |--
 f p -* (iter_sepcon(map f xs) ** (f p ** iter_sepcon(map f ys)))).
 { apply_sepcon_adjoint. sepcon_right_assoc. cancel; reflexivity. }
 sep_apply_r_atomic HR. cancel; reflexivity.
Qed.
Lemma deduction_ptr_focus : forall ps v p,
 In p ps -> simplex_deduction_ptrs ps v |--
 p # Ptr |-> (v p) ** (p # Ptr |-> (v p) -* simplex_deduction_ptrs ps v).
Proof. intros. unfold simplex_deduction_ptrs. exact (deduction_support_focus (fun x=>x # Ptr |-> (v x)) ps p H). Qed.
Lemma deduction_int_focus : forall ps v p,
 In p ps -> simplex_deduction_ints ps v |--
 p # Int |-> (v p) ** (p # Int |-> (v p) -* simplex_deduction_ints ps v).
Proof. intros. unfold simplex_deduction_ints. exact (deduction_support_focus (fun x=>x # Int |-> (v x)) ps p H). Qed.
Lemma deduction_read_restore : forall (P R:Assertion), P ** (P -* R) |-- R.
Proof. intros. apply derivable1_wand_elim2. Qed.

Local Open Scope Z_scope.
(* Canonical finite enumeration removes repeated physical addresses only;
   no distinctness is imposed on the linked-list visit sequence. *)
Definition simplex_deduction_unique (ps:list Z) := nodup Z.eq_dec ps.
Lemma deduction_unique_nodup : forall ps, NoDup(simplex_deduction_unique ps).
Proof. intros. apply NoDup_nodup. Qed.
Lemma deduction_unique_in : forall ps p,
 In p (simplex_deduction_unique ps) <-> In p ps.
Proof. intros. apply nodup_In. Qed.
(* Physical copy view: r complete rows and j cells in the current row.
   Inactive columns and uncopied rows keep unknown typed permissions. *)
Definition simplex_deduction_copy_cell (c:Z) (a:list Z) (n r j k:Z) : Assertion :=
 if andb (orb (k/9 <? r) (andb (k/9 =? r) (k mod 9 <? j))) (k mod 9 <=? n)
 then (c+k*sizeof(INT)) # Int |-> (Znth k a 0)
 else (c+k*sizeof(INT)) # Int |->_.
Definition simplex_deduction_copy (c:Z) (a:list Z) (n r j:Z) : Assertion :=
 iter_sepcon(map (simplex_deduction_copy_cell c a n r j) (Zrange 0 144)).
Definition simplex_deduction_copy_except (c:Z) (a:list Z) (n r j k:Z) : Assertion :=
 iter_sepcon(remove_Znth k
 (map (simplex_deduction_copy_cell c a n r j) (Zrange 0 144))).
Lemma deduction_copy_focus : forall c a n r j k,
 0<=k<144 ->
 simplex_deduction_copy c a n r j --||--
 simplex_deduction_copy_cell c a n r j k **
 simplex_deduction_copy_except c a n r j k.
Proof.
 intros. unfold simplex_deduction_copy,simplex_deduction_copy_except.
 rewrite (iter_sepcon_remove_nth (Z.to_nat k) _ emp)
 by (rewrite length_map; pose proof (simplex_scan_range_length 144 ltac:(lia)) as HL; rewrite Zlength_correct in HL; lia).
 change (nth (Z.to_nat k) _ emp) with
 (Znth k (map (simplex_deduction_copy_cell c a n r j) (Zrange 0 144)) emp).
 rewrite (Znth_map _ _ _ 0 emp)
 by (rewrite simplex_scan_range_length;lia).
 rewrite simplex_scan_range_nth by lia. reflexivity.
Qed.

Definition simplex_deduction_unknown : simplex_check_memory_snapshot := fun _=>None.

(* Closing a copied row changes the cursor, never the physical padding. *)
Lemma deduction_copy_row_complete : forall c a n r,
 0<=n<=8 -> 0<=r<16 ->
 simplex_deduction_copy c a n r (n+1) --||--
 simplex_deduction_copy c a n (r+1) 0.
Proof.
 intros. unfold simplex_deduction_copy. apply solve_iter_equiv.
 intros k HK. apply In_Zrange in HK.
 unfold simplex_deduction_copy_cell.
 assert (E:andb (orb (k/9 <? r) (andb (k/9 =? r) (k mod 9 <? n+1))) (k mod 9 <=? n) =
 andb (orb (k/9 <? r+1) (andb (k/9 =? r+1) (k mod 9 <? 0))) (k mod 9 <=? n)).
 { apply Bool.eq_true_iff_eq.
   repeat first [rewrite Bool.andb_true_iff | rewrite Bool.orb_true_iff | rewrite Z.ltb_lt | rewrite Z.eqb_eq | rewrite Z.leb_le].
   pose proof (Z.mod_pos_bound k 9 ltac:(lia)). lia. }
 rewrite E. reflexivity.
Qed.
(* A local array begins with unknown permissions even when logical A has
   canonical zero padding. *)
Lemma deduction_copy_initial_cells : forall c a n k,
 0<=k<144 -> simplex_deduction_copy_cell c a n 0 0 k =
 (c+k*sizeof(INT)) # Int |->_.
Proof.
 intros. unfold simplex_deduction_copy_cell.
 rewrite (proj2 (Z.ltb_ge (k/9) 0) ltac:(apply Z.div_pos;lia)).
 rewrite (proj2 (Z.ltb_ge (k mod 9) 0) ltac:(pose proof(Z.mod_pos_bound k 9 ltac:(lia));lia)).
 destruct (k/9 =? 0); destruct (k mod 9 <=? n); reflexivity.
Qed.

(* The next destination is unknown before copying and exactly A afterwards. *)
Lemma deduction_copy_cell_before : forall c a n r j,
 0<=r -> 0<=j<=n -> n<=8 ->
 simplex_deduction_copy_cell c a n r j (r*9+j) =
 (c+(r*9+j)*sizeof(INT)) # Int |->_.
Proof.
 intros. unfold simplex_deduction_copy_cell.
 assert (HD:(r*9+j)/9=r).
 { replace (r*9+j) with (j+r*9) by ring.
   rewrite Z.div_add,Z.div_small by lia. lia. }
 assert (HM:(r*9+j) mod 9=j).
 { replace (r*9+j) with (j+r*9) by ring.
   rewrite Z.mod_add,Z.mod_small by lia. reflexivity. }
 rewrite HD,HM,Z.ltb_irrefl,Z.eqb_refl,Z.ltb_irrefl. reflexivity.
Qed.
Lemma deduction_copy_cell_after : forall c a n r j,
 0<=r -> 0<=j<=n -> n<=8 ->
 simplex_deduction_copy_cell c a n r (j+1) (r*9+j) =
 (c+(r*9+j)*sizeof(INT)) # Int |-> (Znth(r*9+j) a 0).
Proof.
 intros. unfold simplex_deduction_copy_cell.
 assert (HD:(r*9+j)/9=r).
 { replace (r*9+j) with (j+r*9) by ring.
   rewrite Z.div_add,Z.div_small by lia. lia. }
 assert (HM:(r*9+j) mod 9=j).
 { replace (r*9+j) with (j+r*9) by ring.
   rewrite Z.mod_add,Z.mod_small by lia. reflexivity. }
 rewrite HD,HM,Z.ltb_irrefl,Z.eqb_refl.
 rewrite (proj2(Z.ltb_lt j (j+1)) ltac:(lia)).
 rewrite (proj2(Z.leb_le j n) ltac:(lia)). reflexivity.
Qed.
Lemma deduction_copy_cell_frame : forall c a n r j k,
 k<>r*9+j ->
 simplex_deduction_copy_cell c a n r j k =
 simplex_deduction_copy_cell c a n r (j+1) k.
Proof.
 intros. unfold simplex_deduction_copy_cell.
 assert (E:andb (orb (k/9 <? r) (andb (k/9 =? r) (k mod 9 <? j))) (k mod 9 <=? n) =
 andb (orb (k/9 <? r) (andb (k/9 =? r) (k mod 9 <? j+1))) (k mod 9 <=? n)).
 { apply Bool.eq_true_iff_eq.
   repeat first [rewrite Bool.andb_true_iff | rewrite Bool.orb_true_iff |
    rewrite Z.ltb_lt | rewrite Z.eqb_eq | rewrite Z.leb_le].
   pose proof (Z.div_mod k 9 ltac:(lia)). nia. }
 rewrite E. reflexivity.
Qed.


(* Caller workspace: only the active rectangle is owned. A visit may be repeated
   in the read support; workspace remains separate. Uncopied cells are unknown. *)
Definition simplex_deduction_workspace_cell (c:Z) (a:list Z) (r j i h:Z) : Assertion :=
 if orb (i <? r) (andb (i =? r) (h <? j))
 then simplex_init_input_cell c a i h
 else (c+i*(sizeof(INT)*9)+h*sizeof(INT)) # Int |->_.
Definition simplex_deduction_workspace (c:Z) (a:list Z) (m n r j:Z) : Assertion :=
 iter_sepcon(map (fun i=>iter_sepcon(map
 (simplex_deduction_workspace_cell c a r j i) (Zrange 0 (n+1)))) (Zrange 0 m)).
Lemma deduction_workspace_complete : forall c a m n,
 simplex_deduction_workspace c a m n m 0 --||-- simplex_init_input c a m n.
Proof.
 intros. unfold simplex_deduction_workspace,simplex_init_input.
 apply solve_iter_equiv. intros i Hi. apply In_Zrange in Hi.
 apply solve_iter_equiv. intros h Hh.
 unfold simplex_deduction_workspace_cell.
 rewrite (proj2(Z.ltb_lt i m) ltac:(lia)). reflexivity.
Qed.
Lemma deduction_workspace_zero : forall c a n r j,
 simplex_deduction_workspace c a 0 n r j = emp.
Proof. intros. reflexivity. Qed.

Definition simplex_deduction_workspace_except (c:Z) (a:list Z) (m n r j:Z) : Assertion :=
 iter_sepcon(remove_Znth r (map (fun i=>iter_sepcon(map
 (simplex_deduction_workspace_cell c a r j i) (Zrange 0 (n+1)))) (Zrange 0 m))) **
 iter_sepcon(remove_Znth j (map (simplex_deduction_workspace_cell c a r j r) (Zrange 0 (n+1)))).

(* Removing one physical support cell gives a first-order residual consumable
   by the C frontend; no new spatial primitive is introduced. *)
Definition simplex_deduction_ptrs_without (ps:list Z) (v:Z->Z) (p:Z) : Assertion :=
 simplex_deduction_ptrs (remove Z.eq_dec p ps) v.
Definition simplex_deduction_ints_without (ps:list Z) (v:Z->Z) (p:Z) : Assertion :=
 simplex_deduction_ints (remove Z.eq_dec p ps) v.
Lemma deduction_support_remove : forall (f:Z->Assertion) ps p,
 NoDup ps -> In p ps ->
 iter_sepcon(map f ps) --||-- f p ** iter_sepcon(map f (remove Z.eq_dec p ps)).
Proof.
 intros f ps. induction ps as [|a ps IH]; intros p HN HI; [contradiction|].
 inversion HN as [|? ? Hnot Htail]; subst.
 destruct HI as [E|HI].
 - subst a. simpl. destruct (Z.eq_dec p p); [|contradiction].
   rewrite notin_remove by exact Hnot.
   rewrite logic_equiv_iter_sepcon_cons. reflexivity.
 - assert (Hne:a<>p) by (intro E; subst; contradiction).
   simpl. destruct (Z.eq_dec p a); [congruence|].
   rewrite !logic_equiv_iter_sepcon_cons.
   rewrite (IH p Htail HI). cbn [map].
   rewrite logic_equiv_iter_sepcon_cons. apply logic_equiv_sepcon_swap.
Qed.


Lemma workspace_focus__workspace_focus : forall c a m n r j,
 0<=r<m -> 0<=j<=n ->
 simplex_deduction_workspace c a m n r j --||--
 (c+r*(sizeof(INT)*9)+j*sizeof(INT)) # Int |->_ **
 simplex_deduction_workspace_except c a m n r j.
Proof.
 intros c a m n r j Hr Hj.
 unfold simplex_deduction_workspace,simplex_deduction_workspace_except.
 rewrite (iter_sepcon_remove_nth (Z.to_nat r) _ emp)
 by (rewrite length_map; pose proof(simplex_scan_range_length m ltac:(lia)) as HL; rewrite Zlength_correct in HL;lia).
 change (nth (Z.to_nat r) _ emp) with
 (Znth r (map (fun i=>iter_sepcon(map (simplex_deduction_workspace_cell c a r j i) (Zrange 0 (n+1)))) (Zrange 0 m)) emp).
 rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length;lia).
 rewrite simplex_scan_range_nth by lia.
 rewrite (iter_sepcon_remove_nth (Z.to_nat j) _ emp)
 by (rewrite length_map;pose proof(simplex_scan_range_length (n+1) ltac:(lia)) as HL;rewrite Zlength_correct in HL;lia).
 change (nth (Z.to_nat j) _ emp) with
 (Znth j (map (simplex_deduction_workspace_cell c a r j r) (Zrange 0 (n+1))) emp).
 rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length;lia).
 rewrite simplex_scan_range_nth by lia.
 unfold simplex_deduction_workspace_cell at 1.
 rewrite Z.ltb_irrefl,Z.eqb_refl,Z.ltb_irrefl. cbn [orb andb].
 unfold remove_Znth. split; sepcon_right_assoc; cancel;reflexivity.
Qed.
Lemma removed_nth_notin__workspace_update : forall (xs:list Z) i d,
 NoDup xs -> (i<List.length xs)%nat -> ~In (nth i xs d) (remove_nth i xs).
Proof.
 induction xs as [|x xs IH]; intros [|i] d HN HB; simpl in *; try lia.
 - inversion HN; assumption.
 - inversion HN as [|? ? Hnot HT]; subst.
   intros [E|HI].
   + apply Hnot. rewrite E. apply nth_In. lia.
   + exact (IH i d HT ltac:(lia) HI).
Qed.
Lemma workspace_cell_frame__workspace_update : forall c a r j i h,
 i<>r \/ h<>j ->
 simplex_deduction_workspace_cell c a r j i h =
 simplex_deduction_workspace_cell c a r (j+1) i h.
Proof.
 intros. unfold simplex_deduction_workspace_cell.
 assert (E:orb (i <? r) (andb (i =? r) (h <? j)) =
 orb (i <? r) (andb (i =? r) (h <? j+1))).
 { apply Bool.eq_true_iff_eq.
 repeat first [rewrite Bool.orb_true_iff | rewrite Bool.andb_true_iff |
 rewrite Z.ltb_lt | rewrite Z.eqb_eq]. lia. }
 rewrite E. reflexivity.
Qed.
Lemma workspace_update__workspace_update : forall c a m n r j,
 0<=r<m -> 0<=j<=n -> n<=8 ->
 (c+r*(sizeof(INT)*9)+j*sizeof(INT)) # Int |-> (Znth(r*9+j) a 0) **
 simplex_deduction_workspace_except c a m n r j |--
 simplex_deduction_workspace c a m n r (j+1).
Proof.
 intros c a m n r j Hr Hj Hn.
 unfold simplex_deduction_workspace_except,simplex_deduction_workspace.
 assert (HO:remove_Znth r (map (fun i => iter_sepcon(map
 (simplex_deduction_workspace_cell c a r j i) (Zrange 0 (n+1)))) (Zrange 0 m)) =
 remove_Znth r (map (fun i => iter_sepcon(map
 (simplex_deduction_workspace_cell c a r (j+1) i) (Zrange 0 (n+1)))) (Zrange 0 m))).
 { rewrite <- !map_remove_Znth. apply map_ext_in. intros i HI.
   apply f_equal. apply map_ext_in. intros h HH.
   apply workspace_cell_frame__workspace_update. left.
   assert (HN:~In r (remove_Znth r (Zrange 0 m))).
   { unfold remove_Znth. replace r with (nth (Z.to_nat r) (Zrange 0 m) 0) at 1.
     apply removed_nth_notin__workspace_update.
     apply NoDup_Zrange.
     pose proof(simplex_scan_range_length m ltac:(lia)); rewrite Zlength_correct in H; lia.
     change (Znth r (Zrange 0 m) 0=r). apply simplex_scan_range_nth;lia. }
   congruence. }
 assert (HI:remove_Znth j (map (simplex_deduction_workspace_cell c a r j r) (Zrange 0 (n+1))) =
 remove_Znth j (map (simplex_deduction_workspace_cell c a r (j+1) r) (Zrange 0 (n+1)))).
 { rewrite <- !map_remove_Znth. apply map_ext_in. intros h HH.
   apply workspace_cell_frame__workspace_update. right.
   assert (HN:~In j (remove_Znth j (Zrange 0 (n+1)))).
   { unfold remove_Znth. replace j with (nth (Z.to_nat j) (Zrange 0 (n+1)) 0) at 1.
     apply removed_nth_notin__workspace_update. apply NoDup_Zrange.
     pose proof(simplex_scan_range_length (n+1) ltac:(lia)); rewrite Zlength_correct in H;lia.
     change (Znth j (Zrange 0 (n+1)) 0=j). apply simplex_scan_range_nth;lia. }
   congruence. }
 rewrite HO,HI.
 rewrite (iter_sepcon_remove_nth (Z.to_nat r) (map (fun i=>iter_sepcon(map (simplex_deduction_workspace_cell c a r (j+1) i) (Zrange 0 (n+1)))) (Zrange 0 m)) emp)
 by (rewrite length_map;pose proof(simplex_scan_range_length m ltac:(lia));rewrite Zlength_correct in H;lia).
 change (nth (Z.to_nat r) _ emp) with (Znth r (map (fun i=>iter_sepcon(map (simplex_deduction_workspace_cell c a r (j+1) i) (Zrange 0 (n+1)))) (Zrange 0 m)) emp).
 rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length;lia).
 rewrite simplex_scan_range_nth by lia.
 rewrite (iter_sepcon_remove_nth (Z.to_nat j) (map (simplex_deduction_workspace_cell c a r (j+1) r) (Zrange 0 (n+1))) emp)
 by (rewrite length_map;pose proof(simplex_scan_range_length (n+1) ltac:(lia));rewrite Zlength_correct in H;lia).
 change (nth (Z.to_nat j) _ emp) with (Znth j (map (simplex_deduction_workspace_cell c a r (j+1) r) (Zrange 0 (n+1))) emp).
 rewrite (Znth_map _ _ _ 0 emp) by (rewrite simplex_scan_range_length;lia).
 rewrite simplex_scan_range_nth by lia.
 unfold simplex_deduction_workspace_cell.
 rewrite Z.ltb_irrefl,Z.eqb_refl,(proj2(Z.ltb_lt j (j+1)) ltac:(lia)).
 unfold simplex_init_input_cell,remove_Znth. cbn. sepcon_right_assoc. cancel; reflexivity.
Qed.
Lemma workspace_row_close__row_advance : forall c a m n r,
 0<=n -> 0<=r<m ->
 simplex_deduction_workspace c a m n r (n+1) --||--
 simplex_deduction_workspace c a m n (r+1) 0.
Proof.
 intros c a m n r Hn Hr.
 unfold simplex_deduction_workspace.
 apply solve_iter_equiv. intros i Hi. apply In_Zrange in Hi.
 apply solve_iter_equiv. intros h Hh. apply In_Zrange in Hh.
 unfold simplex_deduction_workspace_cell.
 assert (E:orb (i <? r) (andb (i =? r) (h <? n+1)) =
 orb (i <? r+1) (andb (i =? r+1) (h <? 0))).
 { apply Bool.eq_true_iff_eq.
   repeat first [rewrite Bool.orb_true_iff | rewrite Bool.andb_true_iff |
     rewrite Z.ltb_lt | rewrite Z.eqb_eq]. lia. }
 rewrite E. reflexivity.
Qed.
