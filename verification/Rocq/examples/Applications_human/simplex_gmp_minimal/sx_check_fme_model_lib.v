From Coq Require Import ZArith List QArith.
From AUXLib Require Import ListLib.
From SumLib Require Import ZRange.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_lib.

Local Open Scope Z_scope.

(* Integer rows contain the constant followed by n coefficients. A valuation
   is observed only on [0,n), and feasibility checks exactly the first m rows. *)
Definition sx_rationally_feasible (n m : Z) (matrix : list Constraint) : Prop :=
  exists x : Z -> Q,
    forall r, 0 <= r < m ->
      let row := Znth r matrix (list_Constraint nil) in
      (inject_Z (coef_Znth 0%Z row 0%Z) +
       fold_right Qplus 0
         (map (fun v => inject_Z (coef_Znth (v + 1)%Z row 0%Z) * x v)
           (Zrange 0%Z n)) <= 0)%Q.

(* The normal-return code classifies the original input over the rationals. *)
Definition sx_check_result (n m : Z) (matrix : list Constraint) (ret : Z) : Prop :=
  ((ret = 0 \/ ret = 1) /\
   (ret = 0 <-> sx_rationally_feasible n m matrix) /\
   (ret = 1 <-> ~ sx_rationally_feasible n m matrix))%type.


From Coq Require Import Lia.
Lemma selection_basic_satisfies_table__feasible_return
    (m k sentinel : Z) (D C A B R : list Z) (x : Z -> Q) :
  m <= k ->
  k < sentinel ->
  ((forall r, 0 <= r < m ->
      0 <= Znth r B 0 < k /\ Znth (Znth r B 0) R 0 = r /\ 0 < Znth r D 0) /\
   (forall v, 0 <= v < k -> Znth v R 0 <> sentinel ->
      0 <= Znth v R 0 < m /\ Znth (Znth v R 0) B 0 = v) /\
   (forall r q, 0 <= r < m -> 0 <= q < m ->
      Znth (r * k + Znth q B 0) A 0 = 0)) ->
  (forall v, x v =
     if Z.eqb (Znth v R 0) sentinel then 0%Q
     else (inject_Z (Znth (Znth v R 0%Z) C 0%Z) /
           inject_Z (Znth (Znth v R 0%Z) D 0%Z))%Q) ->
  forall r, 0 <= r < m ->
    (inject_Z (Znth r D 0%Z) * x (Znth r B 0%Z) ==
     inject_Z (Znth r C 0%Z) +
     fold_right Qplus 0
       (map (fun v => inject_Z (Znth (r * k + v)%Z A 0%Z) * x v)
         (Zrange 0%Z k)))%Q.
Proof.
  intros Hmk Hsentinel [Hbasic [Hlookup Hzero]] Hvalue r Hr.
  destruct (Hbasic r Hr) as [_ [Hrow Hd]].
  assert (Hterm : forall v, In v (Zrange 0 k) ->
      (inject_Z (Znth (r * k + v)%Z A 0%Z) * x v == 0)%Q).
  { intros v Hv.
    apply In_Zrange in Hv.
    rewrite Hvalue.
    destruct (Z.eqb_spec (Znth v R 0) sentinel) as [Heq|Hne].
    - apply Qmult_0_r.
    - destruct (Hlookup v Hv Hne) as [Hq Hcolumn].
      rewrite <- Hcolumn at 1.
      rewrite Hzero by assumption.
      apply Qmult_0_l. }
  assert (Hfold : forall columns : list Z,
    (forall v, In v columns ->
      (inject_Z (Znth (r * k + v)%Z A 0%Z) * x v == 0)%Q) ->
    (fold_right Qplus 0
       (map (fun v => inject_Z (Znth (r * k + v)%Z A 0%Z) * x v)
         columns) == 0)%Q).
  { induction columns as [|v columns IH]; intros Hcolumns.
    - reflexivity.
    - simpl. rewrite Hcolumns by (left; reflexivity).
      rewrite IH by (intros w Hw; apply Hcolumns; right; exact Hw).
      apply Qplus_0_l. }
  rewrite (Hfold _ Hterm), Qplus_0_r, Hvalue, Hrow.
  destruct (Z.eqb_spec r sentinel) as [Heq|Hne]; [lia |].
  apply Qmult_div_r.
  change (~ (inject_Z (Znth r D 0%Z) == inject_Z 0%Z)%Q).
  rewrite inject_Z_injective. lia.
Qed.
Lemma sx_feasible_valuation_extends__infeasible_return n m k I :
  k = m + n ->
  sx_rationally_feasible n m I ->
  exists y : Z -> Q,
    (forall v, n <= v < k -> (y v <= 0)%Q) /\
    (forall r, 0 <= r < m ->
      let row := Znth r I (list_Constraint nil) in
      (y (n + r)%Z == inject_Z (coef_Znth 0%Z row 0%Z) +
       fold_right Qplus 0
         (map (fun v => inject_Z (coef_Znth (v + 1)%Z row 0%Z) * y v)
           (Zrange 0%Z n)))%Q).
Proof.
  intros Hk [x Hfeasible].
  set (row_value := fun r =>
    let row := Znth r I (list_Constraint nil) in
    (inject_Z (coef_Znth 0%Z row 0%Z) +
     fold_right Qplus 0
       (map (fun v => inject_Z (coef_Znth (v + 1)%Z row 0%Z) * x v)
         (Zrange 0%Z n)))%Q).
  set (y := fun v => if (v <? n)%Z then x v else row_value (v - n)).
  assert (Haux : forall v, n <= v -> y v = row_value (v - n)).
  { intros v Hv. unfold y.
    assert ((v <? n)%Z = false) as Hlt by (apply Z.ltb_ge; exact Hv).
    rewrite Hlt. reflexivity. }
  exists y. split.
  - intros v Hv. rewrite Haux by lia.
    apply Hfeasible. lia.
  - intros r Hr. cbn zeta.
    rewrite Haux by lia.
    replace (n + r - n) with r by lia.
    unfold row_value. cbn zeta.
    assert (Hterms :
      map (fun v => (inject_Z (coef_Znth (v + 1)%Z
          (Znth r I (list_Constraint nil)) 0%Z) * x v)%Q) (Zrange 0 n) =
      map (fun v => (inject_Z (coef_Znth (v + 1)%Z
          (Znth r I (list_Constraint nil)) 0%Z) * y v)%Q) (Zrange 0 n)).
    { apply map_ext_in. intros v Hv.
      apply <- In_Zrange in Hv.
      unfold y.
      assert ((v <? n)%Z = true) as Hlt by (apply Z.ltb_lt; lia).
      rewrite Hlt. reflexivity. }
    rewrite Hterms. reflexivity.
Qed.
Lemma uint_cell_to_uchar_segment__array_bridges :
  forall p i,
    SeparationLogic.naive_C_Rules.derivable1
      (SeparationLogic.naive_C_Rules.StoreUIntAsElement.undefstoreA p i)
      (SeparationLogic.naive_C_Rules.UCharArray.undef_seg p (4 * i) (4 * (i + 1))).
Proof.
  intros p i.
  pose proof SeparationLogic.naive_C_Rules.logic_equiv_proper_derivable1.
  pose proof SeparationLogic.naive_C_Rules.logic_equiv_sepcon_proper.
  pose proof SeparationLogic.naive_C_Rules.logic_equiv_andp_proper.
  pose proof SeparationLogic.naive_C_Rules.logic_equiv_symm_instance.
  unfold SeparationLogic.naive_C_Rules.StoreUIntAsElement.undefstoreA.
  rewrite SeparationLogic.naive_C_Rules.sizeof_uint.
  replace (i * 4) with (4 * i) by lia.
  SeparationLogic.naive_C_Rules.sep_apply_r_aux
    (proj2 (SeparationLogic.naive_C_Rules.UCharArray.undef_seg_0_shift
      p (4 * i) (4 * (i + 1)))).
  change SeparationLogic.naive_C_Rules.StoreUCharAsElement.sizeA with 1.
  rewrite Z.mul_1_r.
  replace (4 * (i + 1) - 4 * i) with 4 by lia.
  set (q := p + 4 * i).
  cbn [SeparationLogic.naive_C_Rules.poly_undef_store].
  unfold SeparationLogic.naive_C_Rules.undef_store_uint, SeparationLogic.naive_C_Rules.undef_store_integer at 1.
  SeparationLogic.naive_C_Rules.pureIntros.
  unfold SeparationLogic.naive_C_Rules.UCharArray.undef_seg.
  change (Z.to_nat (4 - 0)) with 4%nat.
  cbn [SeparationLogic.naive_C_Rules.store_undef_array_rec].
  unfold SeparationLogic.naive_C_Rules.StoreUCharAsElement.undefstoreA.
  rewrite SeparationLogic.naive_C_Rules.sizeof_uchar.
  repeat rewrite Z.mul_1_r.
  cbn [SeparationLogic.naive_C_Rules.poly_undef_store].
  unfold SeparationLogic.naive_C_Rules.undef_store_uchar, SeparationLogic.naive_C_Rules.undef_store_integer.
  cbn [SeparationLogic.naive_C_Rules.undef_store_bytes].
  SeparationLogic.naive_C_Rules.split_pure_spatial.
  - repeat match goal with
    | |- context [SeparationLogic.naive_C_Rules.undef_store_byte ?address] =>
      progress ring_simplify address
    end.
    repeat match goal with
    | |- SeparationLogic.naive_C_Rules.derivable1 ?owned _ =>
      match owned with
      | context [SeparationLogic.naive_C_Rules.undef_store_byte ?address] =>
        SeparationLogic.naive_C_Rules.sepcon_right_assoc;
        SeparationLogic.naive_C_Rules.cancel_exactly1_or_fail
          (SeparationLogic.naive_C_Rules.undef_store_byte address)
      end
    end.
  - SeparationLogic.naive_C_Rules.split_pures; SeparationLogic.naive_C_Rules.dump_pre_spatial;
      unfold SeparationLogic.naive_C_Rules.valid_object, SeparationLogic.naive_C_Rules.Arch.valid_object, SeparationLogic.naive_C_Rules.Arch.valid_addr_range,
        SeparationLogic.naive_C_Rules.aligned, SeparationLogic.naive_C_Rules.Arch.aligned in *;
      repeat split; try lia; apply Z.mod_1_r.
Qed.
Lemma uint_undef_segment_to_uchar__array_bridges :
  forall p lo hi (count : nat),
    hi = lo + Z.of_nat count ->
    SeparationLogic.naive_C_Rules.derivable1
      (SeparationLogic.naive_C_Rules.UIntArray.undef_seg p lo hi)
      (SeparationLogic.naive_C_Rules.UCharArray.undef_seg p (4 * lo) (4 * hi)).
Proof.
  intros p lo hi count.
  pose proof SeparationLogic.naive_C_Rules.derivable1_proper_derivable1.
  pose proof SeparationLogic.naive_C_Rules.derivable1s_sepcon_proper.
  pose proof SeparationLogic.naive_C_Rules.derivable1_refl_instance.
  pose proof SeparationLogic.naive_C_Rules.logic_equiv_proper_derivable1.
  pose proof SeparationLogic.naive_C_Rules.logic_equiv_sepcon_proper.
  pose proof SeparationLogic.naive_C_Rules.logic_equiv_symm_instance.
  revert lo.
  induction count as [|count IH]; intros lo Hlength.
  - replace hi with lo by lia.
    rewrite (SeparationLogic.naive_C_Rules.UIntArray.undef_seg_empty p lo).
    rewrite (SeparationLogic.naive_C_Rules.UCharArray.undef_seg_empty p (4 * lo)).
    SeparationLogic.naive_C_Rules.derivable1_refl_tac.
  - rewrite (SeparationLogic.naive_C_Rules.UIntArray.undef_seg_unfold p lo hi) by lia.
    SeparationLogic.naive_C_Rules.sep_apply_l_aux (uint_cell_to_uchar_segment__array_bridges p lo).
    SeparationLogic.naive_C_Rules.sep_apply_l_aux (IH (lo + 1) ltac:(lia)).
    SeparationLogic.naive_C_Rules.sep_apply_l_aux (SeparationLogic.naive_C_Rules.UCharArray.undef_seg_merge_to_undef_seg
      p (4 * lo) (4 * (lo + 1)) (4 * hi) ltac:(lia)).
    SeparationLogic.naive_C_Rules.sepcon_cancel.
Qed.
Lemma uint_full_to_uchar_undef_full__array_bridges :
  forall p count values,
    0 <= count ->
    SeparationLogic.naive_C_Rules.derivable1
      (SeparationLogic.naive_C_Rules.UIntArray.full p count values)
      (SeparationLogic.naive_C_Rules.UCharArray.undef_full p
        (count * SeparationLogic.naive_C_Rules.sizeof_front_end_type CNotation.FET_uint)).
Proof.
  intros p count values Hcount.
  pose proof SeparationLogic.naive_C_Rules.derivable1_proper_derivable1.
  pose proof SeparationLogic.naive_C_Rules.derivable1s_sepcon_proper.
  pose proof SeparationLogic.naive_C_Rules.derivable1_refl_instance.
  pose proof SeparationLogic.naive_C_Rules.logic_equiv_proper_derivable1.
  pose proof SeparationLogic.naive_C_Rules.logic_equiv_sepcon_proper.
  SeparationLogic.naive_C_Rules.sep_apply_l_aux (SeparationLogic.naive_C_Rules.UIntArray.full_to_undef_full p count values).
  SeparationLogic.naive_C_Rules.sep_apply_l_aux (SeparationLogic.naive_C_Rules.UIntArray.undef_full_to_undef_seg p count).
  SeparationLogic.naive_C_Rules.sep_apply_l_aux (uint_undef_segment_to_uchar__array_bridges p 0 count (Z.to_nat count) ltac:(lia)).
  rewrite SeparationLogic.naive_C_Rules.sizeof_uint.
  replace (count * 4) with (4 * count) by lia.
  change (SeparationLogic.naive_C_Rules.derivable1
    (SeparationLogic.naive_C_Rules.UCharArray.undef_seg p 0 (4 * count))
    (SeparationLogic.naive_C_Rules.UCharArray.undef_full p (4 * count))).
  unfold SeparationLogic.naive_C_Rules.UCharArray.undef_seg, SeparationLogic.naive_C_Rules.UCharArray.undef_full, SeparationLogic.naive_C_Rules.store_undef_array.
  rewrite Z.sub_0_r. SeparationLogic.naive_C_Rules.derivable1_refl_tac.
Qed.
