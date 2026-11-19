From Coq Require Import ZArith List String Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import GmpNumber.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.

(* The frontend leaves alias sizes and field addresses abstract in Rocq.
   This condition describes the selected Arch32 MiniGMP object layout. *)
Definition simplex_mpz_layout : Prop :=
  sizeof("__mpz_struct") = 12 /\
  forall p : addr,
    &(p # "__mpz_struct" ->ₛ "_mp_alloc") = p /\
    &(p # "__mpz_struct" ->ₛ "_mp_size") = p + 4 /\
    &(p # "__mpz_struct" ->ₛ "_mp_d") = p + 8.

(* [p] is the malloc base address and [bytes] its exact byte size. The
   external allocator records a ghost cell at [-p]. Negative addresses
   belong to the ghost interpretation, outside the C object address range.
   For [NULL], only a zero-size call can produce this predicate, on emp. *)
Definition simplex_malloc_token (p bytes : Z) : Assertion :=
  if Z.eq_dec p 0 then “ bytes = 0 ” && emp
  else “ 0 < p <= addr_max_unsigned /\ 0 <= bytes ” &&
       (fun st => mem_single (st_mem st) (-p) bytes).

Lemma simplex_malloc_token_null :
  simplex_malloc_token 0 0 --||-- emp.
Proof.
  unfold simplex_malloc_token.
  destruct (Z.eq_dec 0 0); [|contradiction].
  split.
  - intros st [_ Hemp]. exact Hemp.
  - intros st Hemp.
    split.
    + reflexivity.
    + exact Hemp.
Qed.

Lemma simplex_malloc_token_requires_ghost_cell :
  forall p bytes st,
    p <> 0 ->
    simplex_malloc_token p bytes st ->
    st_mem st (-p) = value bytes.
Proof.
  intros p bytes st Hnonnull.
  unfold simplex_malloc_token.
  destruct (Z.eq_dec p 0); [contradiction|].
  intros [_ [Hcell _]]. exact Hcell.
Qed.

Lemma simplex_malloc_token_exclusive :
  forall p bytes1 bytes2,
    p <> 0 ->
    simplex_malloc_token p bytes1 ** simplex_malloc_token p bytes2 |-- “ False ”.
Proof.
  intros p bytes1 bytes2 Hnonnull.
  intros st (st1 & st2 & Hjoin & Htoken1 & Htoken2).
  change False.
  destruct Hjoin as (Hmem & _).
  pose proof (simplex_malloc_token_requires_ghost_cell p bytes1 st1 Hnonnull Htoken1) as Hcell1.
  pose proof (simplex_malloc_token_requires_ghost_cell p bytes2 st2 Hnonnull Htoken2) as Hcell2.
  pose proof (proj1 (mem_join_iff _ _ _) Hmem (-p)) as Hpoint.
  rewrite Hcell1, Hcell2 in Hpoint.
  exact Hpoint.
Qed.

Lemma simplex_malloc_token_not_physical_only :
  forall p bytes st,
    p <> 0 ->
    (forall a, a < 0 -> st_mem st a = Noperm) ->
    ~ simplex_malloc_token p bytes st.
Proof.
  intros p bytes st Hnonnull Hphysical Htoken.
  pose proof (simplex_malloc_token_requires_ghost_cell p bytes st Hnonnull Htoken) as Hcell.
  assert (0 < p) as Hpos.
  { unfold simplex_malloc_token in Htoken.
    destruct (Z.eq_dec p 0); [contradiction|].
    destruct Htoken as [[[Hpos _] _] _].
    exact Hpos. }
  rewrite Hphysical in Hcell by lia.
  discriminate.
Qed.

Lemma simplex_malloc_token_emp_excluded :
  forall p bytes st,
    p <> 0 ->
    emp st ->
    ~ simplex_malloc_token p bytes st.
Proof.
  intros p bytes st Hnonnull Hemp.
  apply simplex_malloc_token_not_physical_only; [exact Hnonnull|].
  intros a _. exact (Hemp a).
Qed.

(* The actual dummy limb is only referenced. The segment owns the disjoint
   headers at indices [lo, hi), each with the MiniGMP dummy representation. *)
Definition simplex_mpz_dummy_seg (p lo hi dummy : Z) : Assertion :=
  store_undef_array_rec
    (fun base index => store_Z_dummy (base + index * sizeof("__mpz_struct")) dummy)
    p lo hi (Z.to_nat (hi - lo)).


Lemma uchar_segment_four_raw__initialization_loop :
  forall p lo hi,
    hi = lo + 4 ->
    UCharArray.undef_seg p lo hi |--
    undef_store_bytes (p + lo) 4.
Proof.
  intros p lo hi ->.
  unfold UCharArray.undef_seg.
  replace (lo + 4 - lo) with 4 by lia.
  change (Z.to_nat 4) with 4%nat.
  cbn [store_undef_array_rec].
  unfold StoreUCharAsElement.undefstoreA.
  rewrite sizeof_uchar.
  repeat rewrite Z.mul_1_r.
  cbn [poly_undef_store].
  unfold undef_store_uchar, undef_store_integer.
  cbn [undef_store_bytes].
  Intros.
  replace (p + (lo + 1)) with (p + lo + 1) by lia.
  replace (p + (lo + 1 + 1)) with (p + lo + 1 + 1) by lia.
  replace (p + (lo + 1 + 1 + 1)) with (p + lo + 1 + 1 + 1) by lia.
  cancel.
Qed.
Lemma raw_four_to_int__initialization_loop :
  forall q, valid_object q 4 4 ->
    undef_store_bytes q 4 |-- undef_store_int q.
Proof.
  intros q Hvalid.
  unfold undef_store_int, undef_store_integer.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. exact Hvalid.
Qed.
Lemma raw_four_to_ptr__initialization_loop :
  forall q, valid_object q 4 4 ->
    undef_store_bytes q 4 |-- undef_store_ptr q.
Proof.
  intros q Hvalid.
  change (undef_store_bytes q 4 |-- “ valid_object q 4 4 ” && undef_store_bytes q 4).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. exact Hvalid.
Qed.
Lemma mpz_undef_header__initialization_loop :
  forall p i,
    simplex_mpz_layout ->
    0 <= p + i * sizeof("__mpz_struct") ->
    (4 | p + i * sizeof("__mpz_struct")) ->
    p + i * sizeof("__mpz_struct") + 11 <= addr_max_unsigned ->
    UCharArray.undef_seg p (i * sizeof("__mpz_struct"))
      ((i + 1) * sizeof("__mpz_struct")) |--
    undef_store_int (&(((p + (i * sizeof("__mpz_struct")))) # "__mpz_struct" ->ₛ "_mp_alloc")) **
    undef_store_int (&(((p + (i * sizeof("__mpz_struct")))) # "__mpz_struct" ->ₛ "_mp_size")) **
    undef_store_ptr (&(((p + (i * sizeof("__mpz_struct")))) # "__mpz_struct" ->ₛ "_mp_d")).
Proof.
  intros p i [Hstride Hfields].
  rewrite Hstride.
  intros Hnonneg Halign Hlast.
  destruct (Hfields (p + i * 12)) as [Halloc [Hsize Hd]].
  rewrite Halloc, Hsize, Hd.
  assert (Hvalid : forall off, 0 <= off <= 8 -> (4 | off) ->
    valid_object (p + i * 12 + off) 4 4).
  {
    intros off Hoff Hdiv.
    unfold valid_object, valid_addr_range, aligned.
    repeat split; try lia.
    apply Z.mod_divide; [lia|].
    apply Z.divide_add_r; assumption.
  }
  replace ((i + 1) * 12) with ((i * 12 + 8) + 4) by lia.
  sep_apply (UCharArray.undef_seg_split_to_undef_seg p (i * 12)
    (i * 12 + 4) (i * 12 + 8 + 4) ltac:(lia)).
  sep_apply (UCharArray.undef_seg_split_to_undef_seg p (i * 12 + 4)
    (i * 12 + 8) (i * 12 + 8 + 4) ltac:(lia)).
  sep_apply (uchar_segment_four_raw__initialization_loop p
    (i * 12) (i * 12 + 4) ltac:(lia)).
  sep_apply (uchar_segment_four_raw__initialization_loop p
    (i * 12 + 4) (i * 12 + 8) ltac:(lia)).
  sep_apply (uchar_segment_four_raw__initialization_loop p
    (i * 12 + 8) (i * 12 + 8 + 4) ltac:(lia)).
  replace (p + (i * 12 + 4)) with (p + i * 12 + 4) by lia.
  replace (p + (i * 12 + 8)) with (p + i * 12 + 8) by lia.
  assert (Halloc_valid : valid_object (p + i * 12) 4 4).
  { replace (p + i * 12) with (p + i * 12 + 0) by lia.
    apply Hvalid; [lia | exists 0; lia]. }
  sep_apply (raw_four_to_int__initialization_loop (p + i * 12) Halloc_valid).
  sep_apply (raw_four_to_int__initialization_loop (p + i * 12 + 4)
    (Hvalid 4 ltac:(lia) ltac:(exists 1; lia))).
  sep_apply (raw_four_to_ptr__initialization_loop (p + i * 12 + 8)
    (Hvalid 8 ltac:(lia) ltac:(exists 2; lia))).
  cancel.
Qed.
Lemma dummy_array_rec_snoc__initialization_loop :
  forall len p lo hi dummy,
    Z.of_nat len = hi - lo ->
    store_undef_array_rec
      (fun base index => store_Z_dummy (base + index * sizeof("__mpz_struct")) dummy)
      p lo hi len **
    store_Z_dummy (p + hi * sizeof("__mpz_struct")) dummy |--
    store_undef_array_rec
      (fun base index => store_Z_dummy (base + index * sizeof("__mpz_struct")) dummy)
      p lo (hi + 1) (S len).
Proof.
  induction len as [|len IH]; intros p lo hi dummy Hlen.
  - assert (hi = lo) by lia. subst hi.
    cbn [store_undef_array_rec].
    Intros.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. reflexivity.
  - cbn [store_undef_array_rec].
    cancel (store_Z_dummy (p + lo * sizeof("__mpz_struct")) dummy).
    apply IH. lia.
Qed.
Lemma mpz_dummy_seg_snoc__initialization_loop :
  forall p lo hi dummy, lo <= hi ->
    simplex_mpz_dummy_seg p lo hi dummy **
    store_Z_dummy (p + hi * sizeof("__mpz_struct")) dummy |--
    simplex_mpz_dummy_seg p lo (hi + 1) dummy.
Proof.
  intros p lo hi dummy Hrange.
  unfold simplex_mpz_dummy_seg.
  replace (Z.to_nat (hi + 1 - lo)) with (S (Z.to_nat (hi - lo))) by lia.
  apply dummy_array_rec_snoc__initialization_loop.
  apply Z2Nat.id. lia.
Qed.
Lemma mpz_dummy_seg_empty_intro__initialization_loop :
  forall p i dummy, emp |-- simplex_mpz_dummy_seg p i i dummy.
Proof.
  intros p i dummy.
  unfold simplex_mpz_dummy_seg.
  replace (i - i) with 0 by lia.
  change (emp |-- “ i = i ” && emp).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. reflexivity.
Qed.
