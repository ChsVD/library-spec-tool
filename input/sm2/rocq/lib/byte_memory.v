(** Shared typed-integer and unsigned-byte memory views. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.Applications_human.sm2.lib Require Export
  byte_encoding sm2_common_lib.

Import ListNotations.
Local Open Scope Z_scope.

Import naive_C_Rules.
Local Open Scope sac.

Lemma uchar_seg_values_bounded : forall p lo hi bs,
  UCharArray.seg p lo hi bs |-- “ u8_list_bounded bs ”.
Proof.
  intros p lo hi bs.
  unfold UCharArray.seg.
  revert lo; induction bs as [| b bs IH]; intros lo; simpl.
  - apply derivable1s_coq_prop_r.
    unfold u8_list_bounded, limb_list_bounded.
    intros i Hi; rewrite Zlength_nil in Hi; lia.
  - prop_apply (store_uchar_range (p + lo * sizeof(UCHAR)) b).
    prop_apply (IH (lo + 1)).
    Intros.
    apply derivable1s_coq_prop_r.
    unfold u8_list_bounded, SM2_BYTE_BASE in *.
    rewrite limb_list_bounded_cons_iff.
    change Byte.max_unsigned with 255 in *.
    split; [lia | assumption].
Qed.

Lemma uchar_full_values_bounded : forall p n bs,
  UCharArray.full p n bs |-- “ u8_list_bounded bs ”.
Proof.
  intros p n bs.
  sep_apply UCharArray.full_to_seg.
  apply uchar_seg_values_bounded.
Qed.

Lemma uchar_full_merge_swapped : forall p n m xs ys,
  0 <= n <= m ->
  UCharArray.full (p + n * sizeof(UCHAR)) (m - n) ys **
  UCharArray.full p n xs |--
  UCharArray.full p m (xs ++ ys).
Proof.
  intros p n m xs ys Hrange.
  assert (Hswap :
    UCharArray.full (p + n * sizeof(UCHAR)) (m - n) ys **
    UCharArray.full p n xs |--
    UCharArray.full p n xs **
    UCharArray.full (p + n * sizeof(UCHAR)) (m - n) ys) by cancel.
  sep_apply Hswap.
  apply UCharArray.full_merge_to_full; exact Hrange.
Qed.

Lemma uchar_full_merge_swapped_frame : forall p n m xs ys
    (F G : Assertion),
  0 <= n <= m ->
  UCharArray.full (p + n * sizeof(UCHAR)) (m - n) ys **
  (F ** (UCharArray.full p n xs ** G)) |--
  F ** (UCharArray.full p m (xs ++ ys) ** G).
Proof.
  intros p n m xs ys F G Hrange.
  sep_apply (uchar_full_merge_swapped p n m xs ys Hrange).
  cancel.
Qed.

Lemma naive_u8_undef_full4_to_undef_store_uint : forall address,
  aligned_4 address ->
  UCharArray.undef_full address 4 |-- undef_store_uint address.
Proof.
  intros address Haligned.
  rewrite undef_store_uint_undef_store_char.
  unfold UCharArray.undef_full, store_undef_array,
    undef_store_uchar, undef_store_char.
  rewrite !sizeof_uchar.
  simpl store_undef_array_rec.
  cbn.
  replace (address + 0) with address by lia.
  entailer!.
Qed.

Lemma uchar_undef_full8_to_uint_undef_full2 : forall address,
  aligned_4 address ->
  UCharArray.undef_full address 8 |-- UIntArray.undef_full address 2.
Proof.
  intros address Haligned.
  assert (Halign4 : aligned_4 (address + 4)).
  { unfold aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Haligned; reflexivity. }
  sep_apply_l_atomic
    (UCharArray.undef_full_split_to_undef_full address 4 8 ltac:(lia)).
  sep_apply_l_atomic
    (naive_u8_undef_full4_to_undef_store_uint address Haligned).
  sep_apply_l_atomic
    (naive_u8_undef_full4_to_undef_store_uint (address + 4) Halign4).
  unfold UIntArray.undef_full, store_undef_array.
  simpl store_undef_array_rec.
  replace (address + 0) with address by lia.
  split_pure_spatial.
  - normalize; cancel.
  - split_pures.
    apply derivable1s_coq_prop_r.
    reflexivity.
Qed.

Import Snaive_C_Rules.
Local Open Scope sac.

Lemma snaive_uchar_seg_values_bounded : forall p lo hi bs,
  UCharArray.seg p lo hi bs |-- “ u8_list_bounded bs ”.
Proof.
  intros p lo hi bs.
  unfold UCharArray.seg.
  revert lo; induction bs as [| b bs IH]; intros lo; simpl.
  - apply derivable1s_coq_prop_r.
    unfold u8_list_bounded, limb_list_bounded.
    intros i Hi; rewrite Zlength_nil in Hi; lia.
  - prop_apply (store_uchar_range (p + lo * sizeof(UCHAR)) b).
    prop_apply (IH (lo + 1)).
    Intros.
    apply derivable1s_coq_prop_r.
    unfold u8_list_bounded, SM2_BYTE_BASE in *.
    rewrite limb_list_bounded_cons_iff.
    change Byte.max_unsigned with 255 in *.
    split; [lia | assumption].
Qed.

Lemma snaive_uchar_full_values_bounded : forall p n bs,
  UCharArray.full p n bs |-- “ u8_list_bounded bs ”.
Proof.
  intros p n bs.
  sep_apply UCharArray.full_to_seg.
  apply snaive_uchar_seg_values_bounded.
Qed.

(** One 32-bit unsigned cell as four little-endian unsigned bytes. *)
Lemma store_uint_store_uchar : forall address value,
  store_uint address value --||--
  EX b0 b1 b2 b3 : Z,
    “ merge_int b0 b1 b2 b3 value ” &&
    “ 0 <= value <= Int.max_unsigned ” &&
    “ aligned_4 address ” &&
    store_uchar address b0 **
    store_uchar (address + 1) b1 **
    store_uchar (address + 2) b2 **
    store_uchar (address + 3) b3.
Proof.
  intros address value.
  split.
  - unfold store_uint, store_4byte.
    Intros z0 z1 z2 z3.
    Exists (Byte.unsigned (Byte.repr z0)).
    Exists (Byte.unsigned (Byte.repr z1)).
    Exists (Byte.unsigned (Byte.repr z2)).
    Exists (Byte.unsigned (Byte.repr z3)).
    unfold store_uchar.
    pose proof Byte.unsigned_range_2 (Byte.repr z0).
    pose proof Byte.unsigned_range_2 (Byte.repr z1).
    pose proof Byte.unsigned_range_2 (Byte.repr z2).
    pose proof Byte.unsigned_range_2 (Byte.repr z3).
    entailer!.
    + repeat (apply derivable1_sepcon_mono;
              [apply store_byte_eqm, Byte.eqm_unsigned_repr |]).
      apply store_byte_eqm, Byte.eqm_unsigned_repr.
    + unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    + unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    + unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    + unfold isvalidptr_char.
      unfold isvalidptr_int in H.
      lia.
    + exact (proj2 (proj2 (proj1 H))).
    + eapply merge_int_eqm;
        try apply Byte.eqm_unsigned_repr; exact H0.
  - Intros b0 b1 b2 b3.
    unfold store_uint, store_uchar, store_4byte.
    Intros.
    Exists b0 b1 b2 b3.
    entailer!.
    unfold isvalidptr_int.
    unfold isvalidptr_char in *.
    repeat split; try lia; auto.
Qed.

Lemma undef_store_uint_undef_store_uchar : forall address,
  undef_store_uint address --||--
  “ aligned_4 address ” &&
  undef_store_uchar address **
  undef_store_uchar (address + 1) **
  undef_store_uchar (address + 2) **
  undef_store_uchar (address + 3).
Proof.
  intros address.
  unfold undef_store_uint, undef_store_uchar.
  unfold isvalidptr_int, isvalidptr_char.
  split; Intros; entailer!.
Qed.

Lemma store_uint_to_u8_full4 :
  forall address value,
    store_uint address value |--
    EX bytes,
      “ Zlength bytes = 4 /\
        u8_list_bounded bytes /\
        u8_list_value bytes = value /\
        aligned_4 address ” &&
      UCharArray.full address 4 bytes.
Proof.
  intros address value.
  rewrite store_uint_store_uchar.
  Intros b0 b1 b2 b3.
  prop_apply (store_uchar_range address b0).
  Intros.
  prop_apply (store_uchar_range (address + 1) b1).
  Intros.
  prop_apply (store_uchar_range (address + 2) b2).
  Intros.
  prop_apply (store_uchar_range (address + 3) b3).
  Intros.
  Exists [b0; b1; b2; b3].
  split_pure_spatial.
  - unfold UCharArray.full, store_array.
    cbn [store_array_rec].
    rewrite !sizeof_uchar.
    cbn.
    replace (address + 0) with address by lia.
    entailer!.
  - entailer!.
    + unfold u8_list_bounded.
      repeat rewrite limb_list_bounded_cons_iff.
      unfold limb_list_bounded, SM2_BYTE_BASE.
      repeat split; cbn in *; lia.
    + unfold u8_list_value.
      repeat rewrite limb_list_value_cons.
      rewrite limb_list_value_nil.
      unfold merge_int, LittleEndian.merge_int in H.
      change Int.max_unsigned with (2 ^ 32 - 1) in *.
      change Byte.max_unsigned with 255 in *.
      rewrite Z.mod_small in H by lia.
      repeat rewrite Z.mod_small in H by lia.
      unfold SM2_BYTE_BASE, limb_radix.
      ring_simplify in H.
      ring_simplify.
      lia.
Qed.

Lemma u8_full4_to_store_uint :
  forall address value bytes,
    Zlength bytes = 4 ->
    u8_list_bounded bytes ->
    u8_list_value bytes = value ->
    aligned_4 address ->
    UCharArray.full address 4 bytes |-- store_uint address value.
Proof.
  intros address value bytes Hlength Hbounded Hvalue Haligned.
  destruct bytes as [|b0 bytes].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct bytes as [|b1 bytes].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct bytes as [|b2 bytes].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct bytes as [|b3 bytes].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct bytes as [|extra bytes].
  2: {
    rewrite Zlength_cons in Hlength.
    pose proof (Zlength_nonneg bytes).
    lia.
  }
  apply limb_list_bounded_cons_iff in Hbounded as [Hb0 Hbounded].
  apply limb_list_bounded_cons_iff in Hbounded as [Hb1 Hbounded].
  apply limb_list_bounded_cons_iff in Hbounded as [Hb2 Hbounded].
  apply limb_list_bounded_cons_iff in Hbounded as [Hb3 _].
  assert (Hvalue_range : 0 <= value < 2 ^ 32).
  {
    pose proof
      (limb_list_value_range SM2_BYTE_BASE [b0; b1; b2; b3]
        ltac:(unfold SM2_BYTE_BASE; lia)) as Hrange.
    assert (Hall :
      limb_list_bounded SM2_BYTE_BASE [b0; b1; b2; b3]).
    {
      repeat rewrite limb_list_bounded_cons_iff.
      repeat split; try assumption.
      all: cbn in *; lia.
    }
    specialize (Hrange Hall).
    unfold u8_list_value in Hvalue.
    rewrite Hvalue in Hrange.
    cbv [limb_radix SM2_BYTE_BASE] in Hrange.
    exact Hrange.
  }
  rewrite store_uint_store_uchar.
  Exists b0 b1 b2 b3.
  split_pure_spatial.
  - unfold UCharArray.full, store_array.
    cbn [store_array_rec].
    rewrite !sizeof_uchar.
    cbn.
    replace (address + 0) with address by lia.
    entailer!.
  - entailer!.
    + change Int.max_unsigned with (2 ^ 32 - 1).
      lia.
    + unfold u8_list_value in Hvalue.
      repeat rewrite limb_list_value_cons in Hvalue.
      rewrite limb_list_value_nil in Hvalue.
      unfold merge_int, LittleEndian.merge_int.
      rewrite Z.mod_small by lia.
      repeat rewrite Z.mod_small by
        (unfold SM2_BYTE_BASE in *; lia).
      unfold SM2_BYTE_BASE, limb_radix in Hvalue.
      ring_simplify in Hvalue.
      ring_simplify.
      lia.
Qed.

Lemma undef_store_uint_to_u8_undef_full4 :
  forall address,
    undef_store_uint address |--
      UCharArray.undef_full address 4.
Proof.
  intros address.
  rewrite undef_store_uint_undef_store_uchar.
  Intros.
  unfold UCharArray.undef_full, store_undef_array.
  rewrite !sizeof_uchar.
  simpl store_undef_array_rec.
  cbn.
  replace (address + 0) with address by lia.
  entailer!.
Qed.

Lemma u8_undef_full4_to_undef_store_uint :
  forall address,
    aligned_4 address ->
    UCharArray.undef_full address 4 |--
      undef_store_uint address.
Proof.
  intros address Haligned.
  rewrite undef_store_uint_undef_store_uchar.
  unfold UCharArray.undef_full, store_undef_array.
  rewrite !sizeof_uchar.
  simpl store_undef_array_rec.
  cbn.
  replace (address + 0) with address by lia.
  entailer!.
Qed.

Lemma store_uint_to_store_bytes4 :
  forall address value,
    store_uint address value |--
    EX bytes,
      “ u8_list_value bytes = value /\ aligned_4 address ” &&
      byte_encoding.store_bytes address 4 bytes.
Proof.
  intros address value.
  sep_apply (store_uint_to_u8_full4 address value).
  Intros bytes.
  Exists bytes.
  unfold byte_encoding.store_bytes.
  entailer!.
Qed.

Lemma store_bytes4_to_store_uint :
  forall address value bytes,
    u8_list_value bytes = value ->
    aligned_4 address ->
    byte_encoding.store_bytes address 4 bytes |-- store_uint address value.
Proof.
  intros address value bytes Hvalue Haligned.
  unfold byte_encoding.store_bytes.
  Intros.
  destruct H as [Hlength Hbounded].
  apply u8_full4_to_store_uint; assumption.
Qed.

(** One 64-bit cell viewed as eight little-endian unsigned bytes. *)
Lemma undef_store_uint64_undef_store_uchar : forall address,
  undef_store_uint64 address --||--
  “ aligned_4 address ” &&
  undef_store_uchar address **
  undef_store_uchar (address + 1) **
  undef_store_uchar (address + 2) **
  undef_store_uchar (address + 3) **
  undef_store_uchar (address + 4) **
  undef_store_uchar (address + 5) **
  undef_store_uchar (address + 6) **
  undef_store_uchar (address + 7).
Proof.
  intros address.
  unfold undef_store_uint64, undef_store_uchar.
  unfold store_8byte_noninit, isvalidptr_int64, isvalidptr_char.
  split; Intros; entailer!.
Qed.

Lemma undef_store_uint64_to_u8_undef_full8 :
  forall address,
    undef_store_uint64 address |--
      UCharArray.undef_full address 8.
Proof.
  intros address.
  rewrite undef_store_uint64_undef_store_uchar.
  Intros.
  unfold UCharArray.undef_full, store_undef_array.
  rewrite !sizeof_uchar.
  simpl store_undef_array_rec.
  cbn.
  replace (address + 0) with address by lia.
  entailer!.
Qed.

Lemma u8_undef_full8_to_undef_store_uint64 :
  forall address,
    aligned_4 address ->
    UCharArray.undef_full address 8 |--
      undef_store_uint64 address.
Proof.
  intros address Haligned.
  rewrite undef_store_uint64_undef_store_uchar.
  unfold UCharArray.undef_full, store_undef_array.
  rewrite !sizeof_uchar.
  simpl store_undef_array_rec.
  cbn.
  replace (address + 0) with address by lia.
  entailer!.
Qed.

Lemma store_uint64_to_u8_full8 :
  forall address value,
    store_uint64 address value |--
    EX bytes,
      “ Zlength bytes = 8 /\
        u8_list_bounded bytes /\
        u8_list_value bytes = value /\
        aligned_4 address ” &&
      UCharArray.full address 8 bytes.
Proof.
  intros address value.
  rewrite store_uint64_store_uchar.
  Intros b0 b1 b2 b3 b4 b5 b6 b7.
  prop_apply (store_uchar_range address b0).
  Intros.
  prop_apply (store_uchar_range (address + 1) b1).
  Intros.
  prop_apply (store_uchar_range (address + 2) b2).
  Intros.
  prop_apply (store_uchar_range (address + 3) b3).
  Intros.
  prop_apply (store_uchar_range (address + 4) b4).
  Intros.
  prop_apply (store_uchar_range (address + 5) b5).
  Intros.
  prop_apply (store_uchar_range (address + 6) b6).
  Intros.
  prop_apply (store_uchar_range (address + 7) b7).
  Intros.
  Exists [b0; b1; b2; b3; b4; b5; b6; b7].
  split_pure_spatial.
  - unfold UCharArray.full, store_array.
    cbn [store_array_rec].
    rewrite !sizeof_uchar.
    cbn.
    replace (address + 0) with address by lia.
    entailer!.
  - entailer!.
    + unfold u8_list_bounded.
      repeat rewrite limb_list_bounded_cons_iff.
      unfold limb_list_bounded.
      change Byte.max_unsigned with 255 in *.
      unfold SM2_BYTE_BASE.
      repeat split; try lia.
      all: cbn in *; lia.
    + unfold u8_list_value.
      repeat rewrite limb_list_value_cons.
      rewrite limb_list_value_nil.
      unfold merge_int64, LittleEndian.merge_int64 in H.
      change Byte.max_unsigned with 255 in *.
      change Int64.max_unsigned with (U64_MOD - 1) in *.
      rewrite Z.mod_small in H by
        (cbv [U64_MOD] in *; lia).
      repeat rewrite Z.mod_small in H by lia.
      unfold SM2_BYTE_BASE, limb_radix.
      ring_simplify in H.
      ring_simplify.
      lia.
Qed.

Lemma u8_full8_to_store_uint64 :
  forall address value bytes,
    Zlength bytes = 8 ->
    u8_list_bounded bytes ->
    u8_list_value bytes = value ->
    aligned_4 address ->
    UCharArray.full address 8 bytes |-- store_uint64 address value.
Proof.
  intros address value bytes Hlength Hbounded Hvalue Haligned.
  destruct bytes as [|b0 bytes].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct bytes as [|b1 bytes].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct bytes as [|b2 bytes].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct bytes as [|b3 bytes].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct bytes as [|b4 bytes].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct bytes as [|b5 bytes].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct bytes as [|b6 bytes].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct bytes as [|b7 bytes].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct bytes as [|extra bytes].
  2: {
    rewrite Zlength_cons in Hlength.
    pose proof (Zlength_nonneg bytes).
    lia.
  }
  apply limb_list_bounded_cons_iff in Hbounded as [Hb0 Hbounded].
  apply limb_list_bounded_cons_iff in Hbounded as [Hb1 Hbounded].
  apply limb_list_bounded_cons_iff in Hbounded as [Hb2 Hbounded].
  apply limb_list_bounded_cons_iff in Hbounded as [Hb3 Hbounded].
  apply limb_list_bounded_cons_iff in Hbounded as [Hb4 Hbounded].
  apply limb_list_bounded_cons_iff in Hbounded as [Hb5 Hbounded].
  apply limb_list_bounded_cons_iff in Hbounded as [Hb6 Hbounded].
  apply limb_list_bounded_cons_iff in Hbounded as [Hb7 _].
  assert (Hvalue_range : 0 <= value < U64_MOD).
  {
    pose proof
      (limb_list_value_range SM2_BYTE_BASE
        [b0; b1; b2; b3; b4; b5; b6; b7]
        ltac:(unfold SM2_BYTE_BASE; lia)) as Hrange.
    assert (Hall :
      limb_list_bounded SM2_BYTE_BASE
        [b0; b1; b2; b3; b4; b5; b6; b7]).
    {
      repeat rewrite limb_list_bounded_cons_iff.
      repeat split; try assumption.
      all: cbn in *; lia.
    }
    specialize (Hrange Hall).
    unfold u8_list_value in Hvalue.
    rewrite Hvalue in Hrange.
    cbv [limb_radix SM2_BYTE_BASE U64_MOD] in Hrange.
    exact Hrange.
  }
  rewrite store_uint64_store_uchar.
  Exists b0 b1 b2 b3 b4 b5 b6 b7.
  split_pure_spatial.
  - unfold UCharArray.full, store_array.
    cbn [store_array_rec].
    rewrite !sizeof_uchar.
    cbn.
    replace (address + 0) with address by lia.
    entailer!.
  - entailer!.
    + change Int64.max_unsigned with (U64_MOD - 1).
      lia.
    + unfold u8_list_value in Hvalue.
      repeat rewrite limb_list_value_cons in Hvalue.
      rewrite limb_list_value_nil in Hvalue.
      unfold merge_int64, LittleEndian.merge_int64.
      rewrite Z.mod_small by
        (unfold U64_MOD in Hvalue_range; lia).
      repeat rewrite Z.mod_small by
        (unfold u8_list_bounded, SM2_BYTE_BASE in *; lia).
      unfold SM2_BYTE_BASE, limb_radix in Hvalue.
      ring_simplify in Hvalue.
      ring_simplify.
      lia.
Qed.

Lemma u8_full8_to_two_store_uint :
  forall address bytes,
    Zlength bytes = 8 ->
    u8_list_bounded bytes ->
    aligned_4 address ->
    UCharArray.full address 8 bytes |--
      store_uint address
        (u8_list_value (sublist 0 4 bytes)) **
      store_uint (address + 4)
        (u8_list_value (sublist 4 8 bytes)).
Proof.
  intros address bytes Hlength Hbounded Haligned.
  assert (Hlen0 : Zlength (sublist 0 4 bytes) = 4).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hlen1 : Zlength (sublist 4 8 bytes) = 4).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hbound0 : u8_list_bounded (sublist 0 4 bytes)).
  {
    unfold u8_list_bounded in *.
    apply limb_list_bounded_sublist; [exact Hbounded |].
    rewrite Hlength.
    lia.
  }
  assert (Hbound1 : u8_list_bounded (sublist 4 8 bytes)).
  {
    unfold u8_list_bounded in *.
    apply limb_list_bounded_sublist; [exact Hbounded |].
    rewrite Hlength.
    lia.
  }
  assert (Halign4 : aligned_4 (address + 4)).
  {
    unfold aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Haligned.
    reflexivity.
  }
  sep_apply
    (UCharArray.full_split_to_full
      address 4 8 bytes ltac:(lia)).
  rewrite sizeof_uchar.
  replace (8 - 4) with 4 by lia.
  sep_apply
    (u8_full4_to_store_uint
      address (u8_list_value (sublist 0 4 bytes))
      (sublist 0 4 bytes)
      Hlen0 Hbound0 ltac:(reflexivity) Haligned).
  sep_apply
    (u8_full4_to_store_uint
      (address + 4) (u8_list_value (sublist 4 8 bytes))
      (sublist 4 8 bytes)
      Hlen1 Hbound1 ltac:(reflexivity) Halign4).
  cancel.
Qed.

Lemma two_store_uint_to_u8_full8 :
  forall address low high,
    store_uint address low **
    store_uint (address + 4) high |--
    EX low_bytes high_bytes,
      “ Zlength low_bytes = 4 /\
        Zlength high_bytes = 4 /\
        u8_list_bounded low_bytes /\
        u8_list_bounded high_bytes /\
        u8_list_value low_bytes = low /\
        u8_list_value high_bytes = high /\
        aligned_4 address ” &&
      UCharArray.full address 8 (low_bytes ++ high_bytes).
Proof.
  intros address low high.
  sep_apply (store_uint_to_u8_full4 address low).
  Intros low_bytes.
  sep_apply (store_uint_to_u8_full4 (address + 4) high).
  Intros high_bytes.
  destruct H as
    [Hlow_length [Hlow_bounded [Hlow_value Haligned]]].
  destruct H0 as
    [Hhigh_length [Hhigh_bounded [Hhigh_value _]]].
  Exists low_bytes high_bytes.
  split_pure_spatial.
  - pose proof
      (UCharArray.full_merge_to_full
        address 4 8 low_bytes high_bytes ltac:(lia)) as Hmerge.
    rewrite sizeof_uchar in Hmerge.
    replace (8 - 4) with 4 in Hmerge by lia.
    sep_apply Hmerge.
    cancel.
  - entailer!.
Qed.

(** The four limbs of a [u32] as one contiguous 32-byte array. *)
Lemma store_u256_limbs_to_u8_full32 :
  forall address value,
    store_u256_limbs address value |--
    EX bytes,
      “ Zlength bytes = 32 /\
        u8_list_bounded bytes /\
        u8_list_value bytes = value /\
        aligned_4 address ” &&
      UCharArray.full address 32 bytes.
Proof.
  intros address value.
  unfold store_u256_limbs.
  Intros x0 x1 x2 x3.
  destruct H as [Hx0 [Hx1 [Hx2 [Hx3 Hvalue]]]].
  rewrite !sizeof_uint64.
  replace (address + 0 * 8) with address by lia.
  sep_apply (store_uint64_to_u8_full8 address x0).
  Intros bytes0.
  destruct H as [Hlen0 [Hbound0 [Hvalue0 Halign]]].
  sep_apply (store_uint64_to_u8_full8 (address + 8) x1).
  Intros bytes1.
  destruct H as [Hlen1 [Hbound1 [Hvalue1 Halign1]]].
  sep_apply (store_uint64_to_u8_full8 (address + 16) x2).
  Intros bytes2.
  destruct H as [Hlen2 [Hbound2 [Hvalue2 Halign2]]].
  sep_apply (store_uint64_to_u8_full8 (address + 24) x3).
  Intros bytes3.
  destruct H as [Hlen3 [Hbound3 [Hvalue3 Halign3]]].
  Exists (bytes0 ++ bytes1 ++ bytes2 ++ bytes3).
  split_pure_spatial.
  - replace (address + 8) with
      (address + 8 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    replace (address + 16) with
      (address + 16 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    replace (address + 24) with
      (address + 24 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    replace (address + 16 * sizeof(UCHAR)) with
      ((address + 8 * sizeof(UCHAR)) + 8 * sizeof(UCHAR)) by lia.
    pose proof
      (UCharArray.full_merge_to_full
        (address + 8 * sizeof(UCHAR)) 8 16 bytes1 bytes2
        ltac:(lia)) as Hmerge12.
    replace (16 - 8) with 8 in Hmerge12 by lia.
    sep_apply Hmerge12.
    pose proof
      (UCharArray.full_merge_to_full
        address 8 24 bytes0 (bytes1 ++ bytes2)
        ltac:(lia)) as Hmerge02.
    replace (24 - 8) with 16 in Hmerge02 by lia.
    sep_apply Hmerge02.
    rewrite derivable1_sepcon_comm.
    pose proof
      (UCharArray.full_merge_to_full
        address 24 32 (bytes0 ++ bytes1 ++ bytes2) bytes3
        ltac:(lia)) as Hmerge03.
    replace (32 - 24) with 8 in Hmerge03 by lia.
    sep_apply Hmerge03.
    entailer!.
    rewrite !app_assoc.
    reflexivity.
  - entailer!.
    + rewrite !Zlength_app, Hlen0, Hlen1, Hlen2, Hlen3.
      lia.
    + unfold u8_list_bounded in *.
      repeat rewrite limb_list_bounded_app.
      tauto.
    + unfold u8_list_value in *.
      repeat rewrite limb_list_value_app.
      rewrite Hlen0, Hlen1, Hlen2.
      unfold limb_radix, SM2_BYTE_BASE in *.
      change (256 ^ 8) with U64_MOD in *.
      rewrite Hvalue0, Hvalue1, Hvalue2, Hvalue3.
      unfold u256_of_limbs in Hvalue.
      lia.
Qed.

Lemma u8_full32_to_store_u256_limbs :
  forall address value bytes,
    Zlength bytes = 32 ->
    u8_list_bounded bytes ->
    u8_list_value bytes = value ->
    aligned_4 address ->
    UCharArray.full address 32 bytes |-- store_u256_limbs address value.
Proof.
  intros address value bytes Hlength Hbounded Hvalue Haligned.
  pose (bytes0 := sublist 0 8 bytes).
  pose (bytes1 := sublist 8 16 bytes).
  pose (bytes2 := sublist 16 24 bytes).
  pose (bytes3 := sublist 24 32 bytes).
  assert (Hlen0 : Zlength bytes0 = 8).
  { unfold bytes0. rewrite Zlength_sublist by lia. lia. }
  assert (Hlen1 : Zlength bytes1 = 8).
  { unfold bytes1. rewrite Zlength_sublist by lia. lia. }
  assert (Hlen2 : Zlength bytes2 = 8).
  { unfold bytes2. rewrite Zlength_sublist by lia. lia. }
  assert (Hlen3 : Zlength bytes3 = 8).
  { unfold bytes3. rewrite Zlength_sublist by lia. lia. }
  assert (Hbound0 : u8_list_bounded bytes0).
  {
    unfold u8_list_bounded in *.
    apply limb_list_bounded_sublist; [exact Hbounded |].
    rewrite Hlength.
    lia.
  }
  assert (Hbound1 : u8_list_bounded bytes1).
  {
    unfold u8_list_bounded in *.
    apply limb_list_bounded_sublist; [exact Hbounded |].
    rewrite Hlength.
    lia.
  }
  assert (Hbound2 : u8_list_bounded bytes2).
  {
    unfold u8_list_bounded in *.
    apply limb_list_bounded_sublist; [exact Hbounded |].
    rewrite Hlength.
    lia.
  }
  assert (Hbound3 : u8_list_bounded bytes3).
  {
    unfold u8_list_bounded in *.
    apply limb_list_bounded_sublist; [exact Hbounded |].
    rewrite Hlength.
    lia.
  }
  set (x0 := u8_list_value bytes0).
  set (x1 := u8_list_value bytes1).
  set (x2 := u8_list_value bytes2).
  set (x3 := u8_list_value bytes3).
  assert (Hx0 : 0 <= x0 < U64_MOD).
  {
    unfold x0, u8_list_value.
    pose proof
      (limb_list_value_range SM2_BYTE_BASE bytes0
        ltac:(unfold SM2_BYTE_BASE; lia) Hbound0) as Hrange.
    rewrite Hlen0 in Hrange.
    cbv [limb_radix SM2_BYTE_BASE U64_MOD] in Hrange.
    exact Hrange.
  }
  assert (Hx1 : 0 <= x1 < U64_MOD).
  {
    unfold x1, u8_list_value.
    pose proof
      (limb_list_value_range SM2_BYTE_BASE bytes1
        ltac:(unfold SM2_BYTE_BASE; lia) Hbound1) as Hrange.
    rewrite Hlen1 in Hrange.
    cbv [limb_radix SM2_BYTE_BASE U64_MOD] in Hrange.
    exact Hrange.
  }
  assert (Hx2 : 0 <= x2 < U64_MOD).
  {
    unfold x2, u8_list_value.
    pose proof
      (limb_list_value_range SM2_BYTE_BASE bytes2
        ltac:(unfold SM2_BYTE_BASE; lia) Hbound2) as Hrange.
    rewrite Hlen2 in Hrange.
    cbv [limb_radix SM2_BYTE_BASE U64_MOD] in Hrange.
    exact Hrange.
  }
  assert (Hx3 : 0 <= x3 < U64_MOD).
  {
    unfold x3, u8_list_value.
    pose proof
      (limb_list_value_range SM2_BYTE_BASE bytes3
        ltac:(unfold SM2_BYTE_BASE; lia) Hbound3) as Hrange.
    rewrite Hlen3 in Hrange.
    cbv [limb_radix SM2_BYTE_BASE U64_MOD] in Hrange.
    exact Hrange.
  }
  assert (Hparts : bytes = bytes0 ++ bytes1 ++ bytes2 ++ bytes3).
  {
    unfold bytes0, bytes1, bytes2, bytes3.
    rewrite <- (sublist_self bytes 32 (eq_sym Hlength)) at 1.
    rewrite (sublist_split 0 32 8 bytes) by lia.
    rewrite (sublist_split 8 32 16 bytes) by lia.
    rewrite (sublist_split 16 32 24 bytes) by lia.
    reflexivity.
  }
  assert (Hlimbs : value = u256_of_limbs x0 x1 x2 x3).
  {
    unfold u8_list_value in Hvalue.
    rewrite Hparts in Hvalue.
    repeat rewrite limb_list_value_app in Hvalue.
    rewrite Hlen0, Hlen1, Hlen2 in Hvalue.
    unfold x0, x1, x2, x3, u8_list_value.
    unfold limb_radix, SM2_BYTE_BASE in Hvalue.
    change (256 ^ 8) with U64_MOD in Hvalue.
    unfold u256_of_limbs.
    unfold SM2_BYTE_BASE.
    ring_simplify in Hvalue.
    ring_simplify.
    lia.
  }
  assert (Htail1 : Zlength (bytes1 ++ bytes2 ++ bytes3) = 24).
  { rewrite !Zlength_app, Hlen1, Hlen2, Hlen3. lia. }
  assert (Htail2 : Zlength (bytes2 ++ bytes3) = 16).
  { rewrite Zlength_app, Hlen2, Hlen3. lia. }
  rewrite Hparts.
  pose proof
    (UCharArray.full_split_to_full
      address 8 32 (bytes0 ++ bytes1 ++ bytes2 ++ bytes3)
      ltac:(lia)) as Hsplit0.
  replace (32 - 8) with 24 in Hsplit0 by lia.
  assert (Hsub00 :
    sublist 0 8 (bytes0 ++ bytes1 ++ bytes2 ++ bytes3) = bytes0).
  {
    replace 8 with (Zlength bytes0) by exact Hlen0.
    apply sublist_app_exact1.
  }
  assert (Hsub01 :
    sublist 8 32 (bytes0 ++ bytes1 ++ bytes2 ++ bytes3) =
      bytes1 ++ bytes2 ++ bytes3).
  {
    rewrite (sublist_split_app_r
      8 32 8 bytes0 (bytes1 ++ bytes2 ++ bytes3)) by lia.
    replace (8 - 8) with 0 by lia.
    replace (32 - 8) with 24 by lia.
    apply sublist_self.
    exact (eq_sym Htail1).
  }
  rewrite Hsub00, Hsub01 in Hsplit0.
  sep_apply Hsplit0.
  pose proof
    (UCharArray.full_split_to_full
      (address + 8 * sizeof(UCHAR)) 8 24
      (bytes1 ++ bytes2 ++ bytes3) ltac:(lia)) as Hsplit1.
  replace (24 - 8) with 16 in Hsplit1 by lia.
  assert (Hsub10 :
    sublist 0 8 (bytes1 ++ bytes2 ++ bytes3) = bytes1).
  {
    replace 8 with (Zlength bytes1) by exact Hlen1.
    apply sublist_app_exact1.
  }
  assert (Hsub11 :
    sublist 8 24 (bytes1 ++ bytes2 ++ bytes3) = bytes2 ++ bytes3).
  {
    rewrite (sublist_split_app_r
      8 24 8 bytes1 (bytes2 ++ bytes3)) by lia.
    replace (8 - 8) with 0 by lia.
    replace (24 - 8) with 16 by lia.
    apply sublist_self.
    exact (eq_sym Htail2).
  }
  rewrite Hsub10, Hsub11 in Hsplit1.
  sep_apply Hsplit1.
  pose proof
    (UCharArray.full_split_to_full
      (address + 16 * sizeof(UCHAR)) 8 16
      (bytes2 ++ bytes3) ltac:(lia)) as Hsplit2.
  replace (16 - 8) with 8 in Hsplit2 by lia.
  assert (Hsub20 : sublist 0 8 (bytes2 ++ bytes3) = bytes2).
  {
    replace 8 with (Zlength bytes2) by exact Hlen2.
    apply sublist_app_exact1.
  }
  assert (Hsub21 : sublist 8 16 (bytes2 ++ bytes3) = bytes3).
  {
    rewrite (sublist_split_app_r 8 16 8 bytes2 bytes3) by lia.
    replace (8 - 8) with 0 by lia.
    replace (16 - 8) with 8 by lia.
    apply sublist_self.
    exact (eq_sym Hlen3).
  }
  rewrite Hsub20, Hsub21 in Hsplit2.
  replace (address + 8 * sizeof(UCHAR) + 8 * sizeof(UCHAR)) with
    (address + 16 * sizeof(UCHAR)) by lia.
  rewrite Hsplit2.
  rewrite sizeof_uchar in *.
  assert (Halign8 : aligned_4 (address + 8)).
  {
    unfold aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Haligned.
    reflexivity.
  }
  assert (Halign16 : aligned_4 (address + 16)).
  {
    unfold aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Haligned.
    reflexivity.
  }
  assert (Halign24 : aligned_4 (address + 24)).
  {
    unfold aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Haligned.
    reflexivity.
  }
  sep_apply
    (u8_full8_to_store_uint64 address x0 bytes0
      Hlen0 Hbound0 ltac:(reflexivity) Haligned).
  sep_apply
    (u8_full8_to_store_uint64 (address + 8) x1 bytes1
      Hlen1 Hbound1 ltac:(reflexivity) Halign8).
  sep_apply
    (u8_full8_to_store_uint64 (address + 16) x2 bytes2
      Hlen2 Hbound2 ltac:(reflexivity) Halign16).
  replace (address + 16 * 1 + 8 * 1) with (address + 24) by lia.
  sep_apply
    (u8_full8_to_store_uint64 (address + 24) x3 bytes3
      Hlen3 Hbound3 ltac:(reflexivity) Halign24).
  unfold store_u256_limbs.
  Exists x0 x1 x2 x3.
  rewrite sizeof_uint64.
  entailer!.
  rewrite derivable1_sepcon_comm.
  replace (address + 0 * 8) with address by lia.
  replace (address + 1 * 8) with (address + 8) by lia.
  replace (address + 2 * 8) with (address + 16) by lia.
  replace (address + 3 * 8) with (address + 24) by lia.
  entailer!.
Qed.

Lemma u64_undef_full4_to_u8_undef_full32 :
  forall address,
    UInt64Array.undef_full address 4 |--
      UCharArray.undef_full address 32.
Proof.
  intros address.
  unfold UInt64Array.undef_full.
  unfold store_undef_array at 1.
  rewrite sizeof_uint64.
  simpl store_undef_array_rec.
  cbn.
  replace (address + 0) with address by lia.
  Intros.
  sep_apply_l_atomic (undef_store_uint64_to_u8_undef_full8 address).
  sep_apply_l_atomic
    (undef_store_uint64_to_u8_undef_full8 (address + 8)).
  sep_apply_l_atomic
    (undef_store_uint64_to_u8_undef_full8 (address + 16)).
  sep_apply_l_atomic
    (undef_store_uint64_to_u8_undef_full8 (address + 24)).
  eapply derivable1_trans with
    (y := UCharArray.undef_full address 8 **
          UCharArray.undef_full (address + 8) 8 **
          UCharArray.undef_full (address + 16) 8 **
          UCharArray.undef_full (address + 24) 8).
  - cancel.
  - pose proof
      (UCharArray.undef_full_merge_to_undef_full
        address 8 16 ltac:(lia)) as Hmerge01.
    rewrite sizeof_uchar in Hmerge01.
    replace (16 - 8) with 8 in Hmerge01 by lia.
    sep_apply Hmerge01.
    pose proof
      (UCharArray.undef_full_merge_to_undef_full
        (address + 16) 8 16 ltac:(lia)) as Hmerge23.
    rewrite sizeof_uchar in Hmerge23.
    replace (16 - 8) with 8 in Hmerge23 by lia.
    replace (address + 16 + 8) with (address + 24) in Hmerge23 by lia.
    replace (address + 16 + 8 * 1) with
      (address + 24) in Hmerge23 by lia.
    sep_apply Hmerge23.
    rewrite derivable1_sepcon_comm.
    pose proof
      (UCharArray.undef_full_merge_to_undef_full
        address 16 32 ltac:(lia)) as Hmerge.
    rewrite sizeof_uchar in Hmerge.
    replace (32 - 16) with 16 in Hmerge by lia.
    replace (address + 16 * 1) with
      (address + 16) in Hmerge by lia.
    exact Hmerge.
Qed.

Lemma u64_undef_full4_aligned_4 :
  forall address,
    UInt64Array.undef_full address 4 |-- “ aligned_4 address ”.
Proof.
  intros address.
  unfold UInt64Array.undef_full, store_undef_array.
  rewrite sizeof_uint64.
  simpl store_undef_array_rec.
  cbn.
  replace (address + 0) with address by lia.
  Intros.
  prop_apply (valid_undef_store_uint64 address).
  Intros.
  unfold isvalidptr_int64 in H0.
  entailer!.
Qed.

Lemma u8_undef_full32_to_u64_undef_full4 :
  forall address,
    aligned_4 address ->
    UCharArray.undef_full address 32 |--
      UInt64Array.undef_full address 4.
Proof.
  intros address Haligned.
  sep_apply
    (UCharArray.undef_full_split_to_undef_full
      address 8 32 ltac:(lia)).
  rewrite sizeof_uchar.
  sep_apply
    (UCharArray.undef_full_split_to_undef_full
      (address + 8) 8 24 ltac:(lia)).
  rewrite sizeof_uchar.
  replace (24 - 8) with 16 by lia.
  replace (address + 8 + 8 * 1) with (address + 16) by lia.
  sep_apply
    (UCharArray.undef_full_split_to_undef_full
      (address + 16) 8 16 ltac:(lia)).
  rewrite sizeof_uchar.
  replace (16 - 8) with 8 by lia.
  replace (address + 16 + 8 * 1) with (address + 24) by lia.
  assert (Halign8 : aligned_4 (address + 8)).
  {
    unfold aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Haligned.
    reflexivity.
  }
  assert (Halign16 : aligned_4 (address + 16)).
  {
    unfold aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Haligned.
    reflexivity.
  }
  assert (Halign24 : aligned_4 (address + 24)).
  {
    unfold aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Haligned.
    reflexivity.
  }
  sep_apply_l_atomic
    (u8_undef_full8_to_undef_store_uint64 address Haligned).
  sep_apply_l_atomic
    (u8_undef_full8_to_undef_store_uint64 (address + 8) Halign8).
  sep_apply_l_atomic
    (u8_undef_full8_to_undef_store_uint64 (address + 16) Halign16).
  sep_apply_l_atomic
    (u8_undef_full8_to_undef_store_uint64 (address + 24) Halign24).
  unfold UInt64Array.undef_full, store_undef_array.
  rewrite sizeof_uint64.
  simpl store_undef_array_rec.
  cbn.
  replace (address + 0) with address by lia.
  entailer!.
Qed.

Lemma undef_u256_to_u8_undef_full32 :
  forall address,
    UndefStructPredu32 address |--
      UCharArray.undef_full address 32.
Proof.
  intros address.
  unfold UndefStructPredu32.
  rewrite u32_v_field_address_eq.
  apply u64_undef_full4_to_u8_undef_full32.
Qed.

Lemma undef_u256_to_u8_undef_full32_aligned :
  forall address,
    UndefStructPredu32 address |--
      “ aligned_4 address ” && UCharArray.undef_full address 32.
Proof.
  intros address.
  unfold UndefStructPredu32.
  rewrite u32_v_field_address_eq.
  prop_apply (u64_undef_full4_aligned_4 address).
  Intros.
  sep_apply (u64_undef_full4_to_u8_undef_full32 address).
  entailer!.
Qed.

Lemma u8_undef_full32_to_undef_u256 :
  forall address,
    aligned_4 address ->
    UCharArray.undef_full address 32 |--
      UndefStructPredu32 address.
Proof.
  intros address Haligned.
  unfold UndefStructPredu32.
  rewrite u32_v_field_address_eq.
  apply u8_undef_full32_to_u64_undef_full4.
  exact Haligned.
Qed.

Local Open Scope string_scope.

Lemma store_fn_to_u8_full32 :
  forall address value,
    store_fn address value |--
    EX bytes,
      “ 0 <= value < SM2_N_Z /\
        Zlength bytes = 32 /\
        u8_list_bounded bytes /\
        u8_list_value bytes = value /\
        aligned_4 (&(address # "u32" ->ₛ "v")) ” &&
      UCharArray.full (&(address # "u32" ->ₛ "v")) 32 bytes.
Proof.
  intros address value.
  unfold store_fn, store_mod, store_u256.
  Intros.
  sep_apply
    (store_u256_limbs_to_u8_full32
      (&(address # "u32" ->ₛ "v")) value).
  Intros bytes.
  Exists bytes.
  entailer!.
Qed.

Lemma u8_full32_to_store_fn :
  forall address value bytes,
    0 <= value < SM2_N_Z ->
    Zlength bytes = 32 ->
    u8_list_bounded bytes ->
    u8_list_value bytes = value ->
    aligned_4 (&(address # "u32" ->ₛ "v")) ->
    UCharArray.full (&(address # "u32" ->ₛ "v")) 32 bytes |--
      store_fn address value.
Proof.
  intros address value bytes Hrange Hlength Hbounded Hvalue Haligned.
  unfold store_fn, store_mod, store_u256.
  entailer!.
  apply u8_full32_to_store_u256_limbs; assumption.
Qed.

Lemma store_u256_to_store_bytes32 :
  forall address value,
    store_u256 address value |--
    EX bytes,
      “ u8_list_value bytes = value /\ aligned_4 address ” &&
      byte_encoding.store_bytes address 32 bytes.
Proof.
  intros address value.
  unfold store_u256.
  rewrite u32_v_field_address_eq.
  sep_apply (store_u256_limbs_to_u8_full32 address value).
  Intros bytes.
  Exists bytes.
  unfold byte_encoding.store_bytes.
  entailer!.
Qed.

Lemma store_bytes32_to_store_u256 :
  forall address value bytes,
    u8_list_value bytes = value ->
    aligned_4 address ->
    byte_encoding.store_bytes address 32 bytes |-- store_u256 address value.
Proof.
  intros address value bytes Hvalue Haligned.
  unfold byte_encoding.store_bytes, store_u256.
  rewrite u32_v_field_address_eq.
  Intros.
  destruct H as [Hlength Hbounded].
  apply u8_full32_to_store_u256_limbs; assumption.
Qed.

Lemma store_fp_to_store_bytes32 :
  forall address value,
    store_fp address value |--
    EX bytes,
      “ 0 <= value < SM2_P_Z /\
        u8_list_value bytes = value /\ aligned_4 address ” &&
      byte_encoding.store_bytes address 32 bytes.
Proof.
  intros address value.
  unfold store_fp, store_mod.
  Intros.
  sep_apply (store_u256_to_store_bytes32 address value).
  Intros bytes.
  Exists bytes.
  entailer!.
Qed.

Lemma store_fn_to_store_bytes32 :
  forall address value,
    store_fn address value |--
    EX bytes,
      “ 0 <= value < SM2_N_Z /\
        u8_list_value bytes = value /\ aligned_4 address ” &&
      byte_encoding.store_bytes address 32 bytes.
Proof.
  intros address value.
  unfold store_fn, store_mod.
  Intros.
  sep_apply (store_u256_to_store_bytes32 address value).
  Intros bytes.
  Exists bytes.
  entailer!.
Qed.
