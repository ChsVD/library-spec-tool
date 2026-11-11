(** Shared byte-array and endian-encoding definitions. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.Applications_human.sm2.lib Require Export limb_arithmetic.

Import ListNotations.
Local Open Scope Z_scope.
Import Snaive_C_Rules.
Local Open Scope sac.

Definition SM2_BYTE_BASE : Z := 256.

Definition u8_list_value (bytes : list Z) : Z :=
  limb_list_value SM2_BYTE_BASE bytes.

Definition u8_list_bounded (bytes : list Z) : Prop :=
  limb_list_bounded SM2_BYTE_BASE bytes.

(** Byte [index] of a nonnegative scalar, in little-endian order. *)
Definition sm2_scalar_byte (scalar index : Z) : Z :=
  (scalar / SM2_BYTE_BASE ^ index) mod SM2_BYTE_BASE.

Definition store_bytes
    (address length : Z) (bytes : list Z) : Assertion :=
  “ Zlength bytes = length /\ u8_list_bounded bytes ” &&
  UCharArray.full address length bytes.

Definition be_u8_list_value (bytes : list Z) : Z :=
  limb_list_value SM2_BYTE_BASE (rev bytes).

(** State after swapping [index] matching pairs from the two ends of
    [original].  This pointwise form keeps the C loop invariant independent
    of any particular array predicate. *)
Definition byte_reverse_loop_state
    (original current : list Z) (index : Z) : Prop :=
  Zlength current = Zlength original /\
  0 <= index /\
  2 * index <= Zlength original /\
  forall position,
    0 <= position < Zlength original ->
    Znth position current 0 =
      if position <? index then
        Znth (Zlength original - 1 - position) original 0
      else if Zlength original - index <=? position then
        Znth (Zlength original - 1 - position) original 0
      else
        Znth position original 0.

Lemma Znth_rev_in_range :
  forall (values : list Z) position default,
    0 <= position < Zlength values ->
    Znth position (rev values) default =
      Znth (Zlength values - 1 - position) values default.
Proof.
  intros values position default Hposition.
  unfold Znth.
  rewrite rev_nth.
  - f_equal.
    rewrite Zlength_correct in Hposition.
    rewrite Zlength_correct.
    lia.
  - rewrite Zlength_correct in Hposition.
    lia.
Qed.

Lemma byte_reverse_loop_state_initial :
  forall original,
    byte_reverse_loop_state original original 0.
Proof.
  intros original.
  unfold byte_reverse_loop_state.
  split; [reflexivity |].
  split; [lia |].
  split.
  - pose proof (Zlength_nonneg original). lia.
  - intros position Hposition.
    rewrite (proj2 (Z.ltb_ge position 0)) by lia.
    rewrite (proj2 (Z.leb_gt (Zlength original - 0) position)) by lia.
    reflexivity.
Qed.

Lemma byte_reverse_loop_state_step :
  forall original current index,
    byte_reverse_loop_state original current index ->
    2 * (index + 1) <= Zlength original ->
    byte_reverse_loop_state original
      (replace_Znth (Zlength original - 1 - index)
        (Znth index current 0)
        (replace_Znth index
          (Znth (Zlength original - 1 - index) current 0) current))
      (index + 1).
Proof.
  intros original current index Hstate Hnext.
  unfold byte_reverse_loop_state in *.
  destruct Hstate as [Hlength [Hindex [Hhalf Hcurrent]]].
  repeat split.
  - rewrite !Zlength_replace_Znth. exact Hlength.
  - lia.
  - exact Hnext.
  - intros position Hposition.
    assert (Hindex_range : 0 <= index < Zlength current) by lia.
    assert (Hmirror_range :
      0 <= Zlength original - 1 - index < Zlength current) by lia.
    assert (Hdistinct : index <> Zlength original - 1 - index) by lia.
    destruct (position <? index + 1) eqn:Hleft.
    + assert (Hleft_bound : position < index + 1).
      { apply Z.ltb_lt. exact Hleft. }
      destruct (Z.eq_dec position index) as [-> | Hposition_index].
      * rewrite Znth_replace_Znth_Diff by
          (rewrite ?Zlength_replace_Znth; lia).
        rewrite Znth_replace_Znth_Same by exact Hindex_range.
        specialize (Hcurrent (Zlength original - 1 - index)).
        rewrite Hlength in Hmirror_range.
        specialize (Hcurrent Hmirror_range).
        rewrite (proj2
          (Z.ltb_ge (Zlength original - 1 - index) index))
          in Hcurrent by lia.
        rewrite (proj2
          (Z.leb_gt (Zlength original - index)
            (Zlength original - 1 - index)))
          in Hcurrent by lia.
        exact Hcurrent.
      * rewrite !Znth_replace_Znth_Diff by
          (rewrite ?Zlength_replace_Znth; lia).
        specialize (Hcurrent position Hposition).
        rewrite (proj2 (Z.ltb_lt position index)) in Hcurrent by lia.
        exact Hcurrent.
    + assert (Hleft_bound : index + 1 <= position).
      { apply Z.ltb_ge. exact Hleft. }
      destruct (Zlength original - (index + 1) <=? position) eqn:Hright.
      * assert (Hright_bound : Zlength original - (index + 1) <= position).
        { apply Z.leb_le. exact Hright. }
        destruct (Z.eq_dec position (Zlength original - 1 - index))
          as [-> | Hposition_mirror].
        -- rewrite Znth_replace_Znth_Same by
             (rewrite ?Zlength_replace_Znth; lia).
           specialize (Hcurrent index).
           rewrite Hlength in Hindex_range.
           specialize (Hcurrent Hindex_range).
           rewrite (proj2 (Z.ltb_ge index index)) in Hcurrent by lia.
           rewrite (proj2
             (Z.leb_gt (Zlength original - index) index))
             in Hcurrent by lia.
           replace
             (Zlength original - 1 - (Zlength original - 1 - index))
             with index by lia.
           exact Hcurrent.
        -- rewrite Znth_replace_Znth_Diff by
             (rewrite ?Zlength_replace_Znth; lia).
           rewrite Znth_replace_Znth_Diff by
             (rewrite ?Zlength_replace_Znth; lia).
           specialize (Hcurrent position Hposition).
           rewrite (proj2 (Z.ltb_ge position index)) in Hcurrent by lia.
           rewrite (proj2
             (Z.leb_le (Zlength original - index) position))
             in Hcurrent by lia.
           exact Hcurrent.
      * assert (Hright_bound : position < Zlength original - (index + 1)).
        { apply Z.leb_gt. exact Hright. }
        rewrite Znth_replace_Znth_Diff by
          (rewrite ?Zlength_replace_Znth; lia).
        rewrite Znth_replace_Znth_Diff by
          (rewrite ?Zlength_replace_Znth; lia).
        specialize (Hcurrent position Hposition).
        rewrite (proj2 (Z.ltb_ge position index)) in Hcurrent by lia.
        rewrite (proj2
          (Z.leb_gt (Zlength original - index) position))
          in Hcurrent by lia.
        exact Hcurrent.
Qed.

Lemma byte_reverse_loop_state_finished :
  forall original current index,
    byte_reverse_loop_state original current index ->
    Zlength original - 1 <= 2 * index ->
    current = rev original.
Proof.
  intros original current index Hstate Hfinished.
  unfold byte_reverse_loop_state in Hstate.
  destruct Hstate as [Hlength [Hindex [Hhalf Hcurrent]]].
  apply (proj2 (list_eq_ext current (rev original) 0)).
  split.
  - rewrite !Zlength_correct.
    rewrite length_rev.
    rewrite !Zlength_correct in Hlength.
    exact Hlength.
  - intros position Hposition.
    rewrite Znth_rev_in_range by (rewrite <- Hlength; exact Hposition).
    assert (Hposition_original :
      0 <= position < Zlength original) by
      (rewrite <- Hlength; exact Hposition).
    specialize (Hcurrent position Hposition_original).
    destruct (position <? index) eqn:Hleft.
    + exact Hcurrent.
    + assert (Hleft_bound : index <= position).
      { apply Z.ltb_ge. exact Hleft. }
      destruct (Zlength original - index <=? position) eqn:Hright.
      * exact Hcurrent.
      * assert (Hright_bound : position < Zlength original - index).
        { apply Z.leb_gt. exact Hright. }
        replace (Zlength original - 1 - position) with position by lia.
        exact Hcurrent.
Qed.

Definition uint_to_be_bytes (count : nat) (value : Z) : list Z :=
  rev
    (map (fun index => sm2_scalar_byte value (Z.of_nat index))
         (seq 0 count)).

Definition u256_to_be_bytes (value : Z) : list Z :=
  uint_to_be_bytes 32 value.

Lemma sm2_byte_base_positive : 0 < SM2_BYTE_BASE.
Proof. reflexivity. Qed.

Lemma sm2_scalar_byte_bounds :
  forall scalar index,
    0 <= index ->
    0 <= sm2_scalar_byte scalar index < SM2_BYTE_BASE.
Proof.
  intros scalar index Hindex.
  unfold sm2_scalar_byte.
  apply Z.mod_pos_bound.
  exact sm2_byte_base_positive.
Qed.

Lemma store_bytes_length :
  forall address length bytes,
    store_bytes address length bytes |-- “ Zlength bytes = length ”.
Proof.
  intros.
  unfold store_bytes.
  entailer!.
Qed.

Lemma store_bytes_bounded :
  forall address length bytes,
    store_bytes address length bytes |-- “ u8_list_bounded bytes ”.
Proof.
  intros.
  unfold store_bytes.
  entailer!.
Qed.

Lemma store_bytes_to_uchar_full :
  forall address length bytes,
    store_bytes address length bytes |--
      UCharArray.full address length bytes.
Proof.
  intros.
  unfold store_bytes.
  entailer!.
Qed.

Lemma store_bytes_address_space_bound :
  forall address length bytes,
    store_bytes address length bytes |--
      “ 0 <= length <= Int.max_unsigned + 1 ”.
Proof.
  intros.
  unfold store_bytes.
  Intros.
  prop_apply (UCharArray.full_length_range address length bytes).
  Intros.
  rewrite sizeof_uchar in H0.
  change Int.max_unsigned with addr_max_unsigned.
  entailer!; lia.
Qed.

Lemma store_bytes_empty :
  forall address,
    store_bytes address 0 nil --||-- emp.
Proof.
  intros.
  unfold store_bytes, u8_list_bounded, limb_list_bounded.
  rewrite UCharArray.full_empty.
  split; entailer!.
  intros index Hindex.
  rewrite Zlength_nil in Hindex.
  lia.
Qed.

Lemma be_u8_list_value_range :
  forall bytes,
    u8_list_bounded bytes ->
    0 <= be_u8_list_value bytes <
      SM2_BYTE_BASE ^ Zlength bytes.
Proof.
  intros bytes Hbounded.
  unfold be_u8_list_value, u8_list_bounded in *.
  pose proof
    (limb_list_value_range SM2_BYTE_BASE (rev bytes)
      ltac:(exact sm2_byte_base_positive)) as Hrange.
  rewrite limb_list_bounded_rev in Hrange.
  specialize (Hrange Hbounded).
  unfold limb_radix in Hrange.
  rewrite !Zlength_correct, length_rev in Hrange.
  rewrite Zlength_correct.
  exact Hrange.
Qed.

Local Fixpoint byte_digits_le (value : Z) (count : nat) : list Z :=
  match count with
  | O => nil
  | S rest =>
      value mod SM2_BYTE_BASE ::
      byte_digits_le (value / SM2_BYTE_BASE) rest
  end.

Local Lemma byte_digits_le_length :
  forall value count,
    Zlength (byte_digits_le value count) = Z.of_nat count.
Proof.
  intros value count.
  revert value.
  induction count as [|count IH]; intros value.
  - reflexivity.
  - cbn [byte_digits_le].
    rewrite Zlength_cons, IH, Nat2Z.inj_succ.
    lia.
Qed.

Local Lemma byte_digits_le_bounded :
  forall value count,
    0 <= value ->
    u8_list_bounded (byte_digits_le value count).
Proof.
  intros value count.
  revert value.
  induction count as [|count IH]; intros value Hvalue.
  - unfold u8_list_bounded, limb_list_bounded.
    intros index Hindex.
    rewrite Zlength_nil in Hindex.
    lia.
  - cbn [byte_digits_le].
    unfold u8_list_bounded in *.
    rewrite limb_list_bounded_cons_iff.
    split.
    + apply Z.mod_pos_bound.
      exact sm2_byte_base_positive.
    + apply IH.
      exact
        (Z.div_pos value SM2_BYTE_BASE Hvalue
          sm2_byte_base_positive).
Qed.

Local Lemma byte_digits_le_value :
  forall value count,
    0 <= value < SM2_BYTE_BASE ^ Z.of_nat count ->
    u8_list_value (byte_digits_le value count) = value.
Proof.
  intros value count.
  revert value.
  induction count as [|count IH]; intros value Hvalue.
  - cbn [byte_digits_le].
    unfold u8_list_value.
    rewrite limb_list_value_nil.
    cbn in Hvalue.
    lia.
  - cbn [byte_digits_le].
    unfold u8_list_value.
    rewrite limb_list_value_cons.
    assert (Hpower :
      SM2_BYTE_BASE ^ Z.of_nat (S count) =
      SM2_BYTE_BASE * SM2_BYTE_BASE ^ Z.of_nat count).
    {
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      reflexivity.
    }
    assert (Hquotient :
      0 <= value / SM2_BYTE_BASE <
        SM2_BYTE_BASE ^ Z.of_nat count).
    {
      split.
      - exact
          (Z.div_pos value SM2_BYTE_BASE (proj1 Hvalue)
            sm2_byte_base_positive).
      - apply Z.div_lt_upper_bound; [exact sm2_byte_base_positive |].
        rewrite <- Hpower.
        exact (proj2 Hvalue).
    }
    specialize (IH (value / SM2_BYTE_BASE) Hquotient).
    unfold u8_list_value in IH.
    rewrite IH.
    pose proof (Z.div_mod value SM2_BYTE_BASE ltac:(lia)) as Hdivmod.
    lia.
Qed.

Local Lemma byte_digits_le_scalar_bytes :
  forall value count,
    0 <= value ->
    byte_digits_le value count =
      map (fun index => sm2_scalar_byte value (Z.of_nat index))
          (seq 0 count).
Proof.
  intros value count.
  revert value.
  induction count as [|count IH]; intros value Hvalue.
  - reflexivity.
  - cbn [byte_digits_le].
    change
      (value mod SM2_BYTE_BASE ::
         byte_digits_le (value / SM2_BYTE_BASE) count =
       sm2_scalar_byte value 0 ::
         map (fun index => sm2_scalar_byte value (Z.of_nat index))
             (seq 1 count)).
    f_equal.
    + unfold sm2_scalar_byte.
      rewrite Z.pow_0_r, Z.div_1_r.
      reflexivity.
    + rewrite <- (seq_shift count 0), map_map.
      rewrite (IH (value / SM2_BYTE_BASE)) by
        (exact
          (Z.div_pos value SM2_BYTE_BASE Hvalue
            sm2_byte_base_positive)).
      apply map_ext.
      intros index.
      unfold sm2_scalar_byte.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite Z.div_div by
        (unfold SM2_BYTE_BASE; try lia; apply Z.pow_pos_nonneg; lia).
      reflexivity.
Qed.

Lemma uint_to_be_bytes_length :
  forall count value,
    Zlength (uint_to_be_bytes count value) = Z.of_nat count.
Proof.
  intros count value.
  unfold uint_to_be_bytes.
  rewrite !Zlength_correct, length_rev, length_map, length_seq.
  reflexivity.
Qed.

Lemma uint_to_be_bytes_bounded :
  forall count value,
    0 <= value ->
    u8_list_bounded (uint_to_be_bytes count value).
Proof.
  intros count value Hvalue.
  unfold uint_to_be_bytes.
  rewrite <- byte_digits_le_scalar_bytes by exact Hvalue.
  unfold u8_list_bounded.
  rewrite limb_list_bounded_rev.
  apply byte_digits_le_bounded.
  exact Hvalue.
Qed.

Lemma be_u8_list_value_uint_to_be_bytes :
  forall count value,
    0 <= value < SM2_BYTE_BASE ^ Z.of_nat count ->
    be_u8_list_value (uint_to_be_bytes count value) = value.
Proof.
  intros count value Hvalue.
  unfold be_u8_list_value, uint_to_be_bytes.
  rewrite rev_involutive.
  rewrite <- byte_digits_le_scalar_bytes by lia.
  apply byte_digits_le_value.
  exact Hvalue.
Qed.

Lemma u256_to_be_bytes_length :
  forall value,
    Zlength (u256_to_be_bytes value) = 32.
Proof.
  intros value.
  unfold u256_to_be_bytes.
  rewrite uint_to_be_bytes_length.
  reflexivity.
Qed.

Lemma u256_to_be_bytes_bounded :
  forall value,
    0 <= value ->
    u8_list_bounded (u256_to_be_bytes value).
Proof.
  intros value Hvalue.
  unfold u256_to_be_bytes.
  apply uint_to_be_bytes_bounded.
  exact Hvalue.
Qed.

Lemma be_u8_list_value_u256_to_be_bytes :
  forall value,
    0 <= value < 2 ^ 256 ->
    be_u8_list_value (u256_to_be_bytes value) = value.
Proof.
  intros value Hvalue.
  unfold u256_to_be_bytes.
  apply be_u8_list_value_uint_to_be_bytes.
  change (0 <= value < 2 ^ 256).
  exact Hvalue.
Qed.

Lemma u256_to_be_bytes_properties :
  forall value,
    0 <= value < 2 ^ 256 ->
    Zlength (u256_to_be_bytes value) = 32 /\
    u8_list_bounded (u256_to_be_bytes value) /\
    be_u8_list_value (u256_to_be_bytes value) = value.
Proof.
  intros value Hvalue.
  split.
  - apply u256_to_be_bytes_length.
  - split.
    + apply u256_to_be_bytes_bounded; lia.
    + apply be_u8_list_value_u256_to_be_bytes.
      exact Hvalue.
Qed.

Lemma u8_list_value_injective :
  forall left right,
    Zlength left = Zlength right ->
    u8_list_bounded left ->
    u8_list_bounded right ->
    u8_list_value left = u8_list_value right ->
    left = right.
Proof.
  induction left as [|x xs IH]; intros right Hlength Hleft Hright Hvalue.
  - destruct right as [|y ys].
    + reflexivity.
    + rewrite Zlength_nil, Zlength_cons in Hlength.
      pose proof (Zlength_nonneg ys).
      lia.
  - destruct right as [|y ys].
    + rewrite Zlength_cons, Zlength_nil in Hlength.
      pose proof (Zlength_nonneg xs).
      lia.
    + apply limb_list_bounded_cons_iff in Hleft as [Hx Hxs].
      apply limb_list_bounded_cons_iff in Hright as [Hy Hys].
      unfold u8_list_value in Hvalue.
      rewrite !limb_list_value_cons in Hvalue.
      assert (Hhead : x = y).
      {
        assert (Hxmod :
          (x + SM2_BYTE_BASE * limb_list_value SM2_BYTE_BASE xs)
            mod SM2_BYTE_BASE = x).
        {
          rewrite Z.add_mod, Z.mul_mod, Z.mod_same.
          rewrite Z.mul_0_l, Z.add_0_r.
          rewrite Z.mod_mod by (unfold SM2_BYTE_BASE; lia).
          rewrite Z.mod_small by exact Hx.
          reflexivity.
          all: unfold SM2_BYTE_BASE; lia.
        }
        assert (Hymod :
          (y + SM2_BYTE_BASE * limb_list_value SM2_BYTE_BASE ys)
            mod SM2_BYTE_BASE = y).
        {
          rewrite Z.add_mod, Z.mul_mod, Z.mod_same.
          rewrite Z.mul_0_l, Z.add_0_r.
          rewrite Z.mod_mod by (unfold SM2_BYTE_BASE; lia).
          rewrite Z.mod_small by exact Hy.
          reflexivity.
          all: unfold SM2_BYTE_BASE; lia.
        }
        rewrite <- Hxmod, <- Hymod, Hvalue.
        reflexivity.
      }
      f_equal.
      * exact Hhead.
      * apply IH.
        -- rewrite !Zlength_cons in Hlength. lia.
        -- exact Hxs.
        -- exact Hys.
        -- unfold u8_list_value.
           apply (Z.mul_reg_l _ _ 256); [lia |].
           rewrite Hhead in Hvalue.
           unfold SM2_BYTE_BASE in Hvalue.
           change SM2_BYTE_BASE with 256.
           lia.
Qed.

Lemma uint_to_be_bytes_unique :
  forall count value bytes,
    0 <= value < SM2_BYTE_BASE ^ Z.of_nat count ->
    Zlength bytes = Z.of_nat count ->
    u8_list_bounded bytes ->
    be_u8_list_value bytes = value ->
    bytes = uint_to_be_bytes count value.
Proof.
  intros count value bytes Hrange Hlength Hbounded Hvalue.
  assert (Hgenerated_length :
    Zlength (uint_to_be_bytes count value) = Z.of_nat count).
  { apply uint_to_be_bytes_length. }
  assert (Hgenerated_bounded :
    u8_list_bounded (uint_to_be_bytes count value)).
  { apply uint_to_be_bytes_bounded. lia. }
  assert (Hgenerated_value :
    be_u8_list_value (uint_to_be_bytes count value) = value).
  { apply be_u8_list_value_uint_to_be_bytes. exact Hrange. }
  assert (Hreversed :
    rev bytes = rev (uint_to_be_bytes count value)).
  {
    apply u8_list_value_injective.
    - rewrite !Zlength_correct, !length_rev.
      rewrite <- !Zlength_correct.
      lia.
    - unfold u8_list_bounded in *.
      rewrite limb_list_bounded_rev.
      exact Hbounded.
    - unfold u8_list_bounded in *.
      rewrite limb_list_bounded_rev.
      exact Hgenerated_bounded.
    - unfold be_u8_list_value in Hvalue, Hgenerated_value.
      unfold u8_list_value.
      rewrite Hvalue, Hgenerated_value.
      reflexivity.
  }
  apply (f_equal (@rev Z)) in Hreversed.
  rewrite !rev_involutive in Hreversed.
  exact Hreversed.
Qed.

Lemma uint_to_be_bytes_from_little_endian :
  forall count value bytes,
    0 <= value < SM2_BYTE_BASE ^ Z.of_nat count ->
    Zlength bytes = Z.of_nat count ->
    u8_list_bounded bytes ->
    u8_list_value bytes = value ->
    rev bytes = uint_to_be_bytes count value.
Proof.
  intros count value bytes Hrange Hlength Hbounded Hvalue.
  apply uint_to_be_bytes_unique.
  - exact Hrange.
  - rewrite !Zlength_correct, length_rev.
    rewrite <- Zlength_correct.
    exact Hlength.
  - unfold u8_list_bounded in *.
    rewrite limb_list_bounded_rev.
    exact Hbounded.
  - unfold be_u8_list_value.
    rewrite rev_involutive.
    exact Hvalue.
Qed.

Lemma u256_to_be_bytes_from_little_endian :
  forall value bytes,
    0 <= value < 2 ^ 256 ->
    Zlength bytes = 32 ->
    u8_list_bounded bytes ->
    u8_list_value bytes = value ->
    rev bytes = u256_to_be_bytes value.
Proof.
  intros value bytes Hrange Hlength Hbounded Hvalue.
  unfold u256_to_be_bytes.
  apply uint_to_be_bytes_from_little_endian; try assumption.
Qed.
