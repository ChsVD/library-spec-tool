(** Mathematical properties of the bit operations emitted by QCP. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import IntLib.

Local Open Scope Z_scope.

Lemma pow2_range_log2 :
  forall width value,
    0 < width ->
    0 <= value < 2 ^ width ->
    Z.log2 value < width.
Proof.
  intros width value Hwidth Hrange.
  destruct (Z.eq_dec value 0) as [-> | Hnonzero].
  - simpl. lia.
  - apply (proj1 (Z.log2_lt_pow2 value width ltac:(lia))).
    lia.
Qed.

Lemma land_range_pow2 :
  forall width left right,
    0 < width ->
    0 <= left < 2 ^ width ->
    0 <= right < 2 ^ width ->
    0 <= Z.land left right < 2 ^ width.
Proof.
  intros width left right Hwidth Hleft Hright.
  pose proof (pow2_range_log2 width left Hwidth Hleft) as Hleft_log.
  assert (Hresult_nonneg : 0 <= Z.land left right).
  { apply (proj2 (Z.land_nonneg left right)). left. lia. }
  split; [exact Hresult_nonneg |].
  destruct (Z.eq_dec (Z.land left right) 0) as [-> | Hnonzero].
  - pose proof (Z.pow_pos_nonneg 2 width ltac:(lia) ltac:(lia)). lia.
  - apply (proj2 (Z.log2_lt_pow2 (Z.land left right) width ltac:(lia))).
    pose proof (Z.log2_land left right ltac:(lia) ltac:(lia)).
    lia.
Qed.

Lemma lor_range_pow2 :
  forall width left right,
    0 < width ->
    0 <= left < 2 ^ width ->
    0 <= right < 2 ^ width ->
    0 <= Z.lor left right < 2 ^ width.
Proof.
  intros width left right Hwidth Hleft Hright.
  pose proof (pow2_range_log2 width left Hwidth Hleft) as Hleft_log.
  pose proof (pow2_range_log2 width right Hwidth Hright) as Hright_log.
  assert (Hresult_nonneg : 0 <= Z.lor left right).
  { apply (proj2 (Z.lor_nonneg left right)). lia. }
  split; [exact Hresult_nonneg |].
  destruct (Z.eq_dec (Z.lor left right) 0) as [-> | Hnonzero].
  - pose proof (Z.pow_pos_nonneg 2 width ltac:(lia) ltac:(lia)). lia.
  - apply (proj2 (Z.log2_lt_pow2 (Z.lor left right) width ltac:(lia))).
    rewrite Z.log2_lor by lia.
    apply Z.max_lub_lt; lia.
Qed.

Lemma lxor_range_pow2 :
  forall width left right,
    0 < width ->
    0 <= left < 2 ^ width ->
    0 <= right < 2 ^ width ->
    0 <= Z.lxor left right < 2 ^ width.
Proof.
  intros width left right Hwidth Hleft Hright.
  pose proof (pow2_range_log2 width left Hwidth Hleft) as Hleft_log.
  pose proof (pow2_range_log2 width right Hwidth Hright) as Hright_log.
  assert (Hresult_nonneg : 0 <= Z.lxor left right).
  { apply (proj2 (Z.lxor_nonneg left right)). lia. }
  split; [exact Hresult_nonneg |].
  destruct (Z.eq_dec (Z.lxor left right) 0) as [-> | Hnonzero].
  - pose proof (Z.pow_pos_nonneg 2 width ltac:(lia) ltac:(lia)). lia.
  - apply (proj2 (Z.log2_lt_pow2 (Z.lxor left right) width ltac:(lia))).
    pose proof (Z.log2_lxor left right ltac:(lia) ltac:(lia)).
    assert (Z.max (Z.log2 left) (Z.log2 right) < width).
    { apply Z.max_lub_lt; lia. }
    lia.
Qed.

Lemma shiftr_range_pow2 :
  forall width value amount,
    0 < width ->
    0 <= value < 2 ^ width ->
    0 <= amount ->
    0 <= Z.shiftr value amount < 2 ^ width.
Proof.
  intros width value amount Hwidth Hvalue Hamount.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hpow : 0 < 2 ^ amount) by (apply Z.pow_pos_nonneg; lia).
  split.
  - apply Z.div_pos; lia.
  - apply Z.le_lt_trans with value; try lia.
    apply Z.div_le_upper_bound; try lia.
    nia.
Qed.

Lemma unsigned_lnot_formula :
  forall width value,
    0 < width ->
    unsigned_last_nbits (Z.lnot value) width =
      2 ^ width - 1 - unsigned_last_nbits value width.
Proof.
  intros width value Hwidth.
  pose proof (unsigned_Lastnbits_range value width ltac:(lia)) as Hrange.
  rewrite Z.lnot_eq_pred_opp.
  unfold unsigned_last_nbits in *.
  symmetry.
  apply Z.mod_unique with (q := -(value / 2 ^ width) - 1).
  - left. lia.
  - pose proof (Z.div_mod value (2 ^ width) ltac:(
      apply Z.pow_nonzero; lia)).
    lia.
Qed.

Lemma land_lnot_unsigned :
  forall width left right,
    0 < width ->
    0 <= right < 2 ^ width ->
    Z.land (Z.lnot left) right =
      Z.land (unsigned_last_nbits (Z.lnot left) width) right.
Proof.
  intros width left right Hwidth Hright.
  unfold unsigned_last_nbits.
  rewrite <- Z.land_ones by lia.
  rewrite <- Z.land_assoc.
  replace (Z.land (Z.ones width) right) with right; [reflexivity |].
  rewrite Z.land_comm, Z.land_ones by lia.
  symmetry.
  apply Z.mod_small.
  lia.
Qed.

Lemma land_lnot_range_pow2 :
  forall width left right,
    0 < width ->
    0 <= right < 2 ^ width ->
    0 <= Z.land (Z.lnot left) right < 2 ^ width.
Proof.
  intros width left right Hwidth Hright.
  rewrite (land_lnot_unsigned width left right Hwidth Hright).
  apply land_range_pow2; try assumption.
  apply unsigned_Lastnbits_range.
  lia.
Qed.

Definition rotate_left (width value amount : Z) : Z :=
  let shift := amount mod width in
  Z.lor
    (unsigned_last_nbits (Z.shiftl value shift) width)
    (Z.shiftr value (width - shift)).

Lemma rotate_left_count_range :
  forall width amount,
    0 < width ->
    0 <= amount mod width < width.
Proof.
  intros width amount Hwidth.
  apply Z.mod_pos_bound.
  lia.
Qed.

Lemma rotate_left_range_pow2 :
  forall width value amount,
    0 < width ->
    0 <= value < 2 ^ width ->
    0 <= rotate_left width value amount < 2 ^ width.
Proof.
  intros width value amount Hwidth Hvalue.
  unfold rotate_left.
  apply lor_range_pow2; try lia.
  - apply unsigned_Lastnbits_range. lia.
  - apply shiftr_range_pow2; try assumption.
    pose proof (rotate_left_count_range width amount Hwidth).
    lia.
Qed.

Lemma rotate_left_frontend_equiv :
  forall width value amount,
    0 < width ->
    Z.lor
      (unsigned_last_nbits
        (Z.shiftl value (amount mod width)) width)
      (Z.shiftr value
        (unsigned_last_nbits (width - amount mod width) width)) =
    rotate_left width value amount.
Proof.
  intros width value amount Hwidth.
  unfold rotate_left.
  pose proof (rotate_left_count_range width amount Hwidth) as Hshift.
  assert (Hcount :
    unsigned_last_nbits (width - amount mod width) width =
    width - amount mod width).
  {
    apply unsigned_last_nbits_eq.
    split; [lia |].
    pose proof (Z.pow_gt_lin_r 2 width ltac:(lia) ltac:(lia)).
    lia.
  }
  rewrite Hcount.
  reflexivity.
Qed.

(** Reversal of the four bytes of a 32-bit unsigned word. *)
Definition byte_swap32 (value : Z) : Z :=
  ((value / 2 ^ 24) mod 256) +
  ((value / 2 ^ 16) mod 256) * 2 ^ 8 +
  ((value / 2 ^ 8) mod 256) * 2 ^ 16 +
  (value mod 256) * 2 ^ 24.

Lemma land_shiftl_ones :
  forall value width offset,
    0 <= width ->
    0 <= offset ->
    Z.land value (Z.shiftl (Z.ones width) offset) =
      Z.shiftl
        (Z.land (Z.shiftr value offset) (Z.ones width))
        offset.
Proof.
  intros value width offset Hwidth Hoffset.
  apply Z.bits_inj'.
  intros bit Hbit.
  rewrite Z.land_spec.
  rewrite !Z.shiftl_spec by lia.
  destruct (bit <? offset) eqn:Hbelow.
  - apply Z.ltb_lt in Hbelow.
    rewrite Z.land_spec.
    assert (Hmask :
      Z.testbit (Z.ones width) (bit - offset) = false).
    { apply Z.testbit_neg_r. lia. }
    rewrite Hmask.
    destruct (Z.testbit value bit),
      (Z.testbit (Z.shiftr value offset) (bit - offset));
    reflexivity.
  - apply Z.ltb_ge in Hbelow.
    rewrite Z.land_spec, Z.shiftr_spec by lia.
    replace (bit - offset + offset) with bit by lia.
    reflexivity.
Qed.

Lemma lor_low_high_add :
  forall low high width,
    0 <= width ->
    0 <= low < 2 ^ width ->
    0 <= high ->
    Z.lor low (high * 2 ^ width) =
      low + high * 2 ^ width.
Proof.
  intros low high width Hwidth Hlow Hhigh.
  assert (Hland : Z.land low (high * 2 ^ width) = 0).
  {
    apply Z.bits_inj_0.
    intros bit.
    rewrite Z.land_spec.
    destruct (bit <? width) eqn:Hbit.
    - apply Z.ltb_lt in Hbit.
      rewrite Z.mul_pow2_bits_low by lia.
      destruct (Z.testbit low bit); reflexivity.
    - apply Z.ltb_ge in Hbit.
      assert (Hmod : low mod 2 ^ width = low).
      { apply Z.mod_small. exact Hlow. }
      rewrite <- Hmod at 1.
      rewrite Z.mod_pow2_bits_high by lia.
      reflexivity.
  }
  rewrite <- (Z.lxor_lor low (high * 2 ^ width) Hland).
  pose proof (Z.add_lxor_2land low (high * 2 ^ width)).
  rewrite Hland in H.
  lia.
Qed.

Lemma byte_swap32_range :
  forall value,
    0 <= byte_swap32 value < 2 ^ 32.
Proof.
  intros value.
  pose proof (Z.mod_pos_bound (value / 2 ^ 24) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (value / 2 ^ 16) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (value / 2 ^ 8) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound value 256 ltac:(lia)).
  unfold byte_swap32.
  cbv [Z.pow].
  lia.
Qed.

Lemma byte_swap32_frontend_equiv :
  forall value,
    0 <= value < 2 ^ 32 ->
    Z.lor
      (Z.lor
        (Z.lor
          (Z.shiftr value 24)
          (Z.land (Z.shiftr value 8) 65280))
        (Z.land
          (unsigned_last_nbits (Z.shiftl value 8) 32)
          16711680))
      (unsigned_last_nbits (Z.shiftl value 24) 32) =
    byte_swap32 value.
Proof.
  intros value Hvalue.
  change (0 <= value < 4294967296) in Hvalue.
  set (b0 := value mod 256).
  set (b1 := (value / 2 ^ 8) mod 256).
  set (b2 := (value / 2 ^ 16) mod 256).
  set (b3 := (value / 2 ^ 24) mod 256).
  assert (Hb0 : 0 <= b0 < 256).
  { unfold b0. apply Z.mod_pos_bound. lia. }
  assert (Hb1 : 0 <= b1 < 256).
  { unfold b1. apply Z.mod_pos_bound. lia. }
  assert (Hb2 : 0 <= b2 < 256).
  { unfold b2. apply Z.mod_pos_bound. lia. }
  assert (Hb3 : 0 <= b3 < 256).
  { unfold b3. apply Z.mod_pos_bound. lia. }
  assert (Hhigh : Z.shiftr value 24 = b3).
  {
    unfold b3.
    rewrite Z.shiftr_div_pow2 by lia.
    apply eq_sym, Z.mod_small.
    change (0 <= value / 16777216 < 256).
    split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
  }
  assert (Hmiddle_high :
    Z.land (Z.shiftr value 8) 65280 = b2 * 2 ^ 8).
  {
    change 65280 with (Z.shiftl (Z.ones 8) 8).
    rewrite land_shiftl_ones by lia.
    rewrite Z.shiftr_shiftr by lia.
    replace (8 + 8) with 16 by lia.
    rewrite Z.land_ones by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    unfold b2.
    reflexivity.
  }
  assert (Hmiddle_low :
    Z.land
      (unsigned_last_nbits (Z.shiftl value 8) 32)
      16711680 = b1 * 2 ^ 16).
  {
    assert (Hmask :
      unsigned_last_nbits 16711680 32 = 16711680).
    {
      apply unsigned_last_nbits_eq.
      change (0 <= 16711680 < 4294967296).
      lia.
    }
    rewrite <- Hmask at 1.
    rewrite unsigned_last_nbits_land_clear_l by lia.
    rewrite Hmask.
    change 16711680 with (Z.shiftl (Z.ones 8) 16).
    rewrite land_shiftl_ones by lia.
    rewrite Z.shiftr_shiftl_r by lia.
    replace (16 - 8) with 8 by lia.
    rewrite Z.land_ones by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    unfold b1.
    reflexivity.
  }
  assert (Hlow :
    unsigned_last_nbits (Z.shiftl value 24) 32 =
      b0 * 2 ^ 24).
  {
    unfold unsigned_last_nbits, b0.
    rewrite Z.shiftl_mul_pow2 by lia.
    pose proof (Z.div_mod value 256 ltac:(lia)) as Hdiv.
    change
      ((value * 16777216) mod 4294967296 =
       (value mod 256) * 16777216).
    replace (value * 16777216) with
      ((value mod 256) * 16777216 +
       (value / 256) * 4294967296) by lia.
    rewrite Z.mod_add by lia.
    rewrite Z.mod_small.
    - reflexivity.
    - pose proof (Z.mod_pos_bound value 256 ltac:(lia)).
      lia.
  }
  rewrite Hhigh, Hmiddle_high, Hmiddle_low, Hlow.
  assert (Hlor1 :
    Z.lor b3 (b2 * 2 ^ 8) = b3 + b2 * 2 ^ 8).
  {
    apply lor_low_high_add.
    - lia.
    - change (0 <= b3 < 256). exact Hb3.
    - lia.
  }
  assert (Hpair1 :
    0 <= b3 + b2 * 2 ^ 8 < 2 ^ 16).
  { change (0 <= b3 + b2 * 256 < 65536). lia. }
  assert (Hlor2 :
    Z.lor (b3 + b2 * 2 ^ 8) (b1 * 2 ^ 16) =
      b3 + b2 * 2 ^ 8 + b1 * 2 ^ 16).
  {
    apply lor_low_high_add.
    - lia.
    - exact Hpair1.
    - lia.
  }
  assert (Hpair2 :
    0 <= b3 + b2 * 2 ^ 8 + b1 * 2 ^ 16 < 2 ^ 24).
  {
    change
      (0 <= b3 + b2 * 256 + b1 * 65536 < 16777216).
    lia.
  }
  assert (Hlor3 :
    Z.lor
      (b3 + b2 * 2 ^ 8 + b1 * 2 ^ 16)
      (b0 * 2 ^ 24) =
    b3 + b2 * 2 ^ 8 + b1 * 2 ^ 16 + b0 * 2 ^ 24).
  {
    apply lor_low_high_add.
    - lia.
    - exact Hpair2.
    - lia.
  }
  rewrite Hlor1, Hlor2, Hlor3.
  unfold byte_swap32, b0, b1, b2, b3.
  reflexivity.
Qed.
