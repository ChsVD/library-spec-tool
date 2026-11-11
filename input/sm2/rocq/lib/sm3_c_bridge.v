(** Bridges the C implementation's pre-rotated [Ti] table to standard SM3. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import AUXLib.ListLib.
From SimpleC.EE.Applications_human.sm2.lib Require Export sm3.

Import ListNotations.
Local Open Scope Z_scope.

Definition SM3_TI_VALUES : list Z :=
  map
    (fun index => sm3_round_constant (Z.of_nat index))
    (seq 0 64).

Lemma SM3_TI_VALUES_length : Zlength SM3_TI_VALUES = 64.
Proof.
  unfold SM3_TI_VALUES.
  rewrite !Zlength_correct, length_map, length_seq.
  reflexivity.
Qed.

Lemma SM3_TI_VALUES_bounded :
  limb_list_bounded SM3_WORD_MODULUS SM3_TI_VALUES.
Proof.
  apply (proj2
    (limb_list_bounded_iff_Forall
      SM3_WORD_MODULUS SM3_TI_VALUES)).
  unfold SM3_TI_VALUES.
  apply Forall_map.
  apply Forall_forall.
  intros index Hindex.
  apply sm3_round_constant_range.
Qed.

Lemma SM3_TI_VALUES_Znth :
  forall index,
    0 <= index < 64 ->
    Znth index SM3_TI_VALUES 0 = sm3_round_constant index.
Proof.
  intros index Hindex.
  unfold SM3_TI_VALUES, Znth.
  transitivity
    (nth (Z.to_nat index)
      (map
        (fun index0 : nat => sm3_round_constant (Z.of_nat index0))
        (seq 0 64))
      (sm3_round_constant (Z.of_nat O))).
  - apply (@nth_indep Z).
    rewrite length_map, length_seq.
    lia.
  - rewrite <- (Z2Nat.id index) at 2 by lia.
    change
      (nth (Z.to_nat index)
        (map
          (fun index0 : nat => sm3_round_constant (Z.of_nat index0))
          (seq 0 64))
        ((fun index0 : nat =>
          sm3_round_constant (Z.of_nat index0)) O) =
       (fun index0 : nat =>
          sm3_round_constant (Z.of_nat index0)) (Z.to_nat index)).
    transitivity
      ((fun index0 : nat =>
          sm3_round_constant (Z.of_nat index0))
        (nth (Z.to_nat index) (seq 0 64) O)).
    + exact (@map_nth nat Z
        (fun index0 : nat =>
          sm3_round_constant (Z.of_nat index0))
        (seq 0 64) O (Z.to_nat index)).
    + f_equal.
      rewrite seq_nth by lia.
      lia.
Qed.

Lemma u8_list_value_uint_to_be_bytes4 :
  forall value,
    0 <= value < 2 ^ 32 ->
    u8_list_value (uint_to_be_bytes 4 value) = byte_swap32 value.
Proof.
  intros value Hvalue.
  assert (Hbytes :
    uint_to_be_bytes 4 value =
      [sm2_scalar_byte value 3; sm2_scalar_byte value 2;
       sm2_scalar_byte value 1; sm2_scalar_byte value 0]).
  { reflexivity. }
  rewrite Hbytes.
  unfold u8_list_value.
  repeat rewrite limb_list_value_cons.
  rewrite limb_list_value_nil.
  unfold sm2_scalar_byte, byte_swap32,
    SM2_BYTE_BASE, limb_radix.
  cbn [Z.of_nat].
  change
    ((value / 16777216) mod 256 +
     256 *
       ((value / 65536) mod 256 +
        256 *
          ((value / 256) mod 256 +
           256 * ((value / 1) mod 256 + 256 * 0))) =
     (value / 16777216) mod 256 +
     (value / 65536) mod 256 * 256 +
     (value / 256) mod 256 * 65536 +
     value mod 256 * 16777216).
  rewrite Z.div_1_r.
  ring.
Qed.

Lemma byte_swap32_little_endian_value :
  forall bytes value,
    Zlength bytes = 4 ->
    u8_list_bounded bytes ->
    u8_list_value bytes = value ->
    byte_swap32 value = be_u8_list_value bytes.
Proof.
  intros bytes value Hlength Hbounded Hvalue.
  assert (Hrange : 0 <= value < 2 ^ 32).
  {
    unfold u8_list_value in Hvalue.
    pose proof
      (limb_list_value_range SM2_BYTE_BASE bytes
        ltac:(unfold SM2_BYTE_BASE; lia) Hbounded) as Hrange.
    rewrite Hvalue, Hlength in Hrange.
    change (0 <= value < 2 ^ 32).
    exact Hrange.
  }
  pose proof
    (uint_to_be_bytes_from_little_endian
      4 value bytes ltac:(
        change (0 <= value < 2 ^ 32); exact Hrange)
      Hlength Hbounded Hvalue) as Hbytes.
  unfold be_u8_list_value.
  rewrite Hbytes.
  symmetry.
  apply u8_list_value_uint_to_be_bytes4.
  exact Hrange.
Qed.

Lemma sm3_block_word_from_little_endian :
  forall block index,
    Zlength block = 64 ->
    u8_list_bounded block ->
    0 <= index < 16 ->
    byte_swap32
      (u8_list_value
        (sublist (4 * index) (4 * index + 4) block)) =
      sm3_block_word block index.
Proof.
  intros block index Hlength Hbounded Hindex.
  unfold sm3_block_word.
  apply byte_swap32_little_endian_value.
  - rewrite Zlength_sublist by lia.
    lia.
  - unfold u8_list_bounded in *.
    apply limb_list_bounded_sublist; [exact Hbounded |].
    rewrite Hlength.
    lia.
  - reflexivity.
Qed.
