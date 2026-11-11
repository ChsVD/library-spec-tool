(** Reusable pure phase facts for the SM3 finalization proof. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import int_auto ListLib.
From SimpleC.SL Require Import IntLib Mem SeparationLogic.
From SimpleC.EE.Applications_human.sm2.lib Require Import
  bitwise sm2_common_lib sm3_def.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Local Open Scope sac.

Lemma sm3_final_bytes_length_at_least_block :
  forall message,
    64 <= Zlength (sm3_final_bytes message).
Proof.
  intros message.
  pose proof (sm3_final_bytes_length message) as Hlength.
  pose proof (sm3_tail_length_range message) as Htail.
  pose proof
    (sm3_padding_zero_count_range (Zlength message)) as Hpadding.
  pose proof (sm3_final_bytes_length_multiple message) as Hmultiple.
  assert (Hpositive : 0 < Zlength (sm3_final_bytes message)) by lia.
  destruct (Z_lt_ge_dec (Zlength (sm3_final_bytes message)) 64).
  - rewrite Z.mod_small in Hmultiple by lia.
    lia.
  - lia.
Qed.

Lemma sm3_final_bytes_last_eight :
  forall message,
    sublist
      (Zlength (sm3_final_bytes message) - 8)
      (Zlength (sm3_final_bytes message))
      (sm3_final_bytes message) =
    u64_to_be_bytes (8 * Zlength message).
Proof.
  intros message.
  unfold sm3_final_bytes.
  rewrite !app_assoc.
  set (padding :=
    (sm3_tail message ++ [128]) ++
    repeat 0
      (Z.to_nat (sm3_padding_zero_count (Zlength message)))).
  set (length_bytes := u64_to_be_bytes (8 * Zlength message)).
  assert (Hlength_bytes : Zlength length_bytes = 8).
  { unfold length_bytes. apply u64_to_be_bytes_length. }
  change
    (sublist (Zlength (padding ++ length_bytes) - 8)
       (Zlength (padding ++ length_bytes))
       (padding ++ length_bytes) =
     u64_to_be_bytes (8 * Zlength message)).
  rewrite Zlength_app, Hlength_bytes.
  replace (Zlength padding + 8 - 8) with (Zlength padding) by lia.
  rewrite (sublist_split_app_r
    (Zlength padding) (Zlength padding + 8) (Zlength padding)
    padding length_bytes) by lia.
  replace (Zlength padding - Zlength padding) with 0 by lia.
  replace (Zlength padding + 8 - Zlength padding) with 8 by lia.
  rewrite sublist_self by exact Hlength_bytes.
  unfold length_bytes.
  reflexivity.
Qed.

(** Canonical two-block view of finalization when the buffered tail has at
    least 56 bytes.  Only the semantic tail identity and branch bounds are
    needed; all memory and alignment facts remain with callers. *)
Lemma sm3_final_long_padding_view :
  forall message tail,
    tail = sm3_tail message ->
    56 <= Zlength tail < 64 ->
    let first_block :=
      (tail +:: 128) ++ repeat_Z 0 (63 - Zlength tail) in
    sm3_final_bytes message =
      first_block ++ repeat_Z 0 56 ++
        u64_to_be_bytes (8 * Zlength message) /\
    Zlength first_block = 64 /\
    Zlength (sm3_final_bytes message) = 128 /\
    first_block =
      sublist 0 (Zlength (sm3_final_bytes message) - 64)
        (sm3_final_bytes message) /\
    repeat_Z 0 56 =
      sublist (Zlength (sm3_final_bytes message) - 64)
        (Zlength (sm3_final_bytes message) - 8)
        (sm3_final_bytes message).
Proof.
  intros message tail Htail Hrange.
  cbn zeta.
  assert (Htail_mod : Zlength tail = Zlength message mod 64).
  { rewrite Htail. apply sm3_tail_length. }
  pose proof (Z.div_mod (Zlength message) 64 ltac:(lia)) as Hdivmod.
  assert (Hzero :
      sm3_padding_zero_count (Zlength message) = 119 - Zlength tail).
  { unfold sm3_padding_zero_count.
    symmetry.
    apply Z.mod_unique with (q := -(Zlength message / 64) - 1); lia. }
  assert (Hfinal :
      sm3_final_bytes message =
        (((tail +:: 128) ++ repeat_Z 0 (63 - Zlength tail)) ++
         repeat_Z 0 56 ++ u64_to_be_bytes (8 * Zlength message))).
  { unfold sm3_final_bytes, repeat_Z.
    rewrite <- Htail, Hzero.
    replace (119 - Zlength tail) with
      ((63 - Zlength tail) + 56) by lia.
    rewrite Z2Nat.inj_add by lia.
    rewrite repeat_app, !app_assoc.
    reflexivity. }
  assert (Hfirst_len :
      Zlength ((tail +:: 128) ++ repeat_Z 0 (63 - Zlength tail)) = 64).
  { assert (Hnat :
        length (repeat_Z 0 (63 - Zlength tail)) =
        Z.to_nat (63 - Zlength tail)).
    { unfold repeat_Z; apply repeat_length. }
    rewrite Zlength_app, Zlength_app_cons.
    rewrite (Zlength_correct (repeat_Z 0 (63 - Zlength tail))).
    rewrite Hnat, Z2Nat.id by lia.
    lia. }
  assert (Hzeros56_len : Zlength (repeat_Z 0 56) = 56).
  { unfold repeat_Z.
    rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
    reflexivity. }
  assert (Hfinal_len : Zlength (sm3_final_bytes message) = 128).
  { rewrite Hfinal.
    rewrite (Zlength_app
      ((tail +:: 128) ++ repeat_Z 0 (63 - Zlength tail))
      (repeat_Z 0 56 ++ u64_to_be_bytes (8 * Zlength message))).
    rewrite Hfirst_len, Zlength_app, Hzeros56_len,
      u64_to_be_bytes_length.
    lia. }
  assert (Hblock_prefix :
      (tail +:: 128) ++ repeat_Z 0 (63 - Zlength tail) =
      sublist 0 (Zlength (sm3_final_bytes message) - 64)
        (sm3_final_bytes message)).
  { rewrite Hfinal_len, Hfinal.
    replace (128 - 64) with
      (Zlength ((tail +:: 128) ++ repeat_Z 0 (63 - Zlength tail)))
      by lia.
    symmetry; apply sublist_app_exact1. }
  assert (Hmiddle :
      repeat_Z 0 56 =
      sublist (Zlength (sm3_final_bytes message) - 64)
        (Zlength (sm3_final_bytes message) - 8)
        (sm3_final_bytes message)).
  { rewrite Hfinal_len, Hfinal.
    replace (128 - 64) with 64 by lia.
    replace (128 - 8) with 120 by lia.
    rewrite (sublist_split_app_r 64 120 64
      ((tail +:: 128) ++ repeat_Z 0 (63 - Zlength tail))
      (repeat_Z 0 56 ++ u64_to_be_bytes (8 * Zlength message))
      Hfirst_len ltac:(lia)).
    replace (64 - 64) with 0 by lia.
    replace (120 - 64) with 56 by lia.
    replace
      (sublist 0 56
        (repeat_Z 0 56 ++ u64_to_be_bytes (8 * Zlength message)))
      with
      (sublist 0 (Zlength (repeat_Z 0 56))
        (repeat_Z 0 56 ++ u64_to_be_bytes (8 * Zlength message)))
      by (rewrite Hzeros56_len; reflexivity).
    symmetry; apply sublist_app_exact1. }
  repeat split; assumption.
Qed.

(** One abstract step through the flattened big-endian encoding of a word
    list.  In particular, this does not depend on the SM3 digest having eight
    words. *)
Lemma u32_be_concat_prefix_step :
  forall (words : list Z) i,
    0 <= i < Zlength words ->
    sublist 0 (4 * i) (concat (map u32_to_be_bytes words)) ++
      u32_to_be_bytes (Znth i words 0) =
    sublist 0 (4 * (i + 1)) (concat (map u32_to_be_bytes words)).
Proof.
  induction words as [|word words IH]; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    cbn [map concat].
    destruct (Z.eq_dec i 0) as [-> | Hnonzero].
    + rewrite Znth0_cons.
      replace (4 * 0) with 0 by lia.
      rewrite Zsublist_nil by lia.
      rewrite app_nil_l.
      replace (4 * (0 + 1)) with (Zlength (u32_to_be_bytes word)) by
        (rewrite u32_to_be_bytes_length; lia).
      symmetry. apply sublist_app_exact1.
    + assert (Hpositive : 0 < i) by lia.
      rewrite Znth_cons by lia.
      assert (Hprefix :
        sublist 0 (4 * i)
          (u32_to_be_bytes word ++ concat (map u32_to_be_bytes words)) =
        u32_to_be_bytes word ++
          sublist 0 (4 * (i - 1))
            (concat (map u32_to_be_bytes words))).
      { rewrite (sublist_split 0 (4 * i) 4) by
          (rewrite ?Zlength_app, ?u32_to_be_bytes_length,
             ?sm3_words_to_bytes_length; lia).
        rewrite (sublist_split_app_l 0 4) by
          (rewrite ?u32_to_be_bytes_length; lia).
        rewrite sublist_self by
          (rewrite u32_to_be_bytes_length; reflexivity).
        rewrite (sublist_split_app_r 4 (4 * i) 4) by
          (rewrite ?u32_to_be_bytes_length; lia).
        replace (4 - 4) with 0 by lia.
        replace (4 * i - 4) with (4 * (i - 1)) by lia.
        reflexivity. }
      assert (Hnext :
        sublist 0 (4 * (i + 1))
          (u32_to_be_bytes word ++ concat (map u32_to_be_bytes words)) =
        u32_to_be_bytes word ++
          sublist 0 (4 * i) (concat (map u32_to_be_bytes words))).
      { rewrite (sublist_split 0 (4 * (i + 1)) 4) by
          (rewrite ?Zlength_app, ?u32_to_be_bytes_length,
             ?sm3_words_to_bytes_length; lia).
        rewrite (sublist_split_app_l 0 4) by
          (rewrite ?u32_to_be_bytes_length; lia).
        rewrite sublist_self by
          (rewrite u32_to_be_bytes_length; reflexivity).
        rewrite (sublist_split_app_r 4 (4 * (i + 1)) 4) by
          (rewrite ?u32_to_be_bytes_length; lia).
        replace (4 - 4) with 0 by lia.
        replace (4 * (i + 1) - 4) with (4 * i) by lia.
        reflexivity. }
      rewrite Hprefix, Hnext, <- app_assoc.
      f_equal.
      replace (4 * i) with (4 * ((i - 1) + 1)) by lia.
      apply IH. lia.
Qed.

(** Case-private bridge for a prefix that has filled its whole capacity.  It
    is deliberately not registered as a strategy. *)
Lemma store_byte_prefix_complete_to_store_bytes :
  forall address capacity bytes,
    Zlength bytes = capacity ->
    store_byte_prefix address capacity bytes |--
    byte_encoding.store_bytes address capacity bytes.
Proof.
  intros address capacity bytes Hlength.
  unfold store_byte_prefix, byte_encoding.store_bytes.
  rewrite Hlength.
  replace (capacity - capacity) with 0 by lia.
  rewrite UCharArray.undef_full_empty.
  Intros_p Hprefix.
  apply split_pure_and_spatial_goals.
  - derivable1_refl_tac.
  - apply derivable1s_coq_prop_r.
    destruct Hprefix as [Hrange Hbounded].
    split; [reflexivity | exact Hbounded].
Qed.

Lemma sm3_message_length_words_be8 :
  forall message : list Z,
    Zlength message < SM3_MAX_BYTES ->
    let bit_length := 8 * Zlength message in
    let high_word := Z.shiftr (Zlength message / 64) 23 in
    let low_word := unsigned_last_nbits bit_length 32 in
      0 <= high_word < 2 ^ 32 /\
      0 <= low_word < 2 ^ 32 /\
      uint_to_be_bytes 4 high_word ++ uint_to_be_bytes 4 low_word =
        u64_to_be_bytes bit_length.
Proof.
  intros message Hmessage.
  cbn zeta.
  pose proof (Zlength_nonneg message) as Hnonnegative.
  assert (Hbit_length : 0 <= 8 * Zlength message < 2 ^ 64).
  { cbv [SM3_MAX_BYTES] in Hmessage. lia. }
  assert (Hhigh_bits :
    Z.shiftr (Zlength message / 64) 23 =
    Z.shiftr (8 * Zlength message) 32).
  {
    rewrite !Z.shiftr_div_pow2 by lia.
    change
      (Zlength message / 64 / 8388608 =
       (8 * Zlength message) / 4294967296).
    rewrite Z.div_div by lia.
    replace 4294967296 with (8 * 536870912) by reflexivity.
    rewrite Z.div_mul_cancel_l by lia.
    reflexivity.
  }
  assert (Hhigh_range :
    0 <= Z.shiftr (Zlength message / 64) 23 < 2 ^ 32).
  {
    rewrite Hhigh_bits, Z.shiftr_div_pow2 by lia.
    change (0 <= (8 * Zlength message) / 4294967296 < 4294967296).
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  }
  assert (Hlow_range :
    0 <= unsigned_last_nbits (8 * Zlength message) 32 < 2 ^ 32).
  { unfold unsigned_last_nbits. apply Z.mod_pos_bound. lia. }
  split; [exact Hhigh_range |].
  split; [exact Hlow_range |].
  unfold u64_to_be_bytes.
  apply uint_to_be_bytes_unique.
  - exact Hbit_length.
  - rewrite Zlength_app, !uint_to_be_bytes_length. reflexivity.
  - unfold u8_list_bounded.
    rewrite limb_list_bounded_app.
    split; apply uint_to_be_bytes_bounded; lia.
  - unfold be_u8_list_value.
    rewrite rev_app_distr, limb_list_value_app.
    fold
      (be_u8_list_value
        (uint_to_be_bytes 4
          (unsigned_last_nbits (8 * Zlength message) 32))).
    fold
      (be_u8_list_value
        (uint_to_be_bytes 4
          (Z.shiftr (Zlength message / 64) 23))).
    rewrite !be_u8_list_value_uint_to_be_bytes by assumption.
    replace
      (Zlength
        (rev
          (uint_to_be_bytes 4
            (unsigned_last_nbits (8 * Zlength message) 32))))
      with 4.
    2:{ rewrite Zlength_correct, length_rev.
        rewrite <- Zlength_correct, uint_to_be_bytes_length.
        reflexivity. }
    unfold limb_radix, SM2_BYTE_BASE, unsigned_last_nbits.
    rewrite Hhigh_bits, Z.shiftr_div_pow2 by lia.
    pose proof
      (Z.div_mod (8 * Zlength message) 4294967296 ltac:(lia)) as Hsplit.
    change
      ((8 * Zlength message) mod 4294967296 +
       (8 * Zlength message) / 4294967296 * 4294967296 =
       8 * Zlength message).
    lia.
Qed.
