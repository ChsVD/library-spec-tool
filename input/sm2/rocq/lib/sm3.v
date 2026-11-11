(** Byte-aligned SM3 standard semantics over integer and byte lists. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import AUXLib.ListLib.
Require Import AUXLib.MonotonicList.
From SimpleC.SL Require Import IntLib.
From SimpleC.EE.Applications_human.sm2.lib
  Require Export byte_encoding bitwise.

Import ListNotations.
Local Open Scope Z_scope.

Definition SM3_MAX_BYTES : Z := 2 ^ 61.
Definition SM3_WORD_MODULUS : Z := 2 ^ 32.

Definition SM3_IV : list Z :=
  [0x7380166F; 0x4914B2B9; 0x172442D7; 0xDA8A0600;
   0xA96F30BC; 0x163138AA; 0xE38DEE4D; 0xB0FB0E4E].

Definition sm3_state : Type := list Z.

Definition valid_sm3_state (state : sm3_state) : Prop :=
  Zlength state = 8 /\ limb_list_bounded SM3_WORD_MODULUS state.

Definition sm3_rotl32 (value amount : Z) : Z :=
  rotate_left 32 value amount.

Definition sm3_p0 (value : Z) : Z :=
  Z.lxor
    (Z.lxor value (sm3_rotl32 value 9))
    (sm3_rotl32 value 17).

Definition sm3_p1 (value : Z) : Z :=
  Z.lxor
    (Z.lxor value (sm3_rotl32 value 15))
    (sm3_rotl32 value 23).

Definition sm3_ff (round x y z : Z) : Z :=
  if round <? 16
  then Z.lxor (Z.lxor x y) z
  else Z.lor
    (Z.lor (Z.land x y) (Z.land x z))
    (Z.land y z).

Definition sm3_gg (round x y z : Z) : Z :=
  if round <? 16
  then Z.lxor (Z.lxor x y) z
  else Z.lor (Z.land x y) (Z.land (Z.lnot x) z).

Definition sm3_t (round : Z) : Z :=
  if round <? 16 then 0x79CC4519 else 0x7A879D8A.

Definition sm3_round_constant (round : Z) : Z :=
  sm3_rotl32 (sm3_t round) round.

Definition sm3_block_word (block : list Z) (index : Z) : Z :=
  be_u8_list_value (sublist (4 * index) (4 * index + 4) block).

Definition sm3_block_words (block : list Z) : list Z :=
  map
    (fun index => sm3_block_word block (Z.of_nat index))
    (seq 0 16).

Definition sm3_expand_word (words : list Z) (index : Z) : Z :=
  Z.lxor
    (Z.lxor
      (sm3_p1
        (Z.lxor
          (Z.lxor (Znth (index - 16) words 0)
                  (Znth (index - 9) words 0))
          (sm3_rotl32 (Znth (index - 3) words 0) 15)))
      (sm3_rotl32 (Znth (index - 13) words 0) 7))
    (Znth (index - 6) words 0).

Fixpoint sm3_expand_words_aux
    (remaining : nat) (words : list Z) : list Z :=
  match remaining with
  | O => words
  | S rest =>
      let next := sm3_expand_word words (Zlength words) in
      sm3_expand_words_aux rest (words ++ [next])
  end.

Definition sm3_expand_words (block : list Z) : list Z :=
  sm3_expand_words_aux 52 (sm3_block_words block).

Definition sm3_expanded_word_prime
    (words : list Z) (round : Z) : Z :=
  Z.lxor (Znth round words 0) (Znth (round + 4) words 0).

Definition sm3_round
    (round : Z) (words state : list Z) : list Z :=
  match state with
  | [a; b; c; d; e; f; g; h] =>
      let a12 := sm3_rotl32 a 12 in
      let ss1 := sm3_rotl32
        (unsigned_last_nbits
          (a12 + e + sm3_round_constant round) 32) 7 in
      let ss2 := Z.lxor ss1 a12 in
      let tt1 := unsigned_last_nbits
        (sm3_ff round a b c + d + ss2 +
         sm3_expanded_word_prime words round) 32 in
      let tt2 := unsigned_last_nbits
        (sm3_gg round e f g + h + ss1 + Znth round words 0) 32 in
      [tt1; a; sm3_rotl32 b 9; c;
       sm3_p0 tt2; e; sm3_rotl32 f 19; g]
  | _ => state
  end.

Fixpoint sm3_rounds_aux
    (remaining : nat) (round : Z)
    (words state : list Z) : list Z :=
  match remaining with
  | O => state
  | S rest =>
      sm3_rounds_aux rest (round + 1) words
        (sm3_round round words state)
  end.

Definition sm3_rounds (words state : list Z) : list Z :=
  sm3_rounds_aux 64 0 words state.

Fixpoint sm3_state_xor (left right : list Z) : list Z :=
  match left, right with
  | x :: xs, y :: ys => Z.lxor x y :: sm3_state_xor xs ys
  | _, _ => nil
  end.

Definition sm3_compress_block
    (state : sm3_state) (block : list Z) : sm3_state :=
  let words := sm3_expand_words block in
  sm3_state_xor state (sm3_rounds words state).

Fixpoint sm3_compress_blocks_aux
    (remaining : nat) (state : sm3_state)
    (blocks : list Z) : sm3_state :=
  match remaining with
  | O => state
  | S rest =>
      sm3_compress_blocks_aux rest
        (sm3_compress_block state (firstn 64 blocks))
        (skipn 64 blocks)
  end.

Definition sm3_compress_bytes
    (state : sm3_state) (blocks : list Z) : sm3_state :=
  sm3_compress_blocks_aux
    (Z.to_nat (Zlength blocks / 64)) state blocks.

Definition u64_to_be_bytes (value : Z) : list Z :=
  uint_to_be_bytes 8 value.

Definition sm3_padding_zero_count (message_length : Z) : Z :=
  (55 - message_length) mod 64.

Definition sm3_pad (message : list Z) : list Z :=
  message ++ [128] ++
  repeat 0 (Z.to_nat (sm3_padding_zero_count (Zlength message))) ++
  u64_to_be_bytes (8 * Zlength message).

Definition sm3_digest_words (message : list Z) : sm3_state :=
  sm3_compress_bytes SM3_IV (sm3_pad message).

Definition u32_to_be_bytes (word : Z) : list Z :=
  uint_to_be_bytes 4 word.

Definition sm3_digest_bytes (message : list Z) : list Z :=
  concat (map u32_to_be_bytes (sm3_digest_words message)).

Lemma limb_list_bounded_iff_Forall :
  forall base values,
    limb_list_bounded base values <->
    Forall (fun value => 0 <= value < base) values.
Proof.
  intros base values.
  unfold limb_list_bounded.
  symmetry.
  exact
    (Forall_Znth (fun value : Z => 0 <= value < base) 0 values).
Qed.

Lemma SM3_IV_valid : valid_sm3_state SM3_IV.
Proof.
  unfold valid_sm3_state.
  split; [reflexivity |].
  apply (proj2
    (limb_list_bounded_iff_Forall SM3_WORD_MODULUS SM3_IV)).
  unfold SM3_IV.
  repeat constructor; cbv [SM3_WORD_MODULUS]; lia.
Qed.

Lemma sm3_rotl32_range :
  forall value amount,
    0 <= value < SM3_WORD_MODULUS ->
    0 <= sm3_rotl32 value amount < SM3_WORD_MODULUS.
Proof.
  intros value amount Hvalue.
  unfold sm3_rotl32.
  change (0 <= rotate_left 32 value amount < 2 ^ 32).
  apply rotate_left_range_pow2; try lia.
  unfold SM3_WORD_MODULUS in Hvalue.
  exact Hvalue.
Qed.

Lemma sm3_p0_range :
  forall value,
    0 <= value < SM3_WORD_MODULUS ->
    0 <= sm3_p0 value < SM3_WORD_MODULUS.
Proof.
  intros value Hvalue.
  unfold sm3_p0, SM3_WORD_MODULUS in *.
  apply lxor_range_pow2; try lia.
  - apply lxor_range_pow2; try lia.
    apply rotate_left_range_pow2; lia.
  - apply rotate_left_range_pow2; lia.
Qed.

Lemma sm3_p1_range :
  forall value,
    0 <= value < SM3_WORD_MODULUS ->
    0 <= sm3_p1 value < SM3_WORD_MODULUS.
Proof.
  intros value Hvalue.
  unfold sm3_p1, SM3_WORD_MODULUS in *.
  apply lxor_range_pow2; try lia.
  - apply lxor_range_pow2; try lia.
    apply rotate_left_range_pow2; lia.
  - apply rotate_left_range_pow2; lia.
Qed.

Lemma sm3_ff_range :
  forall round x y z,
    0 <= x < SM3_WORD_MODULUS ->
    0 <= y < SM3_WORD_MODULUS ->
    0 <= z < SM3_WORD_MODULUS ->
    0 <= sm3_ff round x y z < SM3_WORD_MODULUS.
Proof.
  intros round x y z Hx Hy Hz.
  unfold sm3_ff, SM3_WORD_MODULUS in *.
  destruct (round <? 16) eqn:Hround.
  - apply lxor_range_pow2; try lia.
    apply lxor_range_pow2; lia.
  - apply lor_range_pow2; try lia.
    + apply lor_range_pow2; try lia;
        apply land_range_pow2; lia.
    + apply land_range_pow2; lia.
Qed.

Lemma sm3_gg_range :
  forall round x y z,
    0 <= x < SM3_WORD_MODULUS ->
    0 <= y < SM3_WORD_MODULUS ->
    0 <= z < SM3_WORD_MODULUS ->
    0 <= sm3_gg round x y z < SM3_WORD_MODULUS.
Proof.
  intros round x y z Hx Hy Hz.
  unfold sm3_gg, SM3_WORD_MODULUS in *.
  destruct (round <? 16) eqn:Hround.
  - apply lxor_range_pow2; try lia.
    apply lxor_range_pow2; lia.
  - apply lor_range_pow2; try lia.
    + apply land_range_pow2; lia.
    + apply land_lnot_range_pow2; lia.
Qed.

Lemma sm3_t_range :
  forall round,
    0 <= sm3_t round < SM3_WORD_MODULUS.
Proof.
  intros round.
  unfold sm3_t.
  destruct (round <? 16); cbv [SM3_WORD_MODULUS]; lia.
Qed.

Lemma sm3_round_constant_standard :
  forall round,
    sm3_round_constant round =
      sm3_rotl32
        (if round <? 16 then 0x79CC4519 else 0x7A879D8A)
        round.
Proof.
  intros round.
  reflexivity.
Qed.

Lemma sm3_round_constant_range :
  forall round,
    0 <= sm3_round_constant round < SM3_WORD_MODULUS.
Proof.
  intros round.
  unfold sm3_round_constant.
  apply sm3_rotl32_range.
  apply sm3_t_range.
Qed.

Lemma sm3_block_words_length :
  forall block,
    Zlength (sm3_block_words block) = 16.
Proof.
  intros block.
  unfold sm3_block_words.
  rewrite !Zlength_correct, length_map, length_seq.
  reflexivity.
Qed.

Lemma sm3_block_words_Znth :
  forall block index,
    0 <= index < 16 ->
    Znth index (sm3_block_words block) 0 =
      sm3_block_word block index.
Proof.
  intros block index Hindex.
  unfold sm3_block_words, Znth.
  transitivity
    (nth (Z.to_nat index)
      (map
        (fun index0 : nat => sm3_block_word block (Z.of_nat index0))
        (seq 0 16))
      (sm3_block_word block (Z.of_nat O))).
  - apply (@nth_indep Z).
    rewrite length_map, length_seq.
    lia.
  - rewrite <- (Z2Nat.id index) at 2 by lia.
    change
      (nth (Z.to_nat index)
        (map
          (fun index0 : nat => sm3_block_word block (Z.of_nat index0))
          (seq 0 16))
        ((fun index0 : nat =>
          sm3_block_word block (Z.of_nat index0)) O) =
       (fun index0 : nat =>
          sm3_block_word block (Z.of_nat index0)) (Z.to_nat index)).
    transitivity
      ((fun index0 : nat =>
          sm3_block_word block (Z.of_nat index0))
        (nth (Z.to_nat index) (seq 0 16) O)).
    + exact (@map_nth nat Z
        (fun index0 : nat =>
          sm3_block_word block (Z.of_nat index0))
        (seq 0 16) O (Z.to_nat index)).
    + f_equal.
      rewrite seq_nth by lia.
      lia.
Qed.

Lemma sm3_expanded_word_prime_standard :
  forall words round,
    sm3_expanded_word_prime words round =
      Z.lxor (Znth round words 0) (Znth (round + 4) words 0).
Proof.
  intros words round.
  reflexivity.
Qed.

Lemma sm3_expand_words_aux_length :
  forall remaining words,
    Zlength (sm3_expand_words_aux remaining words) =
      Zlength words + Z.of_nat remaining.
Proof.
  intros remaining.
  induction remaining as [|remaining IH]; intros words.
  - simpl. lia.
  - cbn [sm3_expand_words_aux].
    rewrite IH, Zlength_app, Zlength_cons, Zlength_nil,
      Nat2Z.inj_succ.
    lia.
Qed.

Lemma sm3_expand_words_aux_prefix :
  forall remaining words index,
    0 <= index < Zlength words ->
    Znth index (sm3_expand_words_aux remaining words) 0 =
      Znth index words 0.
Proof.
  intros remaining.
  induction remaining as [|remaining IH];
    intros words index Hindex.
  - reflexivity.
  - cbn [sm3_expand_words_aux].
    transitivity
      (Znth index
        (words ++ [sm3_expand_word words (Zlength words)]) 0).
    + apply IH.
      rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    + apply app_Znth1.
      exact Hindex.
Qed.

Lemma sm3_expand_word_app_prefix :
  forall words suffix index,
    16 <= index <= Zlength words ->
    sm3_expand_word (words ++ suffix) index =
      sm3_expand_word words index.
Proof.
  intros words suffix index Hindex.
  unfold sm3_expand_word.
  repeat rewrite app_Znth1 by lia.
  reflexivity.
Qed.

Lemma sm3_expand_word_aux_prefix :
  forall remaining words index,
    16 <= index <= Zlength words ->
    sm3_expand_word (sm3_expand_words_aux remaining words) index =
      sm3_expand_word words index.
Proof.
  intros remaining words index Hindex.
  unfold sm3_expand_word.
  repeat rewrite sm3_expand_words_aux_prefix by lia.
  reflexivity.
Qed.

Lemma sm3_expand_words_aux_recurrence :
  forall remaining words index,
    16 <= Zlength words ->
    Zlength words <= index <
      Zlength words + Z.of_nat remaining ->
    Znth index (sm3_expand_words_aux remaining words) 0 =
      sm3_expand_word
        (sm3_expand_words_aux remaining words) index.
Proof.
  intros remaining.
  induction remaining as [|remaining IH];
    intros words index Hwords Hindex.
  - cbn [sm3_expand_words_aux] in *.
    lia.
  - cbn [sm3_expand_words_aux].
    set (next := sm3_expand_word words (Zlength words)).
    set (extended := words ++ [next]).
    change
      (Znth index (sm3_expand_words_aux remaining extended) 0 =
       sm3_expand_word
         (sm3_expand_words_aux remaining extended) index).
    assert (Hextended : Zlength extended = Zlength words + 1).
    {
      unfold extended.
      rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    }
    destruct (Z.eq_dec index (Zlength words)) as [Heq | Hneq].
    + subst index.
      rewrite sm3_expand_words_aux_prefix by
        (rewrite Hextended; lia).
      assert (Hnext :
        Znth (Zlength words) extended 0 = next).
      {
        unfold extended.
        rewrite app_Znth2 by lia.
        replace (Zlength words - Zlength words) with 0 by lia.
        reflexivity.
      }
      rewrite Hnext.
      rewrite sm3_expand_word_aux_prefix by
        (rewrite Hextended; lia).
      unfold extended.
      rewrite sm3_expand_word_app_prefix by lia.
      unfold next.
      reflexivity.
    + apply IH.
      * rewrite Hextended.
        lia.
      * rewrite Hextended.
        rewrite Nat2Z.inj_succ in Hindex.
        lia.
Qed.

Lemma sm3_expand_words_length :
  forall block,
    Zlength (sm3_expand_words block) = 68.
Proof.
  intros block.
  unfold sm3_expand_words.
  rewrite sm3_expand_words_aux_length, sm3_block_words_length.
  reflexivity.
Qed.

Lemma sm3_expand_words_initial :
  forall block index,
    0 <= index < 16 ->
    Znth index (sm3_expand_words block) 0 =
      sm3_block_word block index.
Proof.
  intros block index Hindex.
  unfold sm3_expand_words.
  rewrite sm3_expand_words_aux_prefix.
  - apply sm3_block_words_Znth.
    exact Hindex.
  - rewrite sm3_block_words_length.
    exact Hindex.
Qed.

Lemma sm3_expand_words_recurrence :
  forall block index,
    16 <= index < 68 ->
    Znth index (sm3_expand_words block) 0 =
      sm3_expand_word (sm3_expand_words block) index.
Proof.
  intros block index Hindex.
  unfold sm3_expand_words.
  apply sm3_expand_words_aux_recurrence.
  - rewrite sm3_block_words_length.
    lia.
  - rewrite sm3_block_words_length.
    exact Hindex.
Qed.

Lemma sm3_round_length :
  forall round words state,
    Zlength (sm3_round round words state) = Zlength state.
Proof.
  intros round words state.
  destruct state as [|a state]; [reflexivity |].
  destruct state as [|b state]; [reflexivity |].
  destruct state as [|c state]; [reflexivity |].
  destruct state as [|d state]; [reflexivity |].
  destruct state as [|e state]; [reflexivity |].
  destruct state as [|f state]; [reflexivity |].
  destruct state as [|g state]; [reflexivity |].
  destruct state as [|h state]; [reflexivity |].
  destruct state; reflexivity.
Qed.

Lemma sm3_round_bounded :
  forall round words state,
    limb_list_bounded SM3_WORD_MODULUS state ->
    limb_list_bounded SM3_WORD_MODULUS
      (sm3_round round words state).
Proof.
  intros round words state Hbounded.
  destruct state as [|a state]; [exact Hbounded |].
  destruct state as [|b state]; [exact Hbounded |].
  destruct state as [|c state]; [exact Hbounded |].
  destruct state as [|d state]; [exact Hbounded |].
  destruct state as [|e state]; [exact Hbounded |].
  destruct state as [|f state]; [exact Hbounded |].
  destruct state as [|g state]; [exact Hbounded |].
  destruct state as [|h state]; [exact Hbounded |].
  destruct state as [|extra state]; [|exact Hbounded].
  repeat rewrite limb_list_bounded_cons_iff in Hbounded.
  destruct Hbounded as
    [Ha [Hb [Hc [Hd [He [Hf [Hg [Hh _]]]]]]]].
  cbn [sm3_round].
  apply (proj2 (limb_list_bounded_iff_Forall _ _)).
  constructor.
  - unfold SM3_WORD_MODULUS.
    apply unsigned_Lastnbits_range. lia.
  - constructor; [exact Ha |].
    constructor; [apply sm3_rotl32_range; exact Hb |].
    constructor; [exact Hc |].
    constructor.
    + apply sm3_p0_range.
      unfold SM3_WORD_MODULUS.
      apply unsigned_Lastnbits_range. lia.
    + constructor; [exact He |].
      constructor; [apply sm3_rotl32_range; exact Hf |].
      constructor; [exact Hg | constructor].
Qed.

Lemma sm3_rounds_aux_length :
  forall remaining round words state,
    Zlength (sm3_rounds_aux remaining round words state) =
      Zlength state.
Proof.
  intros remaining.
  induction remaining as [|remaining IH]; intros round words state.
  - reflexivity.
  - cbn [sm3_rounds_aux].
    rewrite IH, sm3_round_length.
    reflexivity.
Qed.

Lemma sm3_rounds_aux_bounded :
  forall remaining round words state,
    limb_list_bounded SM3_WORD_MODULUS state ->
    limb_list_bounded SM3_WORD_MODULUS
      (sm3_rounds_aux remaining round words state).
Proof.
  intros remaining.
  induction remaining as [|remaining IH];
    intros round words state Hbounded.
  - exact Hbounded.
  - cbn [sm3_rounds_aux].
    apply IH.
    apply sm3_round_bounded.
    exact Hbounded.
Qed.

Lemma sm3_rounds_length :
  forall words state,
    Zlength (sm3_rounds words state) = Zlength state.
Proof.
  intros words state.
  apply sm3_rounds_aux_length.
Qed.

Lemma sm3_rounds_bounded :
  forall words state,
    limb_list_bounded SM3_WORD_MODULUS state ->
    limb_list_bounded SM3_WORD_MODULUS (sm3_rounds words state).
Proof.
  intros words state Hbounded.
  apply sm3_rounds_aux_bounded.
  exact Hbounded.
Qed.

Lemma sm3_state_xor_length :
  forall left right,
    Zlength left = Zlength right ->
    Zlength (sm3_state_xor left right) = Zlength left.
Proof.
  intros left.
  induction left as [|x xs IH]; intros right Hlength.
  - destruct right; reflexivity.
  - destruct right as [|y ys].
    + pose proof (Zlength_nonneg xs).
      rewrite Zlength_cons, Zlength_nil in Hlength. lia.
    + cbn [sm3_state_xor].
      rewrite !Zlength_cons, IH; [reflexivity |].
      rewrite !Zlength_cons in Hlength.
      lia.
Qed.

Lemma sm3_state_xor_bounded :
  forall left right,
    limb_list_bounded SM3_WORD_MODULUS left ->
    limb_list_bounded SM3_WORD_MODULUS right ->
    limb_list_bounded SM3_WORD_MODULUS
      (sm3_state_xor left right).
Proof.
  intros left right Hleft Hright.
  apply (proj1
    (limb_list_bounded_iff_Forall SM3_WORD_MODULUS left)) in Hleft.
  apply (proj1
    (limb_list_bounded_iff_Forall SM3_WORD_MODULUS right)) in Hright.
  apply (proj2
    (limb_list_bounded_iff_Forall
      SM3_WORD_MODULUS (sm3_state_xor left right))).
  revert right Hright.
  induction Hleft as [|x xs Hx Hxs IH];
    intros right Hright; destruct right as [|y ys]; simpl.
  - constructor.
  - constructor.
  - constructor.
  - inversion Hright as [|? ? Hy Hys]; subst.
    constructor.
    + unfold SM3_WORD_MODULUS in *.
      apply lxor_range_pow2; lia.
    + apply IH. exact Hys.
Qed.

Lemma sm3_compress_block_valid :
  forall state block,
    valid_sm3_state state ->
    valid_sm3_state (sm3_compress_block state block).
Proof.
  intros state block [Hlength Hbounded].
  unfold valid_sm3_state, sm3_compress_block.
  split.
  - rewrite <- Hlength.
    apply sm3_state_xor_length.
    rewrite sm3_rounds_length.
    reflexivity.
  - apply sm3_state_xor_bounded.
    + exact Hbounded.
    + apply sm3_rounds_bounded. exact Hbounded.
Qed.

Lemma sm3_compress_blocks_aux_app :
  forall left_count right_count state left right,
    length left = (64 * left_count)%nat ->
    sm3_compress_blocks_aux
      (left_count + right_count) state (left ++ right) =
    sm3_compress_blocks_aux right_count
      (sm3_compress_blocks_aux left_count state left) right.
Proof.
  intros left_count.
  induction left_count as [|left_count IH];
    intros right_count state left right Hlength.
  - cbn in Hlength.
    apply length_zero_iff_nil in Hlength.
    subst left.
    reflexivity.
  - replace (S left_count + right_count)%nat with
      (S (left_count + right_count)) by lia.
    cbn [sm3_compress_blocks_aux].
    rewrite firstn_app, skipn_app.
    assert (Hblock : (64 <= length left)%nat) by lia.
    replace (64 - length left)%nat with 0%nat by lia.
    rewrite firstn_O, skipn_O, app_nil_r.
    apply IH.
    rewrite length_skipn.
    lia.
Qed.

Lemma sm3_compress_bytes_app :
  forall state left right,
    Zlength left mod 64 = 0 ->
    sm3_compress_bytes state (left ++ right) =
      sm3_compress_bytes
        (sm3_compress_bytes state left) right.
Proof.
  intros state left right Haligned.
  pose proof (Zlength_nonneg left) as Hleft_nonneg.
  pose proof (Zlength_nonneg right) as Hright_nonneg.
  assert (Hleft_div : 0 <= Zlength left / 64) by
    (apply Z.div_pos; lia).
  assert (Hright_div : 0 <= Zlength right / 64) by
    (apply Z.div_pos; lia).
  assert (Hleft_exact :
    Zlength left = (Zlength left / 64) * 64).
  {
    pose proof (Z.div_mod (Zlength left) 64 ltac:(lia)).
    lia.
  }
  assert (Hquotient :
    (Zlength (left ++ right) / 64) =
      Zlength left / 64 + Zlength right / 64).
  {
    rewrite Zlength_app, Hleft_exact.
    rewrite Z.div_add_l by lia.
    rewrite Z.div_mul by lia.
    reflexivity.
  }
  assert (Hleft_length :
    length left =
      (64 * Z.to_nat (Zlength left / 64))%nat).
  {
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_mul, Z2Nat.id by exact Hleft_div.
    rewrite <- Zlength_correct.
    lia.
  }
  unfold sm3_compress_bytes.
  rewrite Hquotient, Z2Nat.inj_add by assumption.
  apply sm3_compress_blocks_aux_app.
  exact Hleft_length.
Qed.

Lemma sm3_compress_bytes_one_block :
  forall state block,
    Zlength block = 64 ->
    sm3_compress_bytes state block =
      sm3_compress_block state block.
Proof.
  intros state block Hlength.
  unfold sm3_compress_bytes.
  rewrite Hlength.
  change
    (sm3_compress_blocks_aux 1 state block =
     sm3_compress_block state block).
  cbn [sm3_compress_blocks_aux].
  rewrite firstn_all2.
  - reflexivity.
  - rewrite Zlength_correct in Hlength.
    lia.
Qed.

Lemma sm3_compress_blocks_aux_valid :
  forall remaining state blocks,
    valid_sm3_state state ->
    valid_sm3_state
      (sm3_compress_blocks_aux remaining state blocks).
Proof.
  intros remaining.
  induction remaining as [|remaining IH];
    intros state blocks Hvalid.
  - exact Hvalid.
  - cbn [sm3_compress_blocks_aux].
    apply IH.
    apply sm3_compress_block_valid.
    exact Hvalid.
Qed.

Lemma sm3_compress_bytes_valid :
  forall state blocks,
    valid_sm3_state state ->
    valid_sm3_state (sm3_compress_bytes state blocks).
Proof.
  intros state blocks Hvalid.
  unfold sm3_compress_bytes.
  apply sm3_compress_blocks_aux_valid.
  exact Hvalid.
Qed.

Lemma sm3_digest_words_valid :
  forall message,
    valid_sm3_state (sm3_digest_words message).
Proof.
  intros message.
  unfold sm3_digest_words.
  apply sm3_compress_bytes_valid.
  exact SM3_IV_valid.
Qed.

Lemma u64_to_be_bytes_length :
  forall value,
    Zlength (u64_to_be_bytes value) = 8.
Proof.
  intros value.
  unfold u64_to_be_bytes.
  apply uint_to_be_bytes_length.
Qed.

Lemma u64_to_be_bytes_bounded :
  forall value,
    0 <= value ->
    u8_list_bounded (u64_to_be_bytes value).
Proof.
  intros value Hvalue.
  unfold u64_to_be_bytes.
  apply uint_to_be_bytes_bounded.
  exact Hvalue.
Qed.

Lemma be_u8_list_value_u64_to_be_bytes :
  forall value,
    0 <= value < 2 ^ 64 ->
    be_u8_list_value (u64_to_be_bytes value) = value.
Proof.
  intros value Hvalue.
  unfold u64_to_be_bytes.
  apply be_u8_list_value_uint_to_be_bytes.
  change (0 <= value < 2 ^ 64).
  exact Hvalue.
Qed.

Lemma u32_to_be_bytes_length :
  forall value,
    Zlength (u32_to_be_bytes value) = 4.
Proof.
  intros value.
  unfold u32_to_be_bytes.
  apply uint_to_be_bytes_length.
Qed.

Lemma u32_to_be_bytes_bounded :
  forall value,
    0 <= value ->
    u8_list_bounded (u32_to_be_bytes value).
Proof.
  intros value Hvalue.
  unfold u32_to_be_bytes.
  apply uint_to_be_bytes_bounded.
  exact Hvalue.
Qed.

Lemma be_u8_list_value_u32_to_be_bytes :
  forall value,
    0 <= value < 2 ^ 32 ->
    be_u8_list_value (u32_to_be_bytes value) = value.
Proof.
  intros value Hvalue.
  unfold u32_to_be_bytes.
  apply be_u8_list_value_uint_to_be_bytes.
  change (0 <= value < 2 ^ 32).
  exact Hvalue.
Qed.

Lemma sm3_words_to_bytes_length :
  forall words,
    Zlength (concat (map u32_to_be_bytes words)) =
      4 * Zlength words.
Proof.
  intros words.
  induction words as [|word words IH].
  - reflexivity.
  - cbn [map concat].
    rewrite Zlength_app, u32_to_be_bytes_length,
      IH, Zlength_cons.
    lia.
Qed.

Lemma sm3_words_to_bytes_bounded :
  forall words,
    limb_list_bounded SM3_WORD_MODULUS words ->
    u8_list_bounded (concat (map u32_to_be_bytes words)).
Proof.
  intros words.
  induction words as [|word words IH]; intros Hbounded.
  - unfold u8_list_bounded, limb_list_bounded.
    intros index Hindex.
    rewrite Zlength_nil in Hindex. lia.
  - apply (proj1
      (limb_list_bounded_cons_iff
        SM3_WORD_MODULUS word words)) in Hbounded.
    destruct Hbounded as [Hword Hwords].
    cbn [map concat].
    unfold u8_list_bounded in *.
    apply (proj2 (limb_list_bounded_app _ _ _)).
    split.
    + apply u32_to_be_bytes_bounded. lia.
    + apply IH. exact Hwords.
Qed.

Lemma sm3_digest_bytes_length :
  forall message,
    Zlength (sm3_digest_bytes message) = 32.
Proof.
  intros message.
  unfold sm3_digest_bytes.
  rewrite sm3_words_to_bytes_length.
  pose proof (sm3_digest_words_valid message) as [Hlength _].
  lia.
Qed.

Lemma sm3_digest_bytes_bounded :
  forall message,
    u8_list_bounded (sm3_digest_bytes message).
Proof.
  intros message.
  unfold sm3_digest_bytes.
  apply sm3_words_to_bytes_bounded.
  exact (proj2 (sm3_digest_words_valid message)).
Qed.

Lemma sm3_digest_bytes_properties :
  forall message,
    Zlength (sm3_digest_bytes message) = 32 /\
    u8_list_bounded (sm3_digest_bytes message).
Proof.
  intros message.
  split.
  - apply sm3_digest_bytes_length.
  - apply sm3_digest_bytes_bounded.
Qed.

Lemma sm3_padding_zero_count_range :
  forall message_length,
    0 <= sm3_padding_zero_count message_length < 64.
Proof.
  intros message_length.
  unfold sm3_padding_zero_count.
  apply Z.mod_pos_bound.
  lia.
Qed.

Lemma sm3_pad_length :
  forall message,
    Zlength (sm3_pad message) =
      Zlength message + 9 +
      sm3_padding_zero_count (Zlength message).
Proof.
  intros message.
  unfold sm3_pad.
  assert (Hrepeat :
    Zlength
      (repeat 0
        (Z.to_nat (sm3_padding_zero_count (Zlength message)))) =
    sm3_padding_zero_count (Zlength message)).
  {
    rewrite Zlength_correct, repeat_length, Z2Nat.id.
    - reflexivity.
    - apply sm3_padding_zero_count_range.
  }
  rewrite !Zlength_app, !Zlength_cons, Zlength_nil,
    u64_to_be_bytes_length, Hrepeat.
  lia.
Qed.

Lemma sm3_pad_bit_length :
  forall (message : list Z),
    Zlength message < SM3_MAX_BYTES ->
    be_u8_list_value
      (u64_to_be_bytes (8 * Zlength message)) =
      8 * Zlength message.
Proof.
  intros message Hlength.
  apply be_u8_list_value_u64_to_be_bytes.
  pose proof (Zlength_nonneg message).
  cbv [SM3_MAX_BYTES].
  cbv [SM3_MAX_BYTES] in Hlength.
  lia.
Qed.

Lemma sm3_pad_length_multiple :
  forall message,
    Zlength (sm3_pad message) mod 64 = 0.
Proof.
  intros message.
  rewrite sm3_pad_length.
  unfold sm3_padding_zero_count.
  apply (proj2 (Z.mod_divide _ 64 ltac:(lia))).
  exists (1 - (55 - Zlength message) / 64).
  pose proof
    (Z.div_mod (55 - Zlength message) 64 ltac:(lia)).
  lia.
Qed.
