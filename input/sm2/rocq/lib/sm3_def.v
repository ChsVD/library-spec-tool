(** QCP-generated SM3_CTX interface and semantic memory predicates. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.Applications_human.sm2.lib Require Export
  sm3_c_bridge byte_memory sm2_c_layout.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import Snaive_C_Rules.
Local Open Scope sac.

Record Record_SM3_CTX : Type := make_record__sm3_ctx {
  _SM3_CTX_digest : list Z;
  _SM3_CTX_nblocks : Z;
  _SM3_CTX_block : list Z;
  _SM3_CTX_num : Z
}.

Definition zero_record__sm3_ctx : Record_SM3_CTX :=
  make_record__sm3_ctx
    (repeat 0 8) 0 (repeat 0 64) 0.

Definition StructPred_SM3_CTX
    (address : Z) (value : Record_SM3_CTX) : Assertion :=
  UIntArray.full
    (&(address # "_SM3_CTX" ->ₛ "digest")) 8
    value.(_SM3_CTX_digest) **
  ((&(address # "_SM3_CTX" ->ₛ "nblocks")) # UInt64
    |-> value.(_SM3_CTX_nblocks)) **
  UCharArray.full
    (&(address # "_SM3_CTX" ->ₛ "block")) 64
    value.(_SM3_CTX_block) **
  ((&(address # "_SM3_CTX" ->ₛ "num")) # UInt64
    |-> value.(_SM3_CTX_num)).

Definition UndefStructPred_SM3_CTX (address : Z) : Assertion :=
  UIntArray.undef_full
    (&(address # "_SM3_CTX" ->ₛ "digest")) 8 **
  ((&(address # "_SM3_CTX" ->ₛ "nblocks")) # UInt64 |->_) **
  UCharArray.undef_full
    (&(address # "_SM3_CTX" ->ₛ "block")) 64 **
  ((&(address # "_SM3_CTX" ->ₛ "num")) # UInt64 |->_).

Lemma store_Pred_SM3_CTX_to_undef :
  forall address value,
    StructPred_SM3_CTX address value |--
      UndefStructPred_SM3_CTX address.
Proof.
  intros address value.
  unfold StructPred_SM3_CTX, UndefStructPred_SM3_CTX.
  sep_apply UIntArray.full_to_undef_full.
  sep_apply store_uint64_undef_store_uint64.
  sep_apply UCharArray.full_to_undef_full.
  sep_apply store_uint64_undef_store_uint64.
  cancel.
Qed.

Definition store_u32_words
    (address count : Z) (words : list Z) : Assertion :=
  “ Zlength words = count /\
     limb_list_bounded SM3_WORD_MODULUS words ” &&
  UIntArray.full address count words.

Definition store_u32_words_missing_i
    (address count index : Z) (words : list Z) : Assertion :=
  “ Zlength words = count /\
     limb_list_bounded SM3_WORD_MODULUS words /\
     0 <= index < count ” &&
  UIntArray.missing_i address index 0 count words.

Definition store_byte_prefix
    (address capacity : Z) (bytes : list Z) : Assertion :=
  “ 0 <= Zlength bytes <= capacity /\
     u8_list_bounded bytes ” &&
  UCharArray.full address (Zlength bytes) bytes **
  UCharArray.undef_full
    (address + Zlength bytes) (capacity - Zlength bytes).

Definition sm3_compress_input_aligned
    (block nblocks : Z) : Prop :=
  nblocks = 0 \/ aligned_4 block.

Definition sm3_digest_input_aligned
    (data data_len : Z) : Prop :=
  data_len < 64 \/ aligned_4 data.

Definition sm3_update_data_aligned
    (data data_len buffered : Z) : Prop :=
  (buffered = 0 /\
   (data_len < 64 \/ aligned_4 data)) \/
  (0 < buffered < 64 /\
   (data_len < 128 - buffered \/
    aligned_4 (data + 64 - buffered))).

Definition sm3_full_len (message : list Z) : Z :=
  64 * (Zlength message / 64).

Definition sm3_full_bytes (message : list Z) : list Z :=
  sublist 0 (sm3_full_len message) message.

Definition sm3_tail (message : list Z) : list Z :=
  sublist (sm3_full_len message) (Zlength message) message.

Definition sm3_final_bytes (message : list Z) : list Z :=
  sm3_tail message ++ [128] ++
  repeat 0
    (Z.to_nat (sm3_padding_zero_count (Zlength message))) ++
  u64_to_be_bytes (8 * Zlength message).

Definition undef_sm3_ctx (ctx : addr) : Assertion :=
  UndefStructPred_SM3_CTX ctx.

Definition store_sm3_ctx
    (ctx : addr) (message : list Z) : Assertion :=
  “ u8_list_bounded message /\
     Zlength message < SM3_MAX_BYTES ” &&
  store_u32_words
    (&(ctx # "_SM3_CTX" ->ₛ "digest")) 8
    (sm3_compress_bytes SM3_IV (sm3_full_bytes message)) **
  ((&(ctx # "_SM3_CTX" ->ₛ "nblocks")) # UInt64
    |-> (Zlength message / 64)) **
  store_byte_prefix
    (&(ctx # "_SM3_CTX" ->ₛ "block")) 64
    (sm3_tail message) **
  ((&(ctx # "_SM3_CTX" ->ₛ "num")) # UInt64
    |-> Zlength (sm3_tail message)).

Definition sm3_ctx_full_shape (ctx : addr) : Assertion :=
  EX value, StructPred_SM3_CTX ctx value.

Definition store_sm3_ti : Assertion :=
  store_u32_words (&("Ti")) 64 SM3_TI_VALUES.

Lemma store_u32_words_length :
  forall address count words,
    store_u32_words address count words |--
      “ Zlength words = count ”.
Proof.
  intros.
  unfold store_u32_words.
  entailer!.
Qed.

Lemma store_u32_words_bounded :
  forall address count words,
    store_u32_words address count words |--
      “ limb_list_bounded SM3_WORD_MODULUS words ”.
Proof.
  intros.
  unfold store_u32_words.
  entailer!.
Qed.

Lemma store_u32_words_to_full_shape :
  forall address count words,
    store_u32_words address count words |--
      UIntArray.full_shape address count.
Proof.
  intros address count words.
  unfold store_u32_words.
  Intros.
  sep_apply UIntArray.full_to_full_shape.
  entailer!.
Qed.

Lemma store_byte_prefix_length :
  forall address capacity bytes,
    store_byte_prefix address capacity bytes |--
      “ 0 <= Zlength bytes <= capacity ”.
Proof.
  intros.
  unfold store_byte_prefix.
  entailer!.
Qed.

Lemma store_byte_prefix_bounded :
  forall address capacity bytes,
    store_byte_prefix address capacity bytes |--
      “ u8_list_bounded bytes ”.
Proof.
  intros.
  unfold store_byte_prefix.
  entailer!.
Qed.

Lemma sm3_update_data_aligned_empty :
  forall data data_len,
    data_len < 64 \/ aligned_4 data ->
    sm3_update_data_aligned data data_len 0.
Proof.
  intros data data_len Haligned.
  unfold sm3_update_data_aligned.
  left.
  auto.
Qed.

Lemma sm3_compress_input_aligned_nonempty :
  forall block nblocks,
    sm3_compress_input_aligned block nblocks ->
    nblocks <> 0 ->
    aligned_4 block.
Proof.
  intros block nblocks Haligned Hnonempty.
  unfold sm3_compress_input_aligned in Haligned.
  tauto.
Qed.

Lemma sm3_digest_input_aligned_update :
  forall data data_len,
    sm3_digest_input_aligned data data_len ->
    sm3_update_data_aligned data data_len 0.
Proof.
  intros data data_len Haligned.
  apply sm3_update_data_aligned_empty.
  exact Haligned.
Qed.

Lemma sm3_update_data_aligned_after_32 :
  forall data data_len,
    data_len < 96 \/ aligned_4 data ->
    sm3_update_data_aligned data data_len 32.
Proof.
  intros data data_len Haligned.
  unfold sm3_update_data_aligned.
  right.
  split; [lia |].
  destruct Haligned as [Hshort | Haligned].
  - left; lia.
  - right.
    replace (data + 64 - 32) with (data + 32) by lia.
    unfold aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Haligned.
    reflexivity.
Qed.

Lemma sm3_full_len_properties :
  forall message,
    0 <= sm3_full_len message <= Zlength message /\
    sm3_full_len message mod 64 = 0.
Proof.
  intros message.
  unfold sm3_full_len.
  pose proof (Zlength_nonneg message).
  assert (Hdiv : 0 <= Zlength message / 64) by
    (apply Z.div_pos; lia).
  split.
  - split; [lia |].
    apply Z.mul_div_le; lia.
  - apply (proj2 (Z.mod_divide _ 64 ltac:(lia))).
    exists (Zlength message / 64).
    ring.
Qed.

Lemma sm3_full_bytes_length :
  forall message,
    Zlength (sm3_full_bytes message) = sm3_full_len message.
Proof.
  intros message.
  unfold sm3_full_bytes.
  pose proof (sm3_full_len_properties message) as [Hfull _].
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma sm3_full_bytes_length_multiple :
  forall message,
    Zlength (sm3_full_bytes message) mod 64 = 0.
Proof.
  intros message.
  rewrite sm3_full_bytes_length.
  exact (proj2 (sm3_full_len_properties message)).
Qed.

Lemma sm3_full_bytes_bounded :
  forall message,
    u8_list_bounded message ->
    u8_list_bounded (sm3_full_bytes message).
Proof.
  intros message Hbounded.
  unfold sm3_full_bytes, u8_list_bounded in *.
  apply limb_list_bounded_sublist.
  - exact Hbounded.
  - pose proof (sm3_full_len_properties message) as [Hfull _].
    lia.
Qed.

Lemma sm3_tail_length :
  forall message,
    Zlength (sm3_tail message) =
      Zlength message mod 64.
Proof.
  intros message.
  unfold sm3_tail.
  pose proof (sm3_full_len_properties message) as [Hfull _].
  rewrite Zlength_sublist by lia.
  unfold sm3_full_len.
  pose proof (Z.div_mod (Zlength message) 64 ltac:(lia)).
  lia.
Qed.

Lemma sm3_update_data_aligned_at_init :
  forall data data_len,
    data_len < 64 \/ aligned_4 data ->
    sm3_update_data_aligned
      data data_len (Zlength (sm3_tail nil)).
Proof.
  intros data data_len Haligned.
  replace (Zlength (sm3_tail nil)) with 0.
  - apply sm3_update_data_aligned_empty.
    exact Haligned.
  - rewrite sm3_tail_length.
    reflexivity.
Qed.

Lemma sm3_update_data_aligned_after_32_byte_prefix :
  forall prefix data data_len,
    Zlength prefix = 32 ->
    data_len < 96 \/ aligned_4 data ->
    sm3_update_data_aligned
      data data_len (Zlength (sm3_tail prefix)).
Proof.
  intros prefix data data_len Hlength Haligned.
  replace (Zlength (sm3_tail prefix)) with 32.
  - apply sm3_update_data_aligned_after_32.
    exact Haligned.
  - rewrite sm3_tail_length, Hlength.
    reflexivity.
Qed.

Lemma sm3_tail_length_range :
  forall message,
    0 <= Zlength (sm3_tail message) < 64.
Proof.
  intros message.
  rewrite sm3_tail_length.
  apply Z.mod_pos_bound.
  lia.
Qed.

Lemma sm3_tail_bounded :
  forall message,
    u8_list_bounded message ->
    u8_list_bounded (sm3_tail message).
Proof.
  intros message Hbounded.
  unfold sm3_tail, u8_list_bounded in *.
  apply limb_list_bounded_sublist.
  - exact Hbounded.
  - pose proof (sm3_full_len_properties message) as [Hfull _].
    lia.
Qed.

Lemma sm3_full_tail_decompose :
  forall message,
    message = sm3_full_bytes message ++ sm3_tail message.
Proof.
  intros message.
  unfold sm3_full_bytes, sm3_tail.
  pose proof (sm3_full_len_properties message) as [Hfull _].
  rewrite <-
    (sublist_self message (Zlength message) eq_refl) at 1.
  rewrite
    (sublist_split
      0 (Zlength message) (sm3_full_len message) message) by lia.
  reflexivity.
Qed.

Lemma sm3_full_bytes_extend_complete_tail :
  forall prefix suffix,
    Zlength (sm3_tail prefix ++ suffix) = 64 ->
    sm3_full_bytes (prefix ++ suffix) =
      sm3_full_bytes prefix ++ sm3_tail prefix ++ suffix.
Proof.
  intros prefix suffix Hcomplete.
  rewrite Zlength_app in Hcomplete.
  rewrite (sm3_full_tail_decompose prefix) at 1.
  rewrite <- app_assoc.
  unfold sm3_full_bytes at 1, sm3_full_len.
  rewrite sublist_self.
  - reflexivity.
  - rewrite !Zlength_app, Hcomplete.
    pose proof (sm3_full_bytes_length_multiple prefix) as Hmultiple.
    pose proof
      (Z.div_mod
        (Zlength (sm3_full_bytes prefix)) 64 ltac:(lia)) as Hdiv.
    assert (Hexact :
      Zlength (sm3_full_bytes prefix) =
        (Zlength (sm3_full_bytes prefix) / 64) * 64) by lia.
    rewrite Hexact.
    replace
      ((Zlength (sm3_full_bytes prefix) / 64) * 64 + 64)
      with ((Zlength (sm3_full_bytes prefix) / 64 + 1) * 64)
      by ring.
    rewrite Z.div_mul by lia.
    ring.
Qed.

Lemma sm3_block_count_extend_complete_tail :
  forall prefix suffix,
    Zlength (sm3_tail prefix ++ suffix) = 64 ->
    Zlength (prefix ++ suffix) / 64 =
      Zlength prefix / 64 + 1.
Proof.
  intros prefix suffix Hcomplete.
  rewrite Zlength_app in Hcomplete |- *.
  rewrite sm3_tail_length in Hcomplete.
  pose proof (Z.div_mod (Zlength prefix) 64 ltac:(lia)) as Hdiv.
  assert (Hlength :
    Zlength prefix + Zlength suffix =
      (Zlength prefix / 64 + 1) * 64) by lia.
  rewrite Hlength, Z.div_mul by lia.
  reflexivity.
Qed.

Lemma sm3_final_bytes_length :
  forall message,
    Zlength (sm3_final_bytes message) =
      Zlength (sm3_tail message) + 9 +
      sm3_padding_zero_count (Zlength message).
Proof.
  intros message.
  unfold sm3_final_bytes.
  assert (Hrepeat :
    Zlength
      (repeat 0
        (Z.to_nat
          (sm3_padding_zero_count (Zlength message)))) =
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

Lemma sm3_final_bytes_bounded :
  forall message,
    u8_list_bounded message ->
    u8_list_bounded (sm3_final_bytes message).
Proof.
  intros message Hbounded.
  unfold sm3_final_bytes, u8_list_bounded.
  apply (proj2 (limb_list_bounded_app _ _ _)).
  split.
  - apply sm3_tail_bounded.
    exact Hbounded.
  - apply (proj2 (limb_list_bounded_app _ _ _)).
    split.
    + rewrite limb_list_bounded_cons_iff.
      split.
      * unfold SM2_BYTE_BASE.
        lia.
      * unfold limb_list_bounded.
        intros index Hindex.
        rewrite Zlength_nil in Hindex.
        lia.
    + apply (proj2 (limb_list_bounded_app _ _ _)).
      split.
      * apply (proj2
          (limb_list_bounded_iff_Forall SM2_BYTE_BASE _)).
        induction
          (Z.to_nat
            (sm3_padding_zero_count (Zlength message)))
          as [|count IH].
        -- constructor.
        -- cbn [repeat].
           constructor.
           ++ unfold SM2_BYTE_BASE.
              lia.
           ++ exact IH.
      * apply u64_to_be_bytes_bounded.
        pose proof (Zlength_nonneg message).
        lia.
Qed.

Lemma sm3_pad_decompose :
  forall message,
    sm3_pad message =
      sm3_full_bytes message ++ sm3_final_bytes message.
Proof.
  intros message.
  unfold sm3_pad, sm3_final_bytes.
  rewrite (sm3_full_tail_decompose message) at 1.
  rewrite !app_assoc.
  reflexivity.
Qed.

Lemma sm3_final_bytes_length_multiple :
  forall message,
    Zlength (sm3_final_bytes message) mod 64 = 0.
Proof.
  intros message.
  pose proof (sm3_pad_length_multiple message) as Hpad.
  pose proof (sm3_full_bytes_length_multiple message) as Hfull.
  rewrite sm3_pad_decompose, Zlength_app in Hpad.
  rewrite Z.add_mod in Hpad by lia.
  rewrite Hfull, Z.add_0_l in Hpad.
  rewrite Z.mod_small in Hpad by
    (apply Z.mod_pos_bound; lia).
  exact Hpad.
Qed.

Lemma sm3_digest_words_from_context :
  forall message,
    sm3_digest_words message =
      sm3_compress_bytes
        (sm3_compress_bytes
          SM3_IV (sm3_full_bytes message))
        (sm3_final_bytes message).
Proof.
  intros message.
  unfold sm3_digest_words.
  rewrite sm3_pad_decompose.
  apply sm3_compress_bytes_app.
  apply sm3_full_bytes_length_multiple.
Qed.

Lemma sm3_digest_bytes_from_context :
  forall message,
    sm3_digest_bytes message =
      concat
        (map u32_to_be_bytes
          (sm3_compress_bytes
            (sm3_compress_bytes
              SM3_IV (sm3_full_bytes message))
            (sm3_final_bytes message))).
Proof.
  intros message.
  unfold sm3_digest_bytes.
  rewrite sm3_digest_words_from_context.
  reflexivity.
Qed.

Lemma store_sm3_ctx_block_aligned :
  forall ctx message,
    store_sm3_ctx ctx message |--
      “ aligned_4
          (&(ctx # "_SM3_CTX" ->ₛ "block")) ”.
Proof.
  intros ctx message.
  unfold store_sm3_ctx.
  Intros.
  prop_apply
    (valid_store_uint64
      (&(ctx # "_SM3_CTX" ->ₛ "nblocks"))
      (Zlength message / 64)).
  Intros.
  pose proof (sm3_block_count_address_eq ctx) as Hlayout.
  assert (Hblock :
    &(ctx # "_SM3_CTX" ->ₛ "block") =
      &(ctx # "_SM3_CTX" ->ₛ "nblocks") + 8) by lia.
  rewrite Hblock.
  unfold isvalidptr_int64, aligned_4 in *.
  rewrite Z.add_mod by lia.
  destruct H0 as [_ [_ [_ Haligned]]].
  rewrite Haligned.
  entailer!.
Qed.

Lemma store_sm3_ctx_count_aligned :
  forall ctx message,
    store_sm3_ctx ctx message |--
      “ aligned_4
          (&(ctx # "_SM3_CTX" ->ₛ "block") + 56) ”.
Proof.
  intros ctx message.
  unfold store_sm3_ctx.
  Intros.
  prop_apply
    (valid_store_uint64
      (&(ctx # "_SM3_CTX" ->ₛ "nblocks"))
      (Zlength message / 64)).
  Intros.
  rewrite sm3_block_count_address_eq.
  unfold isvalidptr_int64, aligned_4 in *.
  rewrite Z.add_mod by lia.
  destruct H0 as [_ [_ [_ Haligned]]].
  rewrite Haligned.
  entailer!.
Qed.

Lemma store_sm3_ti_well_formed :
  store_sm3_ti |--
    “ Zlength SM3_TI_VALUES = 64 /\
       limb_list_bounded SM3_WORD_MODULUS SM3_TI_VALUES ”.
Proof.
  unfold store_sm3_ti, store_u32_words.
  entailer!.
Qed.
