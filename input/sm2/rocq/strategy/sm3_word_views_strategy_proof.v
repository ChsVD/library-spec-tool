Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_word_views_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sm3_word_views_strategy15_correctness : sm3_word_views_strategy15.
Proof.
  pre_process_default.
Qed.

Lemma sm3_word_views_strategy1_correctness : sm3_word_views_strategy1.
Proof.
  pre_process_default.
  change (0 <= word_base + index * 4 - byte_base) in H2.
  change (word_base + index * 4 - byte_base + 4 <= n) in H3.
  set (address := word_base + index * 4).
  set (offset := address - byte_base).
  assert (Haddress_aligned : aligned_4 address).
  {
    unfold address, aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Z.mul_mod by lia.
    rewrite H1.
    rewrite Z.mod_same by lia.
    rewrite Z.mul_0_r.
    reflexivity.
  }
  assert (Hchunk_length :
    Zlength (sublist offset (offset + 4) bytes) = 4).
  { rewrite Zlength_sublist by (unfold offset, address in *; lia); lia. }
  assert (Hchunk_bounded :
    u8_list_bounded (sublist offset (offset + 4) bytes)).
  {
    unfold u8_list_bounded in *.
    apply limb_list_bounded_sublist; [exact H0 |].
    unfold offset, address in *; lia.
  }
  pose proof
    (UCharArray.full_split_to_full
      byte_base offset n bytes ltac:(unfold offset, address in *; lia))
    as Hsplit_prefix.
  sep_apply Hsplit_prefix.
  pose proof
    (UCharArray.full_split_to_full
      (byte_base + offset * sizeof(UCHAR)) 4 (n - offset)
      (sublist offset n bytes)
      ltac:(unfold offset, address in *; lia)) as Hsplit_word.
  sep_apply Hsplit_word.
  rewrite !Zsublist_Zsublist in * by
    (unfold offset, address in *; lia).
  rewrite sizeof_uchar in *.
  replace (0 + offset) with offset in * by lia.
  replace (4 + offset) with (offset + 4) in * by lia.
  replace (n - offset + offset) with n in * by lia.
  replace (byte_base + offset * 1) with address in * by
    (unfold offset; lia).
  replace (byte_base + offset * 1 + 4 * 1) with (address + 4) in * by
    (unfold offset; lia).
  replace (byte_base + offset) with address in * by
    (unfold offset; lia).
  replace (n - offset - 4) with
    (n - (word_base + index * 4 - byte_base + 4)) by
    (unfold offset, address; lia).
  replace (address + 4) with
    (word_base + (index + 1) * sizeof(UINT)) by
    (unfold address; rewrite sizeof_uint; lia).
  replace (word_base + index * sizeof(UINT)) with address by
    (unfold address; rewrite sizeof_uint; lia).
  sep_apply_l_atomic
    (u8_full4_to_store_uint
      address
      (u8_list_value (sublist offset (offset + 4) bytes))
      (sublist offset (offset + 4) bytes)
      Hchunk_length Hchunk_bounded ltac:(reflexivity) Haddress_aligned).
  unfold offset, address in *.
  entailer!.
  replace (word_base + index * 4 + 4 * 1) with
    (word_base + (index + 1) * sizeof(UINT)) by
    (rewrite sizeof_uint; lia).
  cancel (UCharArray.full
    (word_base + (index + 1) * sizeof(UINT))
    (n - (word_base + index * 4 - byte_base + 4))
    (sublist (word_base + index * 4 - byte_base + 4) n bytes)).
  rewrite sizeof_uint.
  cancel.
  Intros_r value.
  apply_sepcon_adjoint.
  Intros_p Hvalue.
  subst value.
  cancel.
Qed.

Lemma sm3_word_views_strategy10_correctness : sm3_word_views_strategy10.
Proof.
  pre_process_default.
  change (word_base + index * 4 - base = Zlength prefix) in H0.
  assert (Hcell_address :
    word_base + index * 4 = base + Zlength prefix) by lia.
  unfold store_byte_prefix.
  Intros.
  destruct H2 as [[Hnonneg Hcapacity] Hbounded].
  set (address := base + Zlength prefix).
  assert (Haddress : address = base + Zlength prefix) by reflexivity.
  assert (Haddress_aligned : aligned_4 address).
  {
    unfold address.
    rewrite <- Hcell_address.
    unfold aligned_4 in *.
    rewrite Z.add_mod by lia.
    rewrite Z.mul_mod by lia.
    rewrite H1.
    rewrite Z.mod_same by lia.
    rewrite Z.mul_0_r.
    reflexivity.
  }
  sep_apply_l_atomic
    (UCharArray.undef_full_split_to_undef_full
      address 4 (capacity - Zlength prefix)
      ltac:(unfold address; lia)).
  rewrite sizeof_uchar.
  sep_apply_l_atomic
    (u8_undef_full4_to_undef_store_uint address Haddress_aligned).
  replace (word_base + index * sizeof(UINT)) with address by
    (unfold address; rewrite sizeof_uint; symmetry; exact Hcell_address).
  replace (address + 4) with
    (word_base + (index + 1) * sizeof(UINT)) by
    (unfold address; rewrite sizeof_uint; lia).
  entailer!.
  replace (address + 4 * 1) with
    (word_base + (index + 1) * sizeof(UINT)) by
    (unfold address; rewrite sizeof_uint; lia).
  replace (word_base + index * 4) with address by
    (rewrite Haddress; symmetry; exact Hcell_address).
  rewrite sizeof_uint.
  cancel (UCharArray.undef_full
    (word_base + (index + 1) * 4)
    (capacity - Zlength prefix - 4)).
  apply_sepcon_adjoint.
  entailer!.
Qed.

Lemma sm3_word_views_strategy2_correctness : sm3_word_views_strategy2.
Proof.
  pre_process_default.
  change (0 <= word_base + index * 4 - byte_base) in H2.
  change (word_base + index * 4 - byte_base + 4 <= n) in H3.
  set (address := word_base + index * 4).
  set (offset := address - byte_base).
  set (chunk := sublist offset (offset + 4) bytes).
  assert (Hchunk_length : Zlength chunk = 4).
  {
    unfold chunk.
    rewrite Zlength_sublist by (unfold offset, address in *; lia).
    lia.
  }
  assert (Hchunk_bounded : u8_list_bounded chunk).
  {
    unfold chunk, u8_list_bounded in *.
    apply limb_list_bounded_sublist; [exact H0 |].
    unfold offset, address in *; lia.
  }
  replace (word_base + index * sizeof(UINT)) with address by
    (unfold address; rewrite sizeof_uint; lia).
  sep_apply_l_atomic
    (store_uint_to_u8_full4 address (u8_list_value chunk)).
  Intros word_bytes.
  destruct H4 as
    [Hword_length [Hword_bounded [Hword_value Haligned]]].
  assert (Hword_bytes : word_bytes = chunk).
  {
    apply u8_list_value_injective.
    - lia.
    - exact Hword_bounded.
    - exact Hchunk_bounded.
    - exact Hword_value.
  }
  subst word_bytes.
  pose proof
    (UCharArray.full_merge_to_full
      byte_base offset (offset + 4)
      (sublist 0 offset bytes) chunk ltac:(lia)) as Hmerge_prefix.
  rewrite sizeof_uchar in Hmerge_prefix.
  replace (byte_base + offset * 1) with address in Hmerge_prefix by
    (unfold offset; lia).
  replace (offset + 4 - offset) with 4 in Hmerge_prefix by lia.
  sep_apply Hmerge_prefix.
  pose proof
    (UCharArray.full_merge_to_full
      byte_base (offset + 4) n
      (sublist 0 offset bytes ++ chunk)
      (sublist (offset + 4) n bytes) ltac:(lia)) as Hmerge_suffix.
  rewrite sizeof_uchar in Hmerge_suffix.
  replace (byte_base + (offset + 4) * 1) with
    (word_base + (index + 1) * sizeof(UINT)) in Hmerge_suffix by
    (unfold offset, address; rewrite sizeof_uint; lia).
  sep_apply Hmerge_suffix.
  assert (Hparts :
    List.app
      (List.app (sublist 0 offset bytes) chunk)
      (sublist (offset + 4) n bytes) = bytes).
  {
    unfold chunk.
    rewrite <- (sublist_split 0 (offset + 4) offset bytes) by lia.
    rewrite <- (sublist_split 0 n (offset + 4) bytes) by lia.
    apply sublist_self.
    symmetry; exact H.
  }
  rewrite Hparts.
  entailer!.
Qed.

Lemma sm3_word_views_strategy11_correctness : sm3_word_views_strategy11.
Proof.
  pre_process_default.
  change (word_base + index * 4 - base = Zlength prefix) in H2.
  assert (Hcell_address :
    word_base + index * 4 = base + Zlength prefix) by lia.
  set (address := word_base + index * 4).
  assert (Haddress : address = base + Zlength prefix) by
    (unfold address; exact Hcell_address).
  replace (word_base + index * sizeof(UINT)) with address by
    (unfold address; rewrite sizeof_uint; lia).
  sep_apply_l_atomic (store_uint_to_u8_full4 address value).
  Intros word_bytes.
  destruct H4 as
    [Hword_length [Hword_bounded [Hword_value Haligned]]].
  Exists word_bytes.
  pose proof
    (UCharArray.full_merge_to_full
      base (Zlength prefix) (Zlength prefix + 4)
      prefix word_bytes ltac:(lia)) as Hmerge.
  rewrite sizeof_uchar in Hmerge.
  replace (base + Zlength prefix * 1) with address in Hmerge by lia.
  replace (Zlength prefix + 4 - Zlength prefix) with 4 in Hmerge by lia.
  sep_apply Hmerge.
  unfold store_byte_prefix.
  replace (base + (Zlength prefix + 4)) with
    (word_base + (index + 1) * sizeof(UINT)) by
    (rewrite sizeof_uint; lia).
  rewrite Zlength_app, Hword_length.
  entailer!.
  - replace (capacity - (Zlength prefix + 4)) with
      (capacity - Zlength prefix - 4) by lia.
    entailer!.
    replace (base + (Zlength prefix + 4)) with
      (word_base + (index + 1) * 4) by lia.
    cancel.
    apply_sepcon_adjoint.
    entailer!.
  - unfold u8_list_bounded in *.
    rewrite limb_list_bounded_app.
    tauto.
Qed.

Lemma sm3_word_views_strategy3_correctness : sm3_word_views_strategy3.
Proof.
  pre_process_default.
  change (0 <= word_base + index * 4 - byte_base) in H2.
  change (word_base + index * 4 - byte_base + 4 <= n) in H3.
  set (address := word_base + index * 4).
  set (offset := address - byte_base).
  replace (word_base + index * sizeof(UINT)) with address by
    (unfold address; rewrite sizeof_uint; lia).
  sep_apply_l_atomic (store_uint_to_u8_full4 address value).
  Intros word_bytes.
  destruct H4 as
    [Hword_length [Hword_bounded [Hword_value Haligned]]].
  Exists word_bytes.
  pose proof
    (UCharArray.full_merge_to_full
      byte_base offset (offset + 4)
      (sublist 0 offset bytes) word_bytes ltac:(lia)) as Hmerge_prefix.
  rewrite sizeof_uchar in Hmerge_prefix.
  replace (byte_base + offset * 1) with address in Hmerge_prefix by
    (unfold offset; lia).
  replace (offset + 4 - offset) with 4 in Hmerge_prefix by lia.
  sep_apply Hmerge_prefix.
  pose proof
    (UCharArray.full_merge_to_full
      byte_base (offset + 4) n
      (sublist 0 offset bytes ++ word_bytes)
      (sublist (offset + 4) n bytes) ltac:(lia)) as Hmerge_suffix.
  rewrite sizeof_uchar in Hmerge_suffix.
  replace (byte_base + (offset + 4) * 1) with
    (word_base + (index + 1) * sizeof(UINT)) in Hmerge_suffix by
    (unfold offset, address; rewrite sizeof_uint; lia).
  sep_apply Hmerge_suffix.
  rewrite app_assoc.
  entailer!.
  - apply_sepcon_adjoint.
    entailer!.
  - unfold u8_list_bounded in *.
    apply (proj2 (limb_list_bounded_app
      SM2_BYTE_BASE
      (sublist 0 offset bytes ++ word_bytes)
      (sublist (offset + 4) n bytes))).
    split.
    + apply (proj2 (limb_list_bounded_app
        SM2_BYTE_BASE (sublist 0 offset bytes) word_bytes)).
      split.
      * apply limb_list_bounded_sublist; [exact H0 | lia].
      * exact Hword_bounded.
    + apply limb_list_bounded_sublist; [exact H0 | lia].
  - rewrite !Zlength_app, Hword_length.
    repeat rewrite Zlength_sublist by lia.
    lia.
Qed.

Lemma sm3_word_views_strategy13_correctness : sm3_word_views_strategy13.
Proof.
  pre_process_default.
  unfold store_byte_prefix.
  Intros.
  destruct H1 as [[Hnonneg Hcapacity] Hbounded].
  rewrite Zlength_nil in *.
  replace (base + 0) with base by lia.
  replace (capacity - 0) with capacity by lia.
  sep_apply_l_atomic
    (UCharArray.undef_full_split_to_undef_full
      base 4 capacity ltac:(lia)).
  rewrite sizeof_uchar.
  sep_apply_l_atomic (u8_undef_full4_to_undef_store_uint base H).
  entailer!.
  replace (base + 4 * 1) with (base + 4) by lia.
  cancel.
  apply_sepcon_adjoint.
  entailer!.
Qed.
