Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import SeparationLogic.
Require Import
  SimpleC.EE.Applications_human.sm2.lib.sm3_def.

Import Snaive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

(** A message with no buffered tail consists entirely of completed blocks. *)
Lemma sm3_tail_nil_full_bytes_self :
  forall message,
    sm3_tail message = nil ->
    sm3_full_bytes message = message.
Proof.
  intros message Htail.
  pose proof (sm3_full_tail_decompose message) as Hdecomp.
  rewrite Htail, app_nil_r in Hdecomp.
  symmetry. exact Hdecomp.
Qed.

(** The empty-tail view also exposes the arithmetic block boundary needed by
    compression composition lemmas. *)
Lemma sm3_tail_nil_length_mod :
  forall message,
    sm3_tail message = nil ->
    Zlength message mod 64 = 0.
Proof.
  intros message Htail.
  rewrite <- sm3_tail_length, Htail, Zlength_nil.
  reflexivity.
Qed.

(** Filling the buffered tail with exactly one block advances every component
    of the abstract streaming state in one step. *)
Lemma sm3_complete_tail_transition :
  forall prefix suffix,
    Zlength (sm3_tail prefix ++ suffix) = 64 ->
    sm3_full_bytes (prefix ++ suffix) =
      sm3_full_bytes prefix ++ (sm3_tail prefix ++ suffix) /\
    sm3_tail (prefix ++ suffix) = nil /\
    Zlength (prefix ++ suffix) / 64 = Zlength prefix / 64 + 1 /\
    sm3_compress_bytes
      (sm3_compress_bytes SM3_IV (sm3_full_bytes prefix))
      (sm3_tail prefix ++ suffix) =
    sm3_compress_bytes SM3_IV (sm3_full_bytes (prefix ++ suffix)).
Proof.
  intros prefix suffix Hcomplete.
  assert (Hfull :
      sm3_full_bytes (prefix ++ suffix) =
      sm3_full_bytes prefix ++ (sm3_tail prefix ++ suffix)).
  { rewrite sm3_full_bytes_extend_complete_tail by exact Hcomplete.
    rewrite app_assoc. reflexivity. }
  assert (Hblocks :
      Zlength (prefix ++ suffix) / 64 = Zlength prefix / 64 + 1).
  { apply sm3_block_count_extend_complete_tail. exact Hcomplete. }
  assert (Htail : sm3_tail (prefix ++ suffix) = nil).
  { apply Zlength_nil_inv.
    rewrite sm3_tail_length, Zlength_app.
    rewrite Zlength_app, sm3_tail_length in Hcomplete.
    pose proof (Z.div_mod (Zlength prefix) 64 ltac:(lia)) as Hprefix_div.
    replace (Zlength prefix + Zlength suffix)
      with (64 * (Zlength prefix / 64 + 1)) by lia.
    rewrite Z.mul_mod by lia. reflexivity. }
  assert (Hdigest :
      sm3_compress_bytes
        (sm3_compress_bytes SM3_IV (sm3_full_bytes prefix))
        (sm3_tail prefix ++ suffix) =
      sm3_compress_bytes SM3_IV (sm3_full_bytes (prefix ++ suffix))).
  { rewrite Hfull.
    symmetry; apply sm3_compress_bytes_app.
    apply sm3_full_bytes_length_multiple. }
  repeat split; assumption.
Qed.

(** Package the two facts most callers need before appending aligned bulk
    bytes: the base is already its own full prefix and lies on a block
    boundary. *)
Lemma sm3_completed_prefix_view :
  forall message,
    sm3_tail message = nil ->
    sm3_full_bytes message = message /\
    Zlength message mod 64 = 0.
Proof.
  intros message Htail.
  split.
  - apply sm3_tail_nil_full_bytes_self. exact Htail.
  - apply sm3_tail_nil_length_mod. exact Htail.
Qed.

(** Forget the initialized prefix while preserving ownership of the complete
    byte buffer.  This is deliberately a separation lemma first; a strategy
    wrapper is justified only after stable multi-site matching is observed. *)
Lemma store_byte_prefix_forget_to_undef :
  forall address capacity bytes,
    store_byte_prefix address capacity bytes |--
    UCharArray.undef_full address capacity.
Proof.
  intros address capacity bytes.
  assert (Hspatial : 0 <= Zlength bytes <= capacity ->
      UCharArray.full address (Zlength bytes) bytes **
      UCharArray.undef_full
        (address + Zlength bytes * sizeof(UCHAR))
        (capacity - Zlength bytes) |--
      UCharArray.undef_full address capacity).
  { intros Hbound.
    sep_apply UCharArray.full_to_undef_full.
    rewrite sizeof_uchar.
    sep_apply (UCharArray.undef_full_merge_to_undef_full
      address (Zlength bytes) capacity Hbound).
    derivable1_refl_tac. }
  rewrite sizeof_uchar in Hspatial.
  replace (Zlength bytes * 1) with (Zlength bytes) in Hspatial by lia.
  unfold store_byte_prefix.
  intros memory Hsource.
  destruct Hsource as [Hproperties Hsource].
  apply (Hspatial (proj1 Hproperties)).
  exact Hsource.
Qed.

(** Normalize the byte count consumed by the bulk-compression loop.  Address
    and alignment facts deliberately remain in each caller. *)
Lemma sm3_bulk_length_unsigned :
  forall n,
    0 <= n < SM3_MAX_BYTES ->
    unsigned_last_nbits (n - n mod 64) 64 = 64 * (n / 64).
Proof.
  intros n Hrange.
  pose proof (Z.div_mod n 64 ltac:(lia)) as Hdivmod.
  assert (Hbulk : n - n mod 64 = 64 * (n / 64)) by lia.
  rewrite Hbulk.
  apply unsigned_last_nbits_eq.
  unfold SM3_MAX_BYTES in *.
  assert (Hqnonneg : 0 <= n / 64) by (apply Z.div_pos; lia).
  pose proof (Z.mod_pos_bound n 64 ltac:(lia)) as Hmodrange.
  split; lia.
Qed.

(** The quotient/remainder decomposition leaves no residual byte offset. *)
Lemma sm3_bulk_remainder_offset_zero :
  forall n,
    0 <= n ->
    n - (64 * (n / 64) + n mod 64) = 0.
Proof.
  intros n Hnonneg.
  pose proof (Z.div_mod n 64 ltac:(lia)).
  lia.
Qed.
