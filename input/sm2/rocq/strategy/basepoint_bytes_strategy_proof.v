Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import basepoint_bytes_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_ecc_const_table.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_basepoint_mul.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma basepoint_bytes_strategy10_correctness : basepoint_bytes_strategy10.
  pre_process_default.
  pose proof
    (UCharArray.full_split_to_full p (8 * i) 32 bytes ltac:(lia))
    as Hsplit.
  sep_apply Hsplit.
  pose proof
    (UCharArray.full_split_to_full
      (p + 8 * i * sizeof(UCHAR)) 8 (32 - 8 * i)
      (sublist (8 * i) 32 bytes) ltac:(lia)) as Hsplit_tail.
  sep_apply Hsplit_tail.
  rewrite !Zsublist_Zsublist by lia.
  rewrite sizeof_uchar.
  replace (0 + 8 * i) with (8 * i) by lia.
  replace (8 + 8 * i) with (8 * i + 8) by lia.
  replace (32 - 8 * i + 8 * i) with 32 by lia.
  entailer!.
  replace (8 * i * 1) with (8 * i) by ring.
  replace (p + 8 * i + 8 * 1) with (p + 8 * i + 8) by lia.
  replace (32 - 8 * i - 8) with (32 - (8 * i + 8)) by lia.
  cancel.
  Unshelve.
  rewrite sizeof_uint64.
  replace (p + i * 8) with (p + 8 * i) by ring.
  replace (p + (i + 1) * 8) with (p + 8 * i + 8) by ring.
  cancel.
Qed.

Lemma basepoint_bytes_strategy11_correctness : basepoint_bytes_strategy11.
  pre_process_default.
  rewrite !sizeof_uint64.
  pose proof (UCharArray.full_merge_to_full
    p (8 * i) (8 * i + 8)
    (sublist 0 (8 * i) bytes)
    (sublist (8 * i) (8 * i + 8) bytes) ltac:(lia)) as Hmerge1.
  replace (8 * i + 8 - 8 * i) with 8 in Hmerge1 by lia.
  rewrite sizeof_uchar in Hmerge1.
  replace (p + i * 8) with (p + 8 * i * 1) by ring.
  sep_apply Hmerge1.
  pose proof (UCharArray.full_merge_to_full
    p (8 * i + 8) 32
    (sublist 0 (8 * i) bytes ++
     sublist (8 * i) (8 * i + 8) bytes)
    (sublist (8 * i + 8) 32 bytes) ltac:(lia)) as Hmerge2.
  rewrite sizeof_uchar in Hmerge2.
  replace (p + (i + 1) * 8) with (p + (8 * i + 8) * 1) by ring.
  sep_apply Hmerge2.
  assert (Hparts :
    List.app
      (List.app (sublist 0 (8 * i) bytes)
        (sublist (8 * i) (8 * i + 8) bytes))
      (sublist (8 * i + 8) 32 bytes) = bytes).
  {
    rewrite <- (sublist_split 0 (8 * i + 8) (8 * i) bytes) by lia.
    rewrite <- (sublist_split 0 32 (8 * i + 8) bytes) by lia.
    apply sublist_self; symmetry; assumption.
  }
  rewrite Hparts; entailer!.
Qed.

Lemma basepoint_bytes_strategy20_correctness : basepoint_bytes_strategy20.
  pre_process_default.
  pose proof (UCharArray.full_split_to_full p 8 32 bytes ltac:(lia))
    as Hsplit0.
  sep_apply Hsplit0.
  pose proof (UCharArray.full_split_to_full
    (p + 8 * sizeof(UCHAR)) 8 24 (sublist 8 32 bytes) ltac:(lia))
    as Hsplit1.
  sep_apply Hsplit1.
  pose proof (UCharArray.full_split_to_full
    (p + 8 * sizeof(UCHAR) + 8 * sizeof(UCHAR)) 8 16
    (sublist 8 24 (sublist 8 32 bytes)) ltac:(lia)) as Hsplit2.
  sep_apply Hsplit2.
  rewrite !Zsublist_Zsublist by lia.
  rewrite sizeof_uchar.
  entailer!.
  replace (0 + 8) with 8 by lia.
  replace (8 + 8) with 16 by lia.
  replace (0 + 8 + 8) with 16 by lia.
  replace (8 + 8 + 8) with 24 by lia.
  replace (16 - 8) with 8 by lia.
  replace (16 + 8 + 8) with 32 by lia.
  replace (p + 8 * 1 + 8 * 1) with (p + 16) by lia.
  replace (p + 8 * 1 + 8 * 1 + 8 * 1) with (p + 24) by lia.
  cancel.
  replace (p + 8 * 1) with (p + 8) by lia.
  replace (16 + 8) with 24 by lia.
  replace (p + 16 + 8 * 1) with (p + 24) by lia.
  cancel.
  Unshelve.
  rewrite sizeof_uint64.
  replace (p + 1 * 8) with (p + 8) by lia.
  replace (p + 2 * 8) with (p + 16) by lia.
  replace (p + 3 * 8) with (p + 24) by lia.
  cancel.
Qed.

Lemma basepoint_bytes_strategy21_correctness : basepoint_bytes_strategy21.
  pre_process_default.
  rewrite !sizeof_uint64.
  pose proof (UCharArray.full_merge_to_full
    p 8 16 (sublist 0 8 bytes) (sublist 8 16 bytes) ltac:(lia))
    as Hmerge1.
  rewrite sizeof_uchar in Hmerge1.
  replace (p + 1 * 8) with (p + 8 * 1) by lia.
  sep_apply Hmerge1.
  pose proof (UCharArray.full_merge_to_full
    p 16 24 (List.app (sublist 0 8 bytes) (sublist 8 16 bytes))
    (sublist 16 24 bytes) ltac:(lia)) as Hmerge2.
  rewrite sizeof_uchar in Hmerge2.
  replace (p + 2 * 8) with (p + 16 * 1) by lia.
  sep_apply Hmerge2.
  pose proof (UCharArray.full_merge_to_full
    p 24 32
    (List.app
      (List.app (sublist 0 8 bytes) (sublist 8 16 bytes))
      (sublist 16 24 bytes))
    (sublist 24 32 bytes) ltac:(lia)) as Hmerge3.
  rewrite sizeof_uchar in Hmerge3.
  replace (p + 3 * 8) with (p + 24 * 1) by lia.
  sep_apply Hmerge3.
  assert (Hparts :
    List.app
      (List.app
        (List.app (sublist 0 8 bytes) (sublist 8 16 bytes))
        (sublist 16 24 bytes))
      (sublist 24 32 bytes) = bytes).
  {
    rewrite <- (sublist_split 0 16 8 bytes) by lia.
    rewrite <- (sublist_split 0 24 16 bytes) by lia.
    rewrite <- (sublist_split 0 32 24 bytes) by lia.
    apply sublist_self; symmetry; assumption.
  }
  rewrite Hparts; entailer!.
Qed.

Lemma basepoint_bytes_strategy30_correctness : basepoint_bytes_strategy30.
  pre_process_default.
  replace (base + 0 * sizeof(UINT64)) with base by ring.
  replace (base + 0) with base by lia.
  entailer!.
Qed.

Lemma basepoint_bytes_strategy31_correctness : basepoint_bytes_strategy31.
  pre_process_default.
  replace (base + 0 * sizeof(UINT64)) with base by ring.
  replace (base + 0) with base by lia.
  entailer!.
Qed.

Lemma basepoint_bytes_strategy32_correctness : basepoint_bytes_strategy32.
  pre_process_default.
  subst alias.
  entailer!.
Qed.

Lemma basepoint_bytes_strategy40_correctness : basepoint_bytes_strategy40.
  pre_process_default.
  sep_apply (u8_full32_to_store_fn k value bytes);
    try assumption; try lia.
  entailer!.
Qed.
