Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.sm2.vc.sm3 Require Import sm3_update_goal.
From SimpleC.EE.Applications_human.sm2.vc.sm3 Require Import sm3_update_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_update_lib.
Local Open Scope sac.

Lemma proof_of_sm3_update_entail_wit_10_1 : sm3_update_entail_wit_10_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (k := 64 - Zlength (sm3_tail Prefix)).
  set (rest := sublist k data_len_pre Chunk).
  Exists (sm3_tail Prefix ++ sublist 0 k Chunk).
  Exists (Zlength (Prefix ++ sublist 0 k Chunk) / 64).
  Exists (sm3_compress_bytes SM3_IV
    (sm3_full_bytes (Prefix ++ sublist 0 k Chunk))).
  Exists (sm3_tail rest).
  Exists (sm3_full_bytes rest).
  Exists (sublist 0 k Chunk).
  assert (Hchunk : Chunk = sublist 0 k Chunk ++ rest).
  { subst rest k.
    rewrite <- (sublist_self Chunk data_len_pre (eq_sym PreH13)) at 1.
    rewrite (sublist_split 0 data_len_pre
      (64 - Zlength (sm3_tail Prefix)) Chunk) by lia.
    reflexivity. }
  assert (Hcomplete : Zlength
      (sm3_tail Prefix ++ sublist 0 k Chunk) = 64).
  { subst k. exact PreH2. }
  pose proof (sm3_complete_tail_transition Prefix
    (sublist 0 k Chunk) Hcomplete) as Htransition.
  destruct Htransition as
    [Hphase [Hcompleted_prefix [Hblocks Hdigest]]].
  assert (Hrest : rest = sm3_full_bytes rest ++ sm3_tail rest).
  { apply sm3_full_tail_decompose. }
  assert (Hchunk_three : Chunk = sublist 0 k Chunk ++
      (sm3_full_bytes rest ++ sm3_tail rest)).
  { transitivity (sublist 0 k Chunk ++ rest).
    - exact Hchunk.
    - f_equal. exact Hrest. }
  pose proof (sm3_full_len_properties rest) as Hrest_full.
  assert (Hrestlen : Zlength rest = data_len_pre - k).
  { subst rest k. rewrite Zlength_sublist; lia. }
  assert (Hunsigned :
      unsigned_last_nbits (Zlength Prefix / 64 + 1) 64 =
      Zlength Prefix / 64 + 1).
  { apply unsigned_last_nbits_eq.
    unfold SM3_MAX_BYTES in *.
    pose proof (Zlength_nonneg Prefix).
    assert (Hqnonneg : 0 <= Zlength Prefix / 64) by
      (apply Z.div_pos; lia).
    assert (Hqle : Zlength Prefix / 64 <= Zlength Prefix) by
      (apply Z.div_le_upper_bound; lia).
    lia. }
  assert (Hblock_safe :
      0 <= 64 <= 64 /\
      u8_list_bounded (sm3_tail Prefix ++ sublist 0 k Chunk)).
  { split; [lia | subst k; exact PreH1]. }
  assert (Hstore :
      UCharArray.full &(ctx_pre # "_SM3_CTX" ->ₛ "block") 64
        (sm3_tail Prefix ++ sublist 0 k Chunk) |--
      store_byte_prefix &(ctx_pre # "_SM3_CTX" ->ₛ "block") 64
        (sm3_tail Prefix ++ sublist 0 k Chunk)).
  { unfold store_byte_prefix.
    rewrite Hcomplete.
    rewrite UCharArray.undef_full_empty.
    apply split_pure_and_spatial_goals.
    - rewrite sepcon_emp_equiv. derivable1_refl_tac.
    - apply derivable1s_coq_prop_r. exact Hblock_safe. }
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- Hdigest, Hblocks.
  split_pure_spatial.
  - sep_apply (UCharArray.full_split_to_seg data_pre k data_len_pre
      (sublist 0 k Chunk ++ rest)); try lia.
    sepcon_assoc_change.
    replace (sublist k data_len_pre (sublist 0 k Chunk ++ rest))
      with rest.
    2: { rewrite (sublist_split_app_r k data_len_pre k
           (sublist 0 k Chunk) rest) by
           (subst k; try exact PreH6; lia).
         symmetry. replace (k - k) with 0 by lia.
         apply sublist_self. subst rest k.
         rewrite Zlength_sublist; lia. }
    sep_apply (UCharArray.seg_split_to_seg data_pre k
      (k + sm3_full_len rest) data_len_pre rest); try lia.
    replace (sublist 0 (k + sm3_full_len rest - k) rest)
      with (sm3_full_bytes rest) by
      (unfold sm3_full_bytes; f_equal; lia).
    replace (sublist (k + sm3_full_len rest - k)
      (data_len_pre - k) rest) with (sm3_tail rest) by
      (unfold sm3_tail; f_equal; lia).
    replace (sublist 0 k (sublist 0 k Chunk ++ rest))
      with (sublist 0 k Chunk).
    2: { rewrite sublist_split_app_l;
           [| lia | rewrite Zlength_sublist; lia].
         rewrite (sublist_self (sublist 0 k Chunk) k) by
           (rewrite Zlength_sublist; lia).
         reflexivity. }
    replace (&(ctx_pre # "_SM3_CTX" ->ₛ "digest") +
      0 * sizeof(UINT)) with &(ctx_pre # "_SM3_CTX" ->ₛ "digest") by lia.
    replace (&(ctx_pre # "_SM3_CTX" ->ₛ "block") +
      0 * sizeof(UCHAR)) with &(ctx_pre # "_SM3_CTX" ->ₛ "block") by lia.
    unfold sm3_full_len.
    rewrite Hrestlen.
    LLM_pre_process ltac:(lia || nia || int_auto).
    rewrite <- Hunsigned.
    replace (data_len_pre - (data_len_pre - k)) with k by lia.
    sep_apply Hstore.
    rewrite !Z.quot_div_nonneg by
      (pose proof (Zlength_nonneg Prefix); lia).
    normalize.
    cancel.
  - rewrite !Z.quot_div_nonneg by
      (pose proof (Zlength_nonneg Prefix); lia).
    rewrite !Z.rem_mod_nonneg by lia.
    unfold sm3_update_data_aligned, sm3_compress_input_aligned in *.
    pose proof (sm3_bulk_remainder_offset_zero (data_len_pre - k)
      ltac:(lia)) as Hbulk_offset.
    pose proof (Z.mod_pos_bound (data_len_pre - k) 64) as Hmodrange.
    specialize (Hmodrange ltac:(lia)).
    assert (Hbulk_unsigned :=
      sm3_bulk_length_unsigned (data_len_pre - k) ltac:(
        unfold SM3_MAX_BYTES in *;
        pose proof (Zlength_nonneg Prefix); lia)).
    assert (Hblocks_signed :
        Zlength Prefix / 64 + 1 =
        Zlength (Prefix ++ sublist 0 k Chunk) ÷ 64).
    { rewrite Z.quot_div_nonneg by
        (pose proof (Zlength_nonneg (Prefix ++ sublist 0 k Chunk)); lia).
      symmetry. exact Hblocks. }
    destruct PreH25 as [[Hbuffered_zero _] | [Hbuffered_range Hdata_align]].
    { lia. }
    assert (Hcompress_align :
        (data_len_pre - k) / 64 = 0 \/
        aligned_4 (data_pre + k * sizeof(UCHAR))).
    { destruct Hdata_align as [Hshort | Haligned].
      - left. apply Z.div_small. lia.
      - right.
        rewrite sizeof_uchar.
        replace (data_pre + k * 1) with
          (data_pre + 64 - Zlength (sm3_tail Prefix)) by
          (subst k; lia).
        exact Haligned. }
    assert (Hcompress_align_final :
        (data_len_pre - k) / 64 = 0 \/
        aligned_4
          (data_pre +
           (data_len_pre -
            (64 * ((data_len_pre - k) / 64) +
             (data_len_pre - k) mod 64)) * sizeof(UCHAR))).
    { destruct Hcompress_align as [Hzero | Haligned].
      - left. exact Hzero.
      - right.
        replace
          (data_pre +
           (data_len_pre -
            (64 * ((data_len_pre - k) / 64) +
             (data_len_pre - k) mod 64)) * sizeof(UCHAR)) with
          (data_pre + k * sizeof(UCHAR)) by (f_equal; lia).
        exact Haligned. }
    split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia; try nia; try int_auto;
      try (rewrite Zlength_app; lia);
      try (rewrite Zlength_sublist; lia);
      try (rewrite sm3_full_bytes_length; unfold sm3_full_len;
        rewrite Hrestlen; reflexivity);
      try (rewrite sm3_tail_length, Hrestlen; reflexivity);
      try (left; lia); try (right; assumption).
Qed.

Lemma proof_of_sm3_update_entail_wit_10_2 : sm3_update_entail_wit_10_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (sm3_tail Prefix).
  Exists (Zlength Prefix ÷ 64).
  Exists (sm3_compress_bytes SM3_IV (sm3_full_bytes Prefix)).
  Exists (sm3_tail Chunk).
  Exists (sm3_full_bytes Chunk).
  Exists (@nil Z).
  pose proof (sm3_full_tail_decompose Chunk) as Hchunk.
  pose proof (sm3_full_len_properties Chunk) as Hfull.
  pose proof (sm3_tail_length_range Chunk) as Htailrange.
  assert (Hprefix_nil : sm3_tail (Prefix ++ @nil Z) = @nil Z).
  { rewrite app_nil_r.
    assert (Htail_len : Zlength (sm3_tail Prefix) = 0) by exact PreH14.
    destruct (sm3_tail Prefix) as [|x xs].
    - reflexivity.
    - rewrite Zlength_cons in Htail_len.
      pose proof (Zlength_nonneg xs). lia. }
  assert (Hstore :
      UCharArray.full &(ctx_pre # "_SM3_CTX" ->ₛ "block")
        (Zlength (sm3_tail Prefix)) (sm3_tail Prefix) **
      UCharArray.undef_full
        (&(ctx_pre # "_SM3_CTX" ->ₛ "block") +
          Zlength (sm3_tail Prefix))
        (64 - Zlength (sm3_tail Prefix)) |--
      store_byte_prefix &(ctx_pre # "_SM3_CTX" ->ₛ "block") 64
        (sm3_tail Prefix)).
  { unfold store_byte_prefix.
    apply split_pure_and_spatial_goals.
    - derivable1_refl_tac.
    - apply derivable1s_coq_prop_r. split; [lia | assumption]. }
  pose proof (sm3_bulk_remainder_offset_zero data_len_pre
    ltac:(lia)) as Hbulk_offset.
  assert (Hmodrange := Z.mod_pos_bound data_len_pre 64 ltac:(lia)).
  assert (Hbulk_unsigned := sm3_bulk_length_unsigned data_len_pre ltac:(
    unfold SM3_MAX_BYTES in *;
    pose proof (Zlength_nonneg Prefix); lia)).
  rewrite !Z.quot_div_nonneg by
    (pose proof (Zlength_nonneg Prefix); lia).
  rewrite !Z.rem_mod_nonneg by lia.
  split_pure_spatial.
  - sep_apply (UCharArray.full_split_to_seg data_pre
      (sm3_full_len Chunk) data_len_pre Chunk); try lia.
    replace (sublist 0 (sm3_full_len Chunk) Chunk)
      with (sm3_full_bytes Chunk) by reflexivity.
    replace (sublist (sm3_full_len Chunk) data_len_pre Chunk)
      with (sm3_tail Chunk).
    2: { unfold sm3_tail. rewrite PreH2. reflexivity. }
    sep_apply Hstore.
    replace (data_len_pre - data_len_pre) with 0 by lia.
    rewrite UCharArray.seg_empty.
    unfold sm3_full_len. rewrite PreH2.
    entailer_pure. normalize. cancel.
    replace (0 + 64 * (data_len_pre / 64)) with
      (64 * (data_len_pre / 64)) by lia.
    derivable1_refl_tac.
  - unfold sm3_update_data_aligned, sm3_compress_input_aligned in *.
    destruct PreH13 as [[_ Hdata_align] | [Hbuffered _]]; [|lia].
    assert (Hcompress_align : data_len_pre / 64 = 0 \/ aligned_4 data_pre).
    { destruct Hdata_align as [Hshort | Haligned].
      - left. apply Z.div_small. lia.
      - right. exact Haligned. }
    assert (Hcompress_align_final : data_len_pre / 64 = 0 \/
        aligned_4
          (data_pre +
           (data_len_pre -
            (64 * (data_len_pre / 64) + data_len_pre mod 64)) *
           sizeof(UCHAR))).
    { destruct Hcompress_align as [Hzero | Haligned].
      - left. exact Hzero.
      - right.
        replace
          (data_pre +
           (data_len_pre -
            (64 * (data_len_pre / 64) + data_len_pre mod 64)) *
           sizeof(UCHAR)) with data_pre by (f_equal; lia).
        exact Haligned. }
    assert (Hprefix_blocks :
        Zlength Prefix / 64 = Zlength (Prefix ++ @nil Z) ÷ 64).
    { rewrite app_nil_r, Z.quot_div_nonneg by
        (pose proof (Zlength_nonneg Prefix); lia).
      reflexivity. }
    split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia; try nia; try int_auto;
      try (rewrite Zlength_app, PreH2; lia);
      try (rewrite sm3_full_bytes_length; unfold sm3_full_len;
        rewrite PreH2; reflexivity);
      try (rewrite sm3_tail_length, PreH2; reflexivity);
      try (rewrite app_nil_r; reflexivity);
      try (change (0 = data_len_pre - data_len_pre); lia);
      try (left; lia); try (right; assumption).
Qed.

Lemma proof_of_sm3_update_entail_wit_12_1 : sm3_update_entail_wit_12_1.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (Zlength (Prefix ++ Chunk) / 64).
  Exists (sm3_compress_bytes SM3_IV (sm3_full_bytes (Prefix ++ Chunk))).
  Exists (sm3_tail (Prefix ++ Chunk)).
  Exists BulkBytes_2.
  Exists ConsumedBytes_2.
  pose proof (sm3_completed_prefix_view
    (Prefix ++ ConsumedBytes_2) PreH23) as Hbase_view.
  destruct Hbase_view as [Hbase_full Hbase_mod].
  assert (Hbase_div : (64 | Zlength (Prefix ++ ConsumedBytes_2))).
  { apply Z.mod_divide; [lia | exact Hbase_mod]. }
  destruct Hbase_div as [base_blocks Hbase_blocks].
  rewrite Zlength_app in Hbase_blocks.
  assert (Hwhole :
      Prefix ++ Chunk =
      (Prefix ++ ConsumedBytes_2 ++ BulkBytes_2) ++ TailBytes_2).
  { rewrite PreH20. repeat rewrite app_assoc. reflexivity. }
  assert (Hfull_len :
      sm3_full_len (Prefix ++ Chunk) =
      Zlength (Prefix ++ ConsumedBytes_2 ++ BulkBytes_2)).
  { unfold sm3_full_len.
    assert (Hprefixbulk_len :
      Zlength (Prefix ++ ConsumedBytes_2 ++ BulkBytes_2) =
      (base_blocks + nblock) * 64).
    { rewrite !Zlength_app, PreH18. lia. }
    rewrite Hwhole, Zlength_app, Hprefixbulk_len, PreH19.
    rewrite Z.div_add_l, Z.div_small by lia. ring. }
  assert (Hwhole_full :
      sm3_full_bytes (Prefix ++ Chunk) =
      Prefix ++ ConsumedBytes_2 ++ BulkBytes_2).
  { unfold sm3_full_bytes. rewrite Hfull_len, Hwhole.
    rewrite sublist_app_exact1. reflexivity. }
  assert (Hwhole_tail :
      sm3_tail (Prefix ++ Chunk) = TailBytes_2).
  { pose proof (sm3_full_tail_decompose (Prefix ++ Chunk)) as Hdec.
    rewrite Hwhole_full, Hwhole in Hdec.
    apply app_inv_head in Hdec.
    rewrite Hwhole. symmetry. exact Hdec. }
  assert (Hstate :
      sm3_compress_bytes State_2 BulkBytes_2 =
      sm3_compress_bytes SM3_IV (sm3_full_bytes (Prefix ++ Chunk))).
  { rewrite Hwhole_full.
    replace (Prefix ++ ConsumedBytes_2 ++ BulkBytes_2)
      with ((Prefix ++ ConsumedBytes_2) ++ BulkBytes_2)
      by (symmetry; apply app_assoc).
    rewrite sm3_compress_bytes_app by exact Hbase_mod.
    rewrite <- Hbase_full, <- PreH21. reflexivity. }
  assert (Hblocks :
      NBlocks_2 + nblock = Zlength (Prefix ++ Chunk) / 64).
  { assert (Hprefixbulk_len :
      Zlength (Prefix ++ ConsumedBytes_2 ++ BulkBytes_2) =
      (base_blocks + nblock) * 64).
    { rewrite !Zlength_app, PreH18. lia. }
    rewrite PreH22, Hwhole.
    rewrite (Zlength_app
      (Prefix ++ ConsumedBytes_2 ++ BulkBytes_2) TailBytes_2).
    rewrite Hprefixbulk_len, PreH19.
    rewrite Z.div_add_l, Z.div_small by lia.
    rewrite Z.quot_div_nonneg by
      (pose proof (Zlength_nonneg (Prefix ++ ConsumedBytes_2)); lia).
    rewrite (Zlength_app Prefix ConsumedBytes_2), Hbase_blocks.
    rewrite Z.div_mul by lia. lia. }
  split_pure_spatial.
  - assert (Hnblocks_unsigned :
        unsigned_last_nbits (NBlocks_2 + nblock) 64 =
        Zlength (Prefix ++ Chunk) / 64).
    { rewrite Hblocks. apply unsigned_last_nbits_eq.
      unfold SM3_MAX_BYTES in PreH14.
      pose proof (Zlength_nonneg (Prefix ++ Chunk)).
      split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia. }
    sep_apply (store_byte_prefix_forget_to_undef
      &(ctx_pre # "_SM3_CTX" ->ₛ "block") 64 BlockBytes).
    sep_apply_l_atomic (UCharArray.undef_full_split_to_undef_full
      &(ctx_pre # "_SM3_CTX" ->ₛ "block") left 64 ltac:(lia)).
    assert (Hbulk_seg :
      store_bytes data (64 * nblock) BulkBytes_2 |--
      UCharArray.seg data_pre (data_len_pre - data_len)
        ((data_len_pre - data_len) + 64 * nblock) BulkBytes_2).
    { assert (Hbulk_spatial :
        UCharArray.full data (64 * nblock) BulkBytes_2 |--
        UCharArray.seg data_pre (data_len_pre - data_len)
          ((data_len_pre - data_len) + 64 * nblock) BulkBytes_2).
      { sep_apply UCharArray.full_to_seg.
        replace data
          with (data_pre + (data_len_pre - data_len) * sizeof(UCHAR))
          by (symmetry; exact PreH12).
        replace
          (64 * nblock)
          with
          ((data_len_pre - data_len + 64 * nblock) -
            (data_len_pre - data_len)) by lia.
        rewrite <- (UCharArray.seg_0_shift data_pre
          (data_len_pre - data_len)
          (data_len_pre - data_len + 64 * nblock) BulkBytes_2).
        replace
          (data_len_pre - data_len +
            (data_len_pre - data_len + 64 * nblock -
              (data_len_pre - data_len)))
          with (data_len_pre - data_len + 64 * nblock) by lia.
        derivable1_refl_tac. }
      unfold store_bytes. intros m Hsrc.
      destruct Hsrc as [_ Hsrc]. apply Hbulk_spatial. exact Hsrc. }
    sep_apply Hbulk_seg.
    rewrite Hstate, Hnblocks_unsigned.
    replace (&(ctx_pre # "_SM3_CTX" ->ₛ "digest") + 0 * sizeof(UINT))
      with &(ctx_pre # "_SM3_CTX" ->ₛ "digest") by lia.
    replace ((left - left) * sizeof(UCHAR)) with 0 by lia.
    replace (&(ctx_pre # "_SM3_CTX" ->ₛ "block") + 0)
      with &(ctx_pre # "_SM3_CTX" ->ₛ "block") by lia.
    normalize. cancel. rewrite Hwhole_tail. derivable1_refl_tac.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia; try nia; try int_auto;
      try (rewrite <- Hstate;
        exact (proj2 (sm3_compress_bytes_valid State_2 BulkBytes_2
          (conj PreH2 PreH1))));
      try (rewrite <- Hstate;
        exact (proj1 (sm3_compress_bytes_valid State_2 BulkBytes_2
          (conj PreH2 PreH1))));
      try (rewrite Hwhole_tail; reflexivity);
      try (rewrite Hwhole_tail; exact PreH19);
      try (rewrite Hwhole_tail; exact PreH20);
      try (rewrite Hstate; reflexivity);
      try (rewrite Hblocks; reflexivity);
      try (rewrite Z.quot_div_nonneg by
        (pose proof (Zlength_nonneg (Prefix ++ Chunk)); lia);
        reflexivity).
Qed.

Lemma proof_of_sm3_update_entail_wit_12_2_split_goal_1 : sm3_update_entail_wit_12_2_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_update_entail_wit_12_2_split_goal_2 : sm3_update_entail_wit_12_2_split_goal_2.
Proof. Abort.

Lemma proof_of_sm3_update_entail_wit_12_2_split_goal_3 : sm3_update_entail_wit_12_2_split_goal_3.
Proof. Abort.

Lemma proof_of_sm3_update_entail_wit_12_2_split_goal_4 : sm3_update_entail_wit_12_2_split_goal_4.
Proof. Abort.

Lemma proof_of_sm3_update_entail_wit_12_2_split_goal_5 : sm3_update_entail_wit_12_2_split_goal_5.
Proof. Abort.

Lemma proof_of_sm3_update_entail_wit_12_2_split_goal_6 : sm3_update_entail_wit_12_2_split_goal_6.
Proof. Abort.

Lemma proof_of_sm3_update_entail_wit_12_2_split_goal_spatial : sm3_update_entail_wit_12_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm3_update_entail_wit_12_2 : sm3_update_entail_wit_12_2.
Proof.
  right.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hnblock : nblock = 0) by lia.
  assert (Hbulk : BulkBytes_2 = nil).
  { destruct BulkBytes_2 as [|x xs].
    - reflexivity.
    - rewrite Zlength_cons in PreH16.
      pose proof (Zlength_nonneg xs). rewrite Hnblock in PreH16. lia. }
  pose proof (sm3_completed_prefix_view
    (Prefix ++ ConsumedBytes_2) PreH21) as Hbase_view.
  destruct Hbase_view as [Hbase_full Hbase_mod].
  assert (Hwhole :
      Prefix ++ Chunk = (Prefix ++ ConsumedBytes_2) ++ TailBytes_2).
  { rewrite PreH18, Hbulk. cbn. repeat rewrite app_assoc. reflexivity. }
  assert (Hwhole_full :
      sm3_full_bytes (Prefix ++ Chunk) = Prefix ++ ConsumedBytes_2).
  { unfold sm3_full_bytes, sm3_full_len.
    rewrite Hwhole, Zlength_app, PreH17.
    pose proof (Z.div_mod (Zlength (Prefix ++ ConsumedBytes_2)) 64
      ltac:(lia)) as Hdivmod.
    rewrite Hbase_mod in Hdivmod.
    replace
      (64 * ((Zlength (Prefix ++ ConsumedBytes_2) + left) / 64))
      with (Zlength (Prefix ++ ConsumedBytes_2)).
    - rewrite sublist_app_exact1. reflexivity.
    - assert (Hquot :
          (Zlength (Prefix ++ ConsumedBytes_2) + left) / 64 =
          Zlength (Prefix ++ ConsumedBytes_2) / 64).
      { rewrite Hdivmod.
        replace
          (64 * (Zlength (Prefix ++ ConsumedBytes_2) / 64) + 0 + left)
          with
          ((Zlength (Prefix ++ ConsumedBytes_2) / 64) * 64 + left)
          by ring.
        replace
          (64 * (Zlength (Prefix ++ ConsumedBytes_2) / 64) + 0)
          with
          ((Zlength (Prefix ++ ConsumedBytes_2) / 64) * 64 + 0)
          by ring.
        rewrite !Z.div_add_l by lia.
        rewrite (Z.div_small left 64) by exact (conj PreH4 PreH5).
        reflexivity. }
      rewrite Hquot. lia. }
  assert (Hwhole_tail : sm3_tail (Prefix ++ Chunk) = TailBytes_2).
  { pose proof (sm3_full_tail_decompose (Prefix ++ Chunk)) as Hdec.
    rewrite Hwhole_full in Hdec.
    rewrite Hwhole in Hdec at 1.
    apply app_inv_head in Hdec. symmetry. exact Hdec. }
  assert (Hstate :
      State_2 = sm3_compress_bytes SM3_IV
        (sm3_full_bytes (Prefix ++ Chunk))).
  { rewrite Hwhole_full, <- Hbase_full. exact PreH19. }
  assert (Hblocks :
      NBlocks_2 = Zlength (Prefix ++ Chunk) / 64).
  { pose proof (Z.div_mod (Zlength (Prefix ++ ConsumedBytes_2)) 64
      ltac:(lia)) as Hdivmod2.
    rewrite Hbase_mod in Hdivmod2.
    assert (Hquot2 :
        (Zlength (Prefix ++ ConsumedBytes_2) + left) / 64 =
        Zlength (Prefix ++ ConsumedBytes_2) / 64).
    { rewrite Hdivmod2.
      replace
        (64 * (Zlength (Prefix ++ ConsumedBytes_2) / 64) + 0 + left)
        with
        ((Zlength (Prefix ++ ConsumedBytes_2) / 64) * 64 + left)
        by ring.
      replace
        (64 * (Zlength (Prefix ++ ConsumedBytes_2) / 64) + 0)
        with
        ((Zlength (Prefix ++ ConsumedBytes_2) / 64) * 64 + 0)
        by ring.
      rewrite !Z.div_add_l by lia.
      rewrite (Z.div_small left 64) by exact (conj PreH4 PreH5).
      reflexivity. }
    rewrite PreH20, Hwhole.
    rewrite (Zlength_app (Prefix ++ ConsumedBytes_2) TailBytes_2).
    rewrite PreH17, Hquot2.
    rewrite Z.quot_div_nonneg by
      (pose proof (Zlength_nonneg (Prefix ++ ConsumedBytes_2)); lia).
    reflexivity. }
  split_pure_spatial.
  - sep_apply (store_byte_prefix_forget_to_undef
      &(ctx_pre # "_SM3_CTX" ->ₛ "block") 64 BlockBytes).
    sep_apply_l_atomic (UCharArray.undef_full_split_to_undef_full
      &(ctx_pre # "_SM3_CTX" ->ₛ "block") left 64 ltac:(lia)).
    replace ((left - left) * sizeof(UCHAR)) with 0 by lia.
    replace (&(ctx_pre # "_SM3_CTX" ->ₛ "block") + 0)
      with &(ctx_pre # "_SM3_CTX" ->ₛ "block") by lia.
    normalize. cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia; try nia; try int_auto;
      try (rewrite Hwhole_tail; exact PreH18);
      try (rewrite Hwhole_tail; exact PreH17);
      try (rewrite Hstate; reflexivity);
      try (rewrite Hblocks; reflexivity);
      try (rewrite Z.quot_div_nonneg by
        (pose proof (Zlength_nonneg (Prefix ++ Chunk)); lia);
        exact Hblocks);
      try (rewrite Z.quot_div_nonneg by
        (pose proof (Zlength_nonneg (Prefix ++ Chunk)); lia);
        reflexivity).
Qed.

Lemma proof_of_sm3_update_entail_wit_14 : sm3_update_entail_wit_14.
Proof.
  right. intros. entailer!.
Qed.

Lemma proof_of_sm3_update_entail_wit_15 : sm3_update_entail_wit_15.
Proof.
  right. intros. entailer!.
Qed.

Lemma proof_of_sm3_update_return_wit_1_split_goal_1 : sm3_update_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH1.
  assert (Hrange : store_bytes retval data_len_pre Chunk |--
    “ u8_list_bounded Chunk ”).
  { unfold store_bytes.
    apply coq_prop_andp_left; intros Hbytes.
    dump_pre_spatial. tauto. }
  prop_apply_p Hrange. Intros_p Hbytes. dump_pre_spatial.
  unfold u8_list_bounded in *.
  rewrite limb_list_bounded_app. tauto.
Qed.

Lemma proof_of_sm3_update_return_wit_1_split_goal_2 : sm3_update_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH1.
  assert (Hlength : store_bytes retval data_len_pre Chunk |--
    “ Zlength Chunk = data_len_pre ”).
  { unfold store_bytes.
    apply coq_prop_andp_left; intros Hbytes.
    dump_pre_spatial. tauto. }
  prop_apply_p Hlength. Intros_p HChunkLen. dump_pre_spatial.
  rewrite Zlength_app. lia.
Qed.

Lemma proof_of_sm3_update_return_wit_1_split_goal_3 : sm3_update_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH1.
  assert (Hlen : store_bytes retval data_len_pre Chunk |--
      “ Zlength Chunk = data_len_pre ”).
  { unfold store_bytes. apply coq_prop_andp_left; intros H.
    dump_pre_spatial. tauto. }
  sep_apply Hlen. Intros_p HChunkLen. dump_pre_spatial.
  assert (Hdecomp :
      Prefix ++ Chunk =
      sm3_full_bytes Prefix ++ (sm3_tail Prefix ++ Chunk)).
  { pose proof (sm3_full_tail_decompose Prefix) as H.
    rewrite H at 1. repeat rewrite app_assoc. reflexivity. }
  assert (Htail_len :
      Zlength (sm3_tail Prefix ++ Chunk) < 64).
  { rewrite Zlength_app, HChunkLen. lia. }
  assert (Hfull_len :
      sm3_full_len (Prefix ++ Chunk) = Zlength (sm3_full_bytes Prefix)).
  { unfold sm3_full_len. rewrite Hdecomp.
    rewrite (Zlength_app (sm3_full_bytes Prefix)
      (sm3_tail Prefix ++ Chunk)).
    pose proof (Z.div_mod (Zlength (sm3_full_bytes Prefix)) 64
      ltac:(lia)) as Hdivmod.
    rewrite sm3_full_bytes_length_multiple in Hdivmod.
    assert (Hquot :
        (Zlength (sm3_full_bytes Prefix) +
          Zlength (sm3_tail Prefix ++ Chunk)) / 64 =
        Zlength (sm3_full_bytes Prefix) / 64).
    { rewrite Hdivmod.
      replace
        (64 * (Zlength (sm3_full_bytes Prefix) / 64) + 0 +
          Zlength (sm3_tail Prefix ++ Chunk))
        with
        ((Zlength (sm3_full_bytes Prefix) / 64) * 64 +
          Zlength (sm3_tail Prefix ++ Chunk)) by ring.
      replace
        (64 * (Zlength (sm3_full_bytes Prefix) / 64) + 0)
        with
        ((Zlength (sm3_full_bytes Prefix) / 64) * 64 + 0) by ring.
      rewrite !Z.div_add_l by lia.
      rewrite (Z.div_small (Zlength (sm3_tail Prefix ++ Chunk)) 64)
        by (pose proof (Zlength_nonneg (sm3_tail Prefix ++ Chunk)); lia).
      reflexivity. }
    rewrite Hquot. lia. }
  f_equal. unfold sm3_full_bytes at 2.
  rewrite Hfull_len, Hdecomp, sublist_app_exact1. reflexivity.
Qed.

Lemma proof_of_sm3_update_return_wit_1_split_goal_4 : sm3_update_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH1.
  assert (Hlen : store_bytes retval data_len_pre Chunk |--
      “ Zlength Chunk = data_len_pre ”).
  { unfold store_bytes. apply coq_prop_andp_left; intros H.
    dump_pre_spatial. tauto. }
  sep_apply Hlen. Intros_p HChunkLen. dump_pre_spatial.
  pose proof (Zlength_nonneg Chunk) as HChunkNonneg.
  rewrite (sm3_tail_length (Prefix ++ Chunk)),
    (sm3_tail_length Prefix), Zlength_app, HChunkLen.
  rewrite Z.add_mod by lia.
  rewrite <- (sm3_tail_length Prefix).
  rewrite (Z.mod_small data_len_pre 64) by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma proof_of_sm3_update_return_wit_1_split_goal_5 : sm3_update_return_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH1.
  assert (Hlen : store_bytes retval data_len_pre Chunk |--
      “ Zlength Chunk = data_len_pre ”).
  { unfold store_bytes. apply coq_prop_andp_left; intros H.
    dump_pre_spatial. tauto. }
  sep_apply Hlen. Intros_p HChunkLen. dump_pre_spatial.
  pose proof (Zlength_nonneg Chunk) as HChunkNonneg.
  pose proof (Z.div_mod (Zlength Prefix) 64 ltac:(lia)) as Hdivmod.
  rewrite <- sm3_tail_length in Hdivmod.
  rewrite Zlength_app, HChunkLen.
  rewrite !Z.quot_div_nonneg by
    (pose proof (Zlength_nonneg Prefix); lia).
  symmetry.
  rewrite Hdivmod.
  replace
    (64 * (Zlength Prefix / 64) + Zlength (sm3_tail Prefix) +
      data_len_pre)
    with
    ((Zlength Prefix / 64) * 64 +
      (Zlength (sm3_tail Prefix) + data_len_pre)) by ring.
  replace
    (64 * (Zlength Prefix / 64) + Zlength (sm3_tail Prefix))
    with
    ((Zlength Prefix / 64) * 64 + Zlength (sm3_tail Prefix)) by ring.
  rewrite !Z.div_add_l by lia.
  rewrite (Z.div_small (Zlength (sm3_tail Prefix) + data_len_pre) 64)
    by lia.
  rewrite (Z.div_small (Zlength (sm3_tail Prefix)) 64) by lia.
  reflexivity.
Qed.

Lemma proof_of_sm3_update_return_wit_1_split_goal_6 : sm3_update_return_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply derivable1s_coq_prop_r. apply Zlength_nonneg.
Qed.

Lemma proof_of_sm3_update_return_wit_1_split_goal_7 : sm3_update_return_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply derivable1s_coq_prop_r.
  pose proof (sm3_tail_length_range (Prefix ++ Chunk)). lia.
Qed.

Lemma proof_of_sm3_update_return_wit_1_split_goal_8 : sm3_update_return_wit_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH1.
  assert (Hbounded : store_bytes retval data_len_pre Chunk |--
      “ u8_list_bounded Chunk ”).
  { unfold store_bytes. apply coq_prop_andp_left; intros H.
    dump_pre_spatial. tauto. }
  sep_apply Hbounded. Intros_p HChunkBounded. dump_pre_spatial.
  apply sm3_tail_bounded.
  unfold u8_list_bounded in *.
  rewrite limb_list_bounded_app. tauto.
Qed.

Lemma proof_of_sm3_update_return_wit_1_split_goal_spatial : sm3_update_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- PreH1.
  assert (Hview : store_bytes retval data_len_pre Chunk |--
      “ Zlength Chunk = data_len_pre /\ u8_list_bounded Chunk ” &&
      UCharArray.full retval data_len_pre Chunk).
  { unfold store_bytes. derivable1_refl_tac. }
  sep_apply Hview. Intros_p Hstore.
  destruct Hstore as [HChunkLen HChunkBounded].
  assert (Hdecomp :
      Prefix ++ Chunk =
      sm3_full_bytes Prefix ++ (sm3_tail Prefix ++ Chunk)).
  { pose proof (sm3_full_tail_decompose Prefix) as H.
    rewrite H at 1. repeat rewrite app_assoc. reflexivity. }
  assert (Htail_len : Zlength (sm3_tail Prefix ++ Chunk) < 64).
  { rewrite Zlength_app, HChunkLen. lia. }
  assert (Hfull_len :
      sm3_full_len (Prefix ++ Chunk) = Zlength (sm3_full_bytes Prefix)).
  { unfold sm3_full_len. rewrite Hdecomp.
    rewrite (Zlength_app (sm3_full_bytes Prefix)
      (sm3_tail Prefix ++ Chunk)).
    pose proof (Z.div_mod (Zlength (sm3_full_bytes Prefix)) 64
      ltac:(lia)) as Hdivmod.
    rewrite sm3_full_bytes_length_multiple in Hdivmod.
    assert (Hquot :
        (Zlength (sm3_full_bytes Prefix) +
          Zlength (sm3_tail Prefix ++ Chunk)) / 64 =
        Zlength (sm3_full_bytes Prefix) / 64).
    { rewrite Hdivmod.
      replace
        (64 * (Zlength (sm3_full_bytes Prefix) / 64) + 0 +
          Zlength (sm3_tail Prefix ++ Chunk))
        with
        ((Zlength (sm3_full_bytes Prefix) / 64) * 64 +
          Zlength (sm3_tail Prefix ++ Chunk)) by ring.
      replace
        (64 * (Zlength (sm3_full_bytes Prefix) / 64) + 0)
        with
        ((Zlength (sm3_full_bytes Prefix) / 64) * 64 + 0) by ring.
      rewrite !Z.div_add_l by lia.
      rewrite (Z.div_small (Zlength (sm3_tail Prefix ++ Chunk)) 64)
        by (pose proof (Zlength_nonneg (sm3_tail Prefix ++ Chunk)); lia).
      reflexivity. }
    rewrite Hquot. lia. }
  assert (Hwhole_full :
      sm3_full_bytes (Prefix ++ Chunk) = sm3_full_bytes Prefix).
  { unfold sm3_full_bytes at 1.
    rewrite Hfull_len, Hdecomp, sublist_app_exact1. reflexivity. }
  assert (Hwhole_tail :
      sm3_tail (Prefix ++ Chunk) = sm3_tail Prefix ++ Chunk).
  { pose proof (sm3_full_tail_decompose (Prefix ++ Chunk)) as H.
    rewrite Hwhole_full in H.
    rewrite Hdecomp in H at 1.
    apply app_inv_head in H. symmetry. exact H. }
  pose proof (Zlength_nonneg Chunk) as HChunkNonneg.
  rewrite PreH1.
  replace data_len_pre with
    (Zlength (sm3_tail Prefix) + data_len_pre -
      Zlength (sm3_tail Prefix)) by lia.
  sep_apply_l_atomic (UCharArray.full_merge_to_full
    &(ctx_pre # "_SM3_CTX" ->ₛ "block")
    (Zlength (sm3_tail Prefix))
    (Zlength (sm3_tail Prefix) + data_len_pre)
    (sm3_tail Prefix) Chunk ltac:(lia)).
  rewrite sizeof_uchar.
  rewrite Hwhole_tail, Zlength_app, HChunkLen.
  normalize. cancel.
  replace
    (Zlength (sm3_tail Prefix) +
      (Zlength (sm3_tail Prefix) + data_len_pre -
        Zlength (sm3_tail Prefix)))
    with (Zlength (sm3_tail Prefix) + data_len_pre) by lia.
  replace
    (64 - Zlength (sm3_tail Prefix) -
      (Zlength (sm3_tail Prefix) + data_len_pre -
        Zlength (sm3_tail Prefix)))
    with (64 - (Zlength (sm3_tail Prefix) + data_len_pre)) by lia.
  replace
    (&(ctx_pre # "_SM3_CTX" ->ₛ "block") + Zlength (sm3_tail Prefix) +
      (Zlength (sm3_tail Prefix) + data_len_pre -
        Zlength (sm3_tail Prefix)) * 1)
    with
    (&(ctx_pre # "_SM3_CTX" ->ₛ "block") +
      (Zlength (sm3_tail Prefix) + data_len_pre)) by lia.
  derivable1_refl_tac.
Qed.

Lemma proof_of_sm3_update_return_wit_1 : sm3_update_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm3_update_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_sm3_update_return_wit_1_split_goal_1.
  - Goal_apply proof_of_sm3_update_return_wit_1_split_goal_2.
  - Goal_apply proof_of_sm3_update_return_wit_1_split_goal_3.
  - Goal_apply proof_of_sm3_update_return_wit_1_split_goal_4.
  - Goal_apply proof_of_sm3_update_return_wit_1_split_goal_5.
  - Goal_apply proof_of_sm3_update_return_wit_1_split_goal_6.
  - Goal_apply proof_of_sm3_update_return_wit_1_split_goal_7.
  - Goal_apply proof_of_sm3_update_return_wit_1_split_goal_8.
Qed.

Lemma proof_of_sm3_update_return_wit_2_split_goal_1 : sm3_update_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_update_return_wit_2_split_goal_2 : sm3_update_return_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_sm3_update_return_wit_2_split_goal_3 : sm3_update_return_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_sm3_update_return_wit_2_split_goal_4 : sm3_update_return_wit_2_split_goal_4.
Proof. Abort.

Lemma proof_of_sm3_update_return_wit_2_split_goal_5 : sm3_update_return_wit_2_split_goal_5.
Proof. Abort.

Lemma proof_of_sm3_update_return_wit_2_split_goal_6 : sm3_update_return_wit_2_split_goal_6.
Proof. Abort.

Lemma proof_of_sm3_update_return_wit_2_split_goal_spatial : sm3_update_return_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm3_update_return_wit_2 : sm3_update_return_wit_2.
Proof.
  right.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Zlength_nonneg BulkBytes) as HBulkNonneg.
  sep_apply UCharArray.full_to_seg.
  sep_apply (UCharArray.seg_merge_to_seg
    data_pre 0 (data_len_pre - data_len)
    (data_len_pre - data_len + 64 * nblock)
    ConsumedBytes BulkBytes ltac:(lia)).
  prop_apply (snaive_uchar_seg_values_bounded data_pre 0
    (data_len_pre - data_len + 64 * nblock)
    (ConsumedBytes ++ BulkBytes)).
  Intros_p HConsumedBulkBounded.
  sep_apply_l_atomic (UCharArray.seg_to_full data_pre 0
    (data_len_pre - data_len + 64 * nblock)
    (ConsumedBytes ++ BulkBytes)).
  sep_apply_l_atomic (UCharArray.seg_to_full data offset
    (offset + left) TailBytes).
  assert (Hchunk_len : Zlength Chunk = data_len_pre).
  { subst Chunk. repeat rewrite Zlength_app. lia. }
  assert (Hchunk_bounded : u8_list_bounded Chunk).
  { rewrite PreH18. unfold u8_list_bounded in *.
    rewrite limb_list_bounded_app in HConsumedBulkBounded.
    rewrite !limb_list_bounded_app. tauto. }
  replace data with
    (data_pre + (data_len_pre - data_len) * sizeof(UCHAR))
    by (symmetry; exact PreH12).
  replace offset with (64 * nblock) by (symmetry; exact PreH6).
  replace
    (data_pre + (data_len_pre - data_len) * sizeof(UCHAR) +
      64 * nblock * sizeof(UCHAR))
    with
    (data_pre + (data_len_pre - data_len + 64 * nblock) * sizeof(UCHAR))
    by ring.
  replace left with
    (data_len_pre - (data_len_pre - data_len + 64 * nblock)) by lia.
  replace (data_pre + 0 * sizeof(UCHAR)) with data_pre by lia.
  replace (data_len_pre - data_len + 64 * nblock - 0)
    with (data_len_pre - data_len + 64 * nblock) by lia.
  replace
    (64 * nblock +
      (data_len_pre - (data_len_pre - data_len + 64 * nblock)) -
      64 * nblock)
    with (data_len_pre - (data_len_pre - data_len + 64 * nblock)) by lia.
  sep_apply_l_atomic (UCharArray.full_merge_to_full
    data_pre (data_len_pre - data_len + 64 * nblock) data_len_pre
    (ConsumedBytes ++ BulkBytes) TailBytes ltac:(lia)).
  sep_apply_l_atomic (UCharArray.seg_to_full
    &(ctx_pre # "_SM3_CTX" ->ₛ "block") 0
    (data_len_pre - (data_len_pre - data_len + 64 * nblock)) TailBytes).
  rewrite PreH21, Hchunk_len.
  split_pure_spatial.
  - replace
      (data_len_pre - (data_len_pre - data_len + 64 * nblock))
      with (Zlength (sm3_tail (Prefix ++ Chunk)))
      by (rewrite <- PreH21, PreH17; lia).
    replace
      ((ConsumedBytes ++ BulkBytes) ++ sm3_tail (Prefix ++ Chunk))
      with Chunk
      by (rewrite <- PreH21, PreH18; apply app_assoc).
    replace
      (Zlength (sm3_tail (Prefix ++ Chunk)) - 0)
      with (Zlength (sm3_tail (Prefix ++ Chunk))) by lia.
    replace
      (&(ctx_pre # "_SM3_CTX" ->ₛ "block") + 0 * sizeof(UCHAR))
      with &(ctx_pre # "_SM3_CTX" ->ₛ "block") by lia.
    rewrite sizeof_uchar.
    replace
      (&(ctx_pre # "_SM3_CTX" ->ₛ "block") +
        Zlength (sm3_tail (Prefix ++ Chunk)) * 1)
      with
      (&(ctx_pre # "_SM3_CTX" ->ₛ "block") +
        Zlength (sm3_tail (Prefix ++ Chunk))) by lia.
    normalize. cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia; try nia; try int_auto;
      try (rewrite Hchunk_len; reflexivity);
      try (exact Hchunk_bounded);
      try (rewrite <- PreH21, PreH17; lia);
      try (apply Zlength_nonneg);
      try (unfold u8_list_bounded in *;
        rewrite limb_list_bounded_app; tauto).
Qed.

Lemma proof_of_sm3_update_partial_solve_wit_3_pure_split_goal_1 : sm3_update_partial_solve_wit_3_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_update_partial_solve_wit_3_pure_split_goal_2 : sm3_update_partial_solve_wit_3_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm3_update_partial_solve_wit_3_pure_split_goal_3 : sm3_update_partial_solve_wit_3_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_sm3_update_partial_solve_wit_3_pure : sm3_update_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pures.
  - dump_pre_spatial. unfold sm3_compress_input_aligned. right.
    replace (&(ctx_pre # "_SM3_CTX" ->ₛ "block") +
      0 * sizeof(UCHAR)) with &(ctx_pre # "_SM3_CTX" ->ₛ "block") by lia.
    assumption.
  - dump_pre_spatial. rewrite Zlength_app, Zlength_sublist; lia.
  - dump_pre_spatial. unfold u8_list_bounded in *.
    rewrite limb_list_bounded_app. split.
    + apply sm3_tail_bounded; assumption.
    + apply limb_list_bounded_sublist; [assumption | lia].
Qed.

Lemma proof_of_sm3_update_partial_solve_wit_4_pure_split_goal_1 : sm3_update_partial_solve_wit_4_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_update_partial_solve_wit_4_pure : sm3_update_partial_solve_wit_4_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pures.
  - dump_pre_spatial. unfold sm3_compress_input_aligned; assumption.
  - sep_apply (snaive_uchar_seg_values_bounded data_pre
      (data_len_pre - data_len)
      (data_len_pre - data_len + 64 * nblock) BulkBytes).
    Intros. apply derivable1s_coq_prop_r; assumption.
Qed.

Lemma proof_of_sm3_update_partial_solve_wit_5_pure_split_goal_1 : sm3_update_partial_solve_wit_5_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_update_partial_solve_wit_5_pure : sm3_update_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pures.
  - dump_pre_spatial; lia.
  - sep_apply (snaive_uchar_seg_values_bounded data_pre
      ((data_len_pre - data_len) + 64 * nblock) data_len_pre TailBytes).
    Intros. apply derivable1s_coq_prop_r; assumption.
Qed.
