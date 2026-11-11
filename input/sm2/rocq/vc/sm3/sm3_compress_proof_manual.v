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
From SimpleC.EE.Applications_human.sm2.vc.sm3 Require Import sm3_compress_goal.
From SimpleC.EE.Applications_human.sm2.vc.sm3 Require Import sm3_compress_proof_auto.
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
Local Open Scope sac.

Lemma proof_of_ONE_ROUND_16_return_wit_1_split_goal_1 : ONE_ROUND_16_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  change (Z.to_nat 1) with (S O).
  cbn [sm3_rounds_aux sm3_round].
  rewrite <- SM3_TI_VALUES_Znth by lia.
  unfold sm3_ff, sm3_gg, sm3_rotl32, rotate_left,
    sm3_p0, sm3_expanded_word_prime.
  replace (Z.ltb idx_pre 16) with true by
    (symmetry; apply Z.ltb_lt; lia).
  cbn beta iota.
  repeat rewrite unsigned_unsigned_add_l_add_other by lia.
  repeat rewrite unsigned_unsigned_add_l by lia.
  replace (12 mod 32) with 12 by reflexivity.
  replace (7 mod 32) with 7 by reflexivity.
  replace (9 mod 32) with 9 by reflexivity.
  replace (17 mod 32) with 17 by reflexivity.
  replace (19 mod 32) with 19 by reflexivity.
  repeat rewrite Z.mod_small by lia.
  repeat rewrite Z.rem_small by lia.
  repeat rewrite unsigned_unsigned_add_l_add_other by lia.
  repeat rewrite unsigned_unsigned_add_l by lia.
  repeat f_equal.
  all: try reflexivity; try lia; try ring; try congruence; try int_auto.
Qed.

Lemma proof_of_ONE_ROUND_16_return_wit_1 : ONE_ROUND_16_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ONE_ROUND_16_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_ONE_ROUNDS_16_return_wit_1_split_goal_1 : ONE_ROUNDS_16_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  change (Z.to_nat 1) with (S O) in *.
  change (Z.to_nat 4) with (S (S (S (S O)))).
  cbn [sm3_rounds_aux] in *.
  rewrite PreH1, PreH2, PreH3, PreH4.
  replace (idx_pre + 1 + 1) with (idx_pre + 2) by lia.
  replace (idx_pre + 2 + 1) with (idx_pre + 3) by lia.
  reflexivity.
Qed.

Lemma proof_of_ONE_ROUNDS_16_return_wit_1 : ONE_ROUNDS_16_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ONE_ROUNDS_16_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_ONE_ROUND_64_return_wit_1_split_goal_1 : ONE_ROUND_64_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  change (Z.to_nat 1) with (S O).
  cbn [sm3_rounds_aux sm3_round].
  rewrite <- SM3_TI_VALUES_Znth by lia.
  unfold sm3_ff, sm3_gg, sm3_rotl32, rotate_left,
    sm3_p0, sm3_expanded_word_prime.
  replace (Z.ltb idx_pre 16) with false by
    (symmetry; apply Z.ltb_ge; lia).
  cbn beta iota.
  repeat rewrite unsigned_unsigned_add_l_add_other by lia.
  repeat rewrite unsigned_unsigned_add_l by lia.
  replace (12 mod 32) with 12 by reflexivity.
  replace (7 mod 32) with 7 by reflexivity.
  replace (9 mod 32) with 9 by reflexivity.
  replace (17 mod 32) with 17 by reflexivity.
  replace (19 mod 32) with 19 by reflexivity.
  repeat rewrite Z.mod_small by lia.
  repeat rewrite Z.rem_small by lia.
  repeat rewrite unsigned_unsigned_add_l_add_other by lia.
  repeat rewrite unsigned_unsigned_add_l by lia.
  repeat f_equal.
  all: try reflexivity; try lia; try ring; try congruence; try int_auto.
Qed.

Lemma proof_of_ONE_ROUND_64_return_wit_1 : ONE_ROUND_64_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ONE_ROUND_64_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_ONE_ROUNDS_64_return_wit_1_split_goal_1 : ONE_ROUNDS_64_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  change (Z.to_nat 1) with (S O) in *.
  change (Z.to_nat 4) with (S (S (S (S O)))).
  cbn [sm3_rounds_aux] in *.
  rewrite PreH1, PreH2, PreH3, PreH4.
  replace (idx_pre + 1 + 1) with (idx_pre + 2) by lia.
  replace (idx_pre + 2 + 1) with (idx_pre + 3) by lia.
  reflexivity.
Qed.

Lemma proof_of_ONE_ROUNDS_64_return_wit_1 : ONE_ROUNDS_64_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ONE_ROUNDS_64_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_sm3_compress_entail_wit_2_split_goal_1 : sm3_compress_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  change (sublist 0 (64 * 0) Blocks) with (@nil Z).
  cbn [sm3_compress_bytes sm3_compress_blocks_aux].
  rewrite Zlength_correct in PreH5.
  replace 8 with (Z.of_nat 8) in PreH5 by reflexivity.
  apply Nat2Z.inj in PreH5.
  destruct State as [|s0 tail0]; cbn in PreH5; try discriminate.
  destruct tail0 as [|s1 tail1]; cbn in PreH5; try discriminate.
  destruct tail1 as [|s2 tail2]; cbn in PreH5; try discriminate.
  destruct tail2 as [|s3 tail3]; cbn in PreH5; try discriminate.
  destruct tail3 as [|s4 tail4]; cbn in PreH5; try discriminate.
  destruct tail4 as [|s5 tail5]; cbn in PreH5; try discriminate.
  destruct tail5 as [|s6 tail6]; cbn in PreH5; try discriminate.
  destruct tail6 as [|s7 tail7]; cbn in PreH5; try discriminate.
  destruct tail7 as [|extra tail8]; cbn [Znth] in PreH5 |-; try discriminate.
  reflexivity.
Qed.

Lemma proof_of_sm3_compress_entail_wit_2_split_goal_2 : sm3_compress_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm3_compress_entail_wit_2_split_goal_3 : sm3_compress_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (sm3_compress_input_aligned_nonempty block_pre nblocks_pre); assumption.
Qed.

Lemma proof_of_sm3_compress_entail_wit_2_split_goal_4 : sm3_compress_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm3_compress_entail_wit_2_split_goal_5 : sm3_compress_entail_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm3_compress_entail_wit_2_split_goal_6 : sm3_compress_entail_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Zlength_nonneg Blocks).
  lia.
Qed.

Lemma proof_of_sm3_compress_entail_wit_2_split_goal_7 : sm3_compress_entail_wit_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm3_compress_entail_wit_2 : sm3_compress_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm3_compress_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_sm3_compress_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_sm3_compress_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_sm3_compress_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_sm3_compress_entail_wit_2_split_goal_5.
  - Goal_apply proof_of_sm3_compress_entail_wit_2_split_goal_6.
  - Goal_apply proof_of_sm3_compress_entail_wit_2_split_goal_7.
Qed.

Lemma proof_of_sm3_compress_entail_wit_3_split_goal_1 : sm3_compress_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm3_compress_entail_wit_3_split_goal_2 : sm3_compress_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold u8_list_bounded in *.
  apply limb_list_bounded_sublist.
  - exact PreH12.
  - lia.
Qed.

Lemma proof_of_sm3_compress_entail_wit_3_split_goal_3 : sm3_compress_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma proof_of_sm3_compress_entail_wit_3 : sm3_compress_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm3_compress_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_sm3_compress_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_sm3_compress_entail_wit_3_split_goal_3.
Qed.

Lemma proof_of_sm3_compress_entail_wit_4_split_goal_1 : sm3_compress_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (proj2 (list_eq_ext _ _ 0)).
  split.
  - rewrite !Zlength_sublist by
      (rewrite ?Zlength_replace_Znth, ?sm3_block_words_length; lia).
    lia.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by
      (rewrite Zlength_replace_Znth; lia).
    rewrite !Znth_sublist by lia.
    replace (0 + k) with k by lia.
    destruct (Z.eq_dec k j) as [-> | Hneq].
    + replace (j + 0) with j by lia.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite sm3_block_words_Znth by lia.
      unfold sm3_block_word.
      replace (pblock + j * sizeof (UINT) - pblock) with (4 * j) by
        (rewrite sizeof_uint; lia).
      assert (Hword_range :
        0 <= u8_list_value
          (sublist (4 * j) (4 * j + 4)
            (sublist (64 * BlockIndex) (64 * BlockIndex + 64) Blocks)) <
        2 ^ 32).
      {
        unfold u8_list_value, u8_list_bounded in *.
        pose proof
          (limb_list_value_range SM2_BYTE_BASE
            (sublist (4 * j) (4 * j + 4)
              (sublist (64 * BlockIndex) (64 * BlockIndex + 64) Blocks))
            sm2_byte_base_positive) as Hrange.
        specialize (Hrange ltac:(
          apply limb_list_bounded_sublist; [exact PreH16 |]; lia)).
        rewrite Zlength_sublist in Hrange by lia.
        replace (4 * j + 4 - 4 * j) with 4 in Hrange by lia.
        unfold limb_radix, SM2_BYTE_BASE in Hrange |- *.
        exact Hrange.
      }
      assert (Hmask :
        unsigned_last_nbits 16711680 32 = 16711680).
      { apply unsigned_last_nbits_eq. lia. }
      rewrite <- Hmask at 1.
      rewrite <- unsigned_last_nbits_land_clear_l by lia.
      rewrite Hmask.
      rewrite byte_swap32_frontend_equiv by exact Hword_range.
      apply sm3_block_word_from_little_endian.
      * exact PreH15.
      * exact PreH16.
      * lia.
    + replace (k + 0) with k by lia.
      rewrite Znth_replace_Znth_Diff by lia.
      pose proof
        (f_equal (fun xs => Znth k xs 0) PreH18) as Heq.
      cbn in Heq.
      change
        (Znth k (sublist 0 j Words_3) 0 =
         Znth k
           (sublist 0 j
             (sm3_block_words
               (sublist (64 * BlockIndex) (64 * BlockIndex + 64) Blocks))) 0)
        in Heq.
      rewrite !Znth_sublist in Heq by lia.
      replace (k + 0) with k in Heq by lia.
      exact Heq.
Qed.

Lemma proof_of_sm3_compress_entail_wit_4_split_goal_2 : sm3_compress_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH17.
Qed.

Lemma proof_of_sm3_compress_entail_wit_4 : sm3_compress_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm3_compress_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_sm3_compress_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_sm3_compress_entail_wit_5_split_goal_1 : sm3_compress_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj : j = 16) by lia.
  rewrite Hj in PreH25.
  rewrite PreH25.
  apply (proj2 (list_eq_ext _ _ 0)).
  split.
  - rewrite !Zlength_sublist by
      (rewrite ?sm3_block_words_length, ?sm3_expand_words_length; lia).
    lia.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by
      (rewrite sm3_block_words_length; lia).
    rewrite !Znth_sublist by lia.
    replace (0 + k) with k by lia.
    rewrite sm3_block_words_Znth by lia.
    rewrite sm3_expand_words_initial by lia.
    reflexivity.
Qed.

Lemma proof_of_sm3_compress_entail_wit_5 : sm3_compress_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sm3_compress_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_sm3_compress_entail_wit_6_split_goal_1 : sm3_compress_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (proj2 (list_eq_ext _ _ 0)).
  split.
  - rewrite !Zlength_sublist by
      (rewrite ?Zlength_replace_Znth, ?sm3_expand_words_length; lia).
    lia.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by
      (rewrite Zlength_replace_Znth; lia).
    rewrite !Znth_sublist by lia.
    replace (0 + k) with k by lia.
    assert (Hprefix : forall idx,
      0 <= idx < j_2 ->
      Znth idx Words_4 0 =
      Znth idx
        (sm3_expand_words
          (sublist (64 * i_2) (64 * i_2 + 64) Blocks)) 0).
    {
      intros idx Hidx.
      pose proof
        (f_equal (fun xs => Znth idx xs 0) PreH18) as Heq.
      change
        (Znth idx (sublist 0 j_2 Words_4) 0 =
         Znth idx
           (sublist 0 j_2
             (sm3_expand_words
               (sublist (64 * i_2) (64 * i_2 + 64) Blocks))) 0)
        in Heq.
      rewrite !Znth_sublist in Heq by lia.
      replace (idx + 0) with idx in Heq by lia.
      exact Heq.
    }
    destruct (Z.eq_dec k j_2) as [-> | Hneq].
    + replace (j_2 + 0) with j_2 by lia.
      rewrite Znth_replace_Znth_Same by lia.
      change
        (sm3_expand_word Words_4 j_2 =
         Znth j_2
           (sm3_expand_words
             (sublist (64 * i_2) (64 * i_2 + 64) Blocks)) 0).
      rewrite sm3_expand_words_recurrence by lia.
      unfold sm3_expand_word.
      repeat rewrite Hprefix by lia.
      reflexivity.
    + replace (k + 0) with k by lia.
      rewrite Znth_replace_Znth_Diff by lia.
      apply Hprefix.
      lia.
Qed.

Lemma proof_of_sm3_compress_entail_wit_6_split_goal_2 : sm3_compress_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH17.
Qed.

Lemma proof_of_sm3_compress_entail_wit_6 : sm3_compress_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm3_compress_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_sm3_compress_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_sm3_compress_entail_wit_7_split_goal_1 : sm3_compress_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (HWords : Words_4 = sm3_expand_words
      (sublist (64 * i) (64 * i + 64) Blocks)).
  { replace j_2 with 68 in PreH34 by lia.
    rewrite <- (sublist_self Words_4 68 (eq_sym PreH33)), PreH34.
    apply sublist_self. reflexivity. }
  rewrite (sublist_split 0 (64 * (i + 1)) (64 * i) Blocks) by lia.
  replace (64 * (i + 1)) with (64 * i + 64) by ring.
  rewrite sm3_compress_bytes_app.
  2: rewrite Zlength_sublist by lia; replace (64 * i - 0) with (i * 64) by ring; apply Z.mod_mul; lia.
  rewrite <- PreH25, sm3_compress_bytes_one_block.
  2: rewrite Zlength_sublist by lia; nia.
  assert (Hchunks : forall (n m : nat) r words state,
    sm3_rounds_aux (n + m) r words state =
    sm3_rounds_aux m (r + Z.of_nat n) words
      (sm3_rounds_aux n r words state)).
  { intros n; induction n as [|n IH]; intros m r words state.
    - cbn [sm3_rounds_aux]. rewrite Nat2Z.inj_0. f_equal. lia.
    - change (sm3_rounds_aux (n + m) (r + 1) words
        (sm3_round r words state) =
        sm3_rounds_aux m (r + Z.of_nat (S n)) words
          (sm3_rounds_aux n (r + 1) words (sm3_round r words state))).
      rewrite (IH m (r + 1) words (sm3_round r words state)), Nat2Z.inj_succ.
      replace (r + 1 + Z.of_nat n) with (r + (Z.of_nat n + 1)) by lia.
      reflexivity. }
  assert (Hrounds : sm3_rounds Words_4 CurState_2 =
    ao :: bo :: co :: dout :: eo :: fo :: go :: ho :: nil).
  { unfold sm3_rounds.
    change (Z.to_nat 4) with (4%nat) in PreH1, PreH2, PreH3, PreH4,
      PreH5, PreH6, PreH7, PreH8, PreH9, PreH10, PreH11, PreH12,
      PreH13, PreH14, PreH15, PreH16.
    change (sm3_rounds_aux ((4 + 60)%nat) 0 Words_4 CurState_2 =
      ao :: bo :: co :: dout :: eo :: fo :: go :: ho :: nil).
    rewrite <- PreH28.
    rewrite (Hchunks (4%nat) (60%nat) 0 Words_4
      (A_3 :: B_3 :: C_3 :: D_3 :: E_3 :: F_3 :: G_3 :: H_3 :: nil)), <- PreH16.
    rewrite (Hchunks (4%nat) (56%nat) 4 Words_4 _), <- PreH15.
    rewrite (Hchunks (4%nat) (52%nat) 8 Words_4 _), <- PreH14.
    rewrite (Hchunks (4%nat) (48%nat) 12 Words_4 _), <- PreH13.
    rewrite (Hchunks (4%nat) (44%nat) 16 Words_4 _), <- PreH12.
    rewrite (Hchunks (4%nat) (40%nat) 20 Words_4 _), <- PreH11.
    rewrite (Hchunks (4%nat) (36%nat) 24 Words_4 _), <- PreH10.
    rewrite (Hchunks (4%nat) (32%nat) 28 Words_4 _), <- PreH9.
    rewrite (Hchunks (4%nat) (28%nat) 32 Words_4 _), <- PreH8.
    rewrite (Hchunks (4%nat) (24%nat) 36 Words_4 _), <- PreH7.
    rewrite (Hchunks (4%nat) (20%nat) 40 Words_4 _), <- PreH6.
    rewrite (Hchunks (4%nat) (16%nat) 44 Words_4 _), <- PreH5.
    rewrite (Hchunks (4%nat) (12%nat) 48 Words_4 _), <- PreH4.
    rewrite (Hchunks (4%nat) (8%nat) 52 Words_4 _), <- PreH3.
    rewrite (Hchunks (4%nat) (4%nat) 56 Words_4 _), <- PreH2.
    exact (eq_sym PreH1). }
  unfold sm3_compress_block.
  rewrite <- HWords, Hrounds, <- PreH28.
  cbn [Znth replace_Znth sm3_state_xor]. reflexivity.
Qed.

Lemma proof_of_sm3_compress_entail_wit_7_split_goal_2 : sm3_compress_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (sm3_compress_bytes_valid State
    (sublist 0 (64 * (i + 1)) Blocks) (conj PreH68 PreH69)) as Hvalid.
  exact (proj2 Hvalid).
Qed.

Lemma proof_of_sm3_compress_entail_wit_7_split_goal_3 : sm3_compress_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (sm3_compress_bytes_valid State
    (sublist 0 (64 * (i + 1)) Blocks) (conj PreH68 PreH69)) as Hvalid.
  exact (proj1 Hvalid).
Qed.

Lemma proof_of_sm3_compress_entail_wit_7_split_goal_4 : sm3_compress_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst pblock_2.
  subst block.
  rewrite sizeof_uchar, sizeof_uint.
  lia.
Qed.

Lemma proof_of_sm3_compress_entail_wit_7_split_goal_5 : sm3_compress_entail_wit_7_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (HWords : Words_4 = sm3_expand_words
      (sublist (64 * i) (64 * i + 64) Blocks)).
  { replace j_2 with 68 in PreH34 by lia.
    rewrite <- (sublist_self Words_4 68 (eq_sym PreH33)), PreH34.
    apply sublist_self. reflexivity. }
  rewrite (sublist_split 0 (64 * (i + 1)) (64 * i) Blocks) by lia.
  replace (64 * (i + 1)) with (64 * i + 64) by ring.
  rewrite sm3_compress_bytes_app.
  2: rewrite Zlength_sublist by lia; replace (64 * i - 0) with (i * 64) by ring; apply Z.mod_mul; lia.
  rewrite <- PreH25, sm3_compress_bytes_one_block.
  2: rewrite Zlength_sublist by lia; nia.
  assert (Hchunks : forall (n m : nat) r words state,
    sm3_rounds_aux (n + m) r words state =
    sm3_rounds_aux m (r + Z.of_nat n) words
      (sm3_rounds_aux n r words state)).
  { intros n; induction n as [|n IH]; intros m r words state.
    - cbn [sm3_rounds_aux]. rewrite Nat2Z.inj_0. f_equal. lia.
    - change (sm3_rounds_aux (n + m) (r + 1) words
        (sm3_round r words state) =
        sm3_rounds_aux m (r + Z.of_nat (S n)) words
          (sm3_rounds_aux n (r + 1) words (sm3_round r words state))).
      rewrite (IH m (r + 1) words (sm3_round r words state)), Nat2Z.inj_succ.
      replace (r + 1 + Z.of_nat n) with (r + (Z.of_nat n + 1)) by lia.
      reflexivity. }
  assert (Hrounds : sm3_rounds Words_4 CurState_2 =
    ao :: bo :: co :: dout :: eo :: fo :: go :: ho :: nil).
  { unfold sm3_rounds.
    change (Z.to_nat 4) with (4%nat) in PreH1, PreH2, PreH3, PreH4,
      PreH5, PreH6, PreH7, PreH8, PreH9, PreH10, PreH11, PreH12,
      PreH13, PreH14, PreH15, PreH16.
    change (sm3_rounds_aux ((4 + 60)%nat) 0 Words_4 CurState_2 =
      ao :: bo :: co :: dout :: eo :: fo :: go :: ho :: nil).
    rewrite <- PreH28.
    rewrite (Hchunks (4%nat) (60%nat) 0 Words_4
      (A_3 :: B_3 :: C_3 :: D_3 :: E_3 :: F_3 :: G_3 :: H_3 :: nil)), <- PreH16.
    rewrite (Hchunks (4%nat) (56%nat) 4 Words_4 _), <- PreH15.
    rewrite (Hchunks (4%nat) (52%nat) 8 Words_4 _), <- PreH14.
    rewrite (Hchunks (4%nat) (48%nat) 12 Words_4 _), <- PreH13.
    rewrite (Hchunks (4%nat) (44%nat) 16 Words_4 _), <- PreH12.
    rewrite (Hchunks (4%nat) (40%nat) 20 Words_4 _), <- PreH11.
    rewrite (Hchunks (4%nat) (36%nat) 24 Words_4 _), <- PreH10.
    rewrite (Hchunks (4%nat) (32%nat) 28 Words_4 _), <- PreH9.
    rewrite (Hchunks (4%nat) (28%nat) 32 Words_4 _), <- PreH8.
    rewrite (Hchunks (4%nat) (24%nat) 36 Words_4 _), <- PreH7.
    rewrite (Hchunks (4%nat) (20%nat) 40 Words_4 _), <- PreH6.
    rewrite (Hchunks (4%nat) (16%nat) 44 Words_4 _), <- PreH5.
    rewrite (Hchunks (4%nat) (12%nat) 48 Words_4 _), <- PreH4.
    rewrite (Hchunks (4%nat) (8%nat) 52 Words_4 _), <- PreH3.
    rewrite (Hchunks (4%nat) (4%nat) 56 Words_4 _), <- PreH2.
    exact (eq_sym PreH1). }
  unfold sm3_compress_block.
  rewrite <- HWords, Hrounds, <- PreH28.
  cbn [Znth replace_Znth sm3_state_xor]. reflexivity.
Qed.

Lemma proof_of_sm3_compress_entail_wit_7 : sm3_compress_entail_wit_7.
Proof.
  aggressive_pre_process.
  - repeat match goal with H : _ |- _ => revert H end.
    change sm3_compress_entail_wit_7_split_goal_1.
    exact proof_of_sm3_compress_entail_wit_7_split_goal_1.
  - repeat match goal with H : _ |- _ => revert H end.
    change sm3_compress_entail_wit_7_split_goal_2.
    exact proof_of_sm3_compress_entail_wit_7_split_goal_2.
  - repeat match goal with H : _ |- _ => revert H end.
    change sm3_compress_entail_wit_7_split_goal_3.
    exact proof_of_sm3_compress_entail_wit_7_split_goal_3.
  - repeat match goal with H : _ |- _ => revert H end.
    change sm3_compress_entail_wit_7_split_goal_4.
    exact proof_of_sm3_compress_entail_wit_7_split_goal_4.
  - repeat match goal with H : _ |- _ => revert H end.
    change sm3_compress_entail_wit_7_split_goal_5.
    exact proof_of_sm3_compress_entail_wit_7_split_goal_5.
Qed.

Lemma proof_of_sm3_compress_return_wit_1_split_goal_1 : sm3_compress_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (i = nblocks_pre) by lia.
  subst i.
  pose proof (sm3_compress_bytes_valid State Blocks (conj PreH8 PreH9)) as Hvalid.
  exact (proj1 Hvalid).
Qed.

Lemma proof_of_sm3_compress_return_wit_1_split_goal_2 : sm3_compress_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (sm3_compress_bytes_valid State Blocks (conj PreH8 PreH9)) as Hvalid.
  exact (proj2 Hvalid).
Qed.

Lemma proof_of_sm3_compress_return_wit_1_split_goal_3 : sm3_compress_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (i = nblocks_pre) by lia.
  subst i.
  rewrite sublist_self in PreH5 by lia.
  exact PreH5.
Qed.

Lemma proof_of_sm3_compress_return_wit_1_split_goal_spatial : sm3_compress_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_sm3_ti, store_u32_words.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    split; assumption.
Qed.

Lemma proof_of_sm3_compress_return_wit_1 : sm3_compress_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm3_compress_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_sm3_compress_return_wit_1_split_goal_1.
  - Goal_apply proof_of_sm3_compress_return_wit_1_split_goal_2.
  - Goal_apply proof_of_sm3_compress_return_wit_1_split_goal_3.
Qed.

Lemma proof_of_sm3_compress_which_implies_wit_2_split_goal_1 : sm3_compress_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_sm3_ti.
  apply store_u32_words_bounded.
Qed.

Lemma proof_of_sm3_compress_which_implies_wit_2_split_goal_2 : sm3_compress_which_implies_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm3_compress_which_implies_wit_2_split_goal_spatial : sm3_compress_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm3_compress_which_implies_wit_2 : sm3_compress_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm3_compress_which_implies_wit_2_split_goal_spatial.
  - Goal_apply proof_of_sm3_compress_which_implies_wit_2_split_goal_1.
  - Goal_apply proof_of_sm3_compress_which_implies_wit_2_split_goal_2.
Qed.

Lemma proof_of_sm3_compress_which_implies_wit_3_split_goal_1 : sm3_compress_which_implies_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst pblock.
  specialize (PreH1 ltac:(lia)).
  unfold aligned_4 in *.
  rewrite sizeof_uchar.
  replace (64 * i * 1) with (4 * (16 * i)) by ring.
  rewrite Z.add_mod by lia.
  rewrite Z.mul_mod by lia.
  rewrite PreH1.
  reflexivity.
Qed.

Lemma proof_of_sm3_compress_which_implies_wit_3_split_goal_spatial : sm3_compress_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (UCharArray.full_split_to_full
      block_pre (64 * i) (64 * nblocks_pre) Blocks ltac:(lia)).
  sep_apply_l_atomic
    (UCharArray.full_split_to_full
      (block_pre + 64 * i * sizeof(UCHAR))
      64 (64 * nblocks_pre - 64 * i)
      (sublist (64 * i) (64 * nblocks_pre) Blocks) ltac:(lia)).
  rewrite !sizeof_uchar in *.
  rewrite !Zsublist_Zsublist by lia.
  replace (0 + 64 * i) with (64 * i) by lia.
  replace (64 + 64 * i) with (64 * i + 64) by lia.
  replace (64 * nblocks_pre - 64 * i + 64 * i) with
    (64 * nblocks_pre) by lia.
  cancel.
  replace (block_pre + 64 * i * 1 + 64 * 1) with
    (block_pre + (64 * i + 64) * 1) by ring.
  cancel.
Qed.

Lemma proof_of_sm3_compress_which_implies_wit_3 : sm3_compress_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm3_compress_which_implies_wit_3_split_goal_spatial.
  - Goal_apply proof_of_sm3_compress_which_implies_wit_3_split_goal_1.
Qed.

Lemma proof_of_sm3_compress_which_implies_wit_4_split_goal_spatial : sm3_compress_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite !sizeof_uchar in *.
  pose proof
    (UCharArray.full_merge_to_full
      block_pre (64 * BlockIndex) (64 * BlockIndex + 64)
      (sublist 0 (64 * BlockIndex) Blocks)
      (sublist (64 * BlockIndex) (64 * BlockIndex + 64) Blocks)
      ltac:(lia)) as Hmerge_prefix.
  rewrite sizeof_uchar in Hmerge_prefix.
  replace (64 * BlockIndex + 64 - 64 * BlockIndex) with 64
    in Hmerge_prefix by lia.
  sep_apply Hmerge_prefix.
  replace
    (sublist 0 (64 * BlockIndex) Blocks ++
     sublist (64 * BlockIndex) (64 * BlockIndex + 64) Blocks) with
    (sublist 0 (64 * BlockIndex + 64) Blocks).
  2: { rewrite (sublist_split 0 (64 * BlockIndex + 64)
                  (64 * BlockIndex) Blocks) by lia.
       reflexivity. }
  pose proof
    (UCharArray.full_merge_to_full
      block_pre (64 * BlockIndex + 64) (64 * nblocks_pre)
      (sublist 0 (64 * BlockIndex + 64) Blocks)
      (sublist (64 * BlockIndex + 64) (64 * nblocks_pre) Blocks)
      ltac:(lia)) as Hmerge_all.
  rewrite sizeof_uchar in Hmerge_all.
  replace (64 * nblocks_pre - (64 * BlockIndex + 64)) with
    (64 * nblocks_pre - 64 * BlockIndex - 64) in Hmerge_all by lia.
  sep_apply Hmerge_all.
  replace
    (sublist 0 (64 * BlockIndex + 64) Blocks ++
     sublist (64 * BlockIndex + 64) (64 * nblocks_pre) Blocks) with Blocks.
  2: { assert (Hwhole : sublist 0 (64 * nblocks_pre) Blocks = Blocks).
       { rewrite <- PreH3.
         apply sublist_self.
         reflexivity. }
       rewrite (sublist_split 0 (64 * nblocks_pre)
                  (64 * BlockIndex + 64) Blocks) in Hwhole by lia.
       symmetry.
       exact Hwhole. }
  cancel.
Qed.

Lemma proof_of_sm3_compress_which_implies_wit_4 : sm3_compress_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm3_compress_which_implies_wit_4_split_goal_spatial.
Qed.
