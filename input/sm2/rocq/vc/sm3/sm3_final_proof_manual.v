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
From SimpleC.EE.Applications_human.sm2.vc.sm3 Require Import sm3_final_goal.
From SimpleC.EE.Applications_human.sm2.vc.sm3 Require Import sm3_final_proof_auto.
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
      SimpleC.EE.Applications_human.sm2.lib.sm3_final_lib.
Local Open Scope sac.

Lemma proof_of_sm3_final_entail_wit_4_split_goal_1 : sm3_final_entail_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_4_split_goal_spatial : sm3_final_entail_wit_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_4 : sm3_final_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (sm3_compress_bytes SM3_IV (sm3_full_bytes Message)).
  Exists (sm3_tail Message).
  pose proof (sm3_tail_length_range Message) as Htailrange.
  split_pure_spatial.
  - sep_apply_l_atomic
      (UCharArray.undef_full_to_undef_seg
         (&( ctx_pre # "_SM3_CTX" ->ₛ "block") +
          Zlength (sm3_tail Message))
         (64 - Zlength (sm3_tail Message))).
    pose proof (UCharArray.undef_seg_0_shift
      &(ctx_pre # "_SM3_CTX" ->ₛ "block")
      (Zlength (sm3_tail Message)) 64) as Hshift.
    rewrite sizeof_uchar in Hshift.
    replace
      (&(ctx_pre # "_SM3_CTX" ->ₛ "block") +
        Zlength (sm3_tail Message) * 1)
      with
      (&(ctx_pre # "_SM3_CTX" ->ₛ "block") +
        Zlength (sm3_tail Message)) in Hshift by lia.
    rewrite <- Hshift.
    normalize.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_sm3_final_entail_wit_5_split_goal_spatial : sm3_final_entail_wit_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_5 : sm3_final_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists State_2 Tail_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (UCharArray.undef_seg_split_to_undef_seg
        (&( ctx_pre # "_SM3_CTX" ->ₛ "block"))
        (Zlength Tail_2 + 1) 56 64 ltac:(lia)).
    sep_apply_l_atomic
      (UCharArray.undef_seg_to_undef_full
        (&( ctx_pre # "_SM3_CTX" ->ₛ "block"))
        (Zlength Tail_2 + 1) 56).
    sep_apply_l_atomic
      (UCharArray.undef_seg_to_undef_full
        (&( ctx_pre # "_SM3_CTX" ->ₛ "block")) 56 64).
    normalize.
    replace (56 - (Zlength Tail_2 + 1)) with (55 - Zlength Tail_2) by lia.
    replace (64 - 56) with 8 by lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_sm3_final_entail_wit_8_split_goal_spatial : sm3_final_entail_wit_8_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_8 : sm3_final_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists State_2 Tail_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (UCharArray.undef_seg_to_undef_full
        (&( ctx_pre # "_SM3_CTX" ->ₛ "block"))
        (Zlength Tail_2 + 1) 64).
    normalize.
    replace (64 - (Zlength Tail_2 + 1)) with (63 - Zlength Tail_2) by lia.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_sm3_final_entail_wit_10_split_goal_1 : sm3_final_entail_wit_10_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_10_split_goal_2 : sm3_final_entail_wit_10_split_goal_2.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_10_split_goal_3 : sm3_final_entail_wit_10_split_goal_3.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_10_split_goal_spatial : sm3_final_entail_wit_10_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_10 : sm3_final_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists State_2
    (Tail_2 ++ ((128 :: nil) ++ repeat_Z 0 (63 - Zlength Tail_2)))
    Tail_2.
  replace (unsigned_last_nbits 0 8) with 0 in * by reflexivity.
  replace (64 - Zlength Tail_2 - 1) with (63 - Zlength Tail_2) in * by lia.
  assert (Htail_bounded : u8_list_bounded Tail_2).
  { rewrite PreH6. apply sm3_tail_bounded. exact PreH4. }
  assert (Hbyte128 : u8_list_bounded (128 :: nil)).
  { unfold u8_list_bounded.
    rewrite limb_list_bounded_cons_iff.
    split.
    - unfold SM2_BYTE_BASE. lia.
    - unfold limb_list_bounded. intros j Hj. rewrite Zlength_nil in Hj. lia. }
  assert (Hzero_bounded : u8_list_bounded (repeat_Z 0 (63 - Zlength Tail_2))).
  { exact PreH1. }
  assert (Hblock_bounded :
    u8_list_bounded
      (Tail_2 ++ ((128 :: nil) ++ repeat_Z 0 (63 - Zlength Tail_2)))).
  { unfold u8_list_bounded.
    apply (proj2 (limb_list_bounded_app SM2_BYTE_BASE
      Tail_2 ((128 :: nil) ++ repeat_Z 0 (63 - Zlength Tail_2)))).
    split.
    - exact Htail_bounded.
    - apply (proj2 (limb_list_bounded_app SM2_BYTE_BASE
        (128 :: nil) (repeat_Z 0 (63 - Zlength Tail_2)))).
      tauto. }
  assert (Hblock_len :
    Zlength (Tail_2 ++ ((128 :: nil) ++ repeat_Z 0 (63 - Zlength Tail_2))) = 64).
  { rewrite !Zlength_app, Zlength_cons, Zlength_nil, PreH2. lia. }
  replace (63 - Zlength Tail_2) with (64 - (Zlength Tail_2 + 1)) in * by lia.
  assert (Hmerge :
    UCharArray.full
      (&( ctx_pre # "_SM3_CTX" ->ₛ "block") +
        (Zlength Tail_2 + 1) * sizeof(UCHAR))
      (64 - (Zlength Tail_2 + 1))
      (repeat_Z 0 (64 - (Zlength Tail_2 + 1))) **
    UCharArray.full
      (&( ctx_pre # "_SM3_CTX" ->ₛ "block"))
      (Zlength Tail_2 + 1) (Tail_2 +:: 128)
    |--
    UCharArray.full
      (&( ctx_pre # "_SM3_CTX" ->ₛ "block")) 64
      ((Tail_2 +:: 128) ++ repeat_Z 0 (64 - (Zlength Tail_2 + 1)))).
  { apply uchar_full_merge_swapped. lia. }
  assert (Hcompress_align :
    sm3_compress_input_aligned
      (&( ctx_pre # "_SM3_CTX" ->ₛ "block")) 1).
  { unfold sm3_compress_input_aligned. right. exact PreH13. }
  split_pure_spatial.
  - cancel (store_u32_words &( ctx_pre # "_SM3_CTX" ->ₛ "digest") 8 State_2).
    cancel (&( ctx_pre # "_SM3_CTX" ->ₛ "nblocks") # UInt64 |-> (Zlength Message ÷ 64)).
    cancel (&( ctx_pre # "_SM3_CTX" ->ₛ "num") # UInt64 |-> Zlength Tail_2).
    cancel (UCharArray.undef_full digest_pre 32).
    cancel store_sm3_ti.
    sep_apply Hmerge.
    rewrite app_assoc.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_sm3_final_entail_wit_13_split_goal_1 : sm3_final_entail_wit_13_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_13_split_goal_2 : sm3_final_entail_wit_13_split_goal_2.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_13_split_goal_3 : sm3_final_entail_wit_13_split_goal_3.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_13_split_goal_4 : sm3_final_entail_wit_13_split_goal_4.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_13_split_goal_spatial : sm3_final_entail_wit_13_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_13 : sm3_final_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (sm3_final_long_padding_view Message Tail_2 PreH7 ltac:(lia)) as
    [Hfinal [Hfirst_len [Hfinal_len [Hfirst_block Hmiddle56]]]].
  assert (Hblock_prefix :
    BlockBytes_2 =
      sublist 0 (Zlength (sm3_final_bytes Message) - 64)
        (sm3_final_bytes Message)).
  { rewrite PreH10, app_assoc. exact Hfirst_block. }
  Exists
    (sm3_compress_bytes SM3_IV
      (app (sm3_full_bytes Message) BlockBytes_2))
    BlockBytes_2 Tail_2.
  split_pure_spatial.
  - replace
      (&(ctx_pre # "_SM3_CTX" ->ₛ "digest") + 0 * sizeof(UINT))
      with (&(ctx_pre # "_SM3_CTX" ->ₛ "digest")) by lia.
    replace
      (&(ctx_pre # "_SM3_CTX" ->ₛ "block") + 0 * sizeof(UCHAR))
      with (&(ctx_pre # "_SM3_CTX" ->ₛ "block")) by lia.
    rewrite PreH16.
    rewrite sm3_compress_bytes_app.
    replace (64 * 1) with 64 by lia.
    sep_apply_l_atomic
      (UCharArray.full_split_to_full
        (&(ctx_pre # "_SM3_CTX" ->ₛ "block")) 56 64 BlockBytes_2
        ltac:(lia)).
    sep_apply_l_atomic
      (UCharArray.full_to_undef_full
        (&(ctx_pre # "_SM3_CTX" ->ₛ "block")) 56
        (sublist 0 56 BlockBytes_2)).
    replace
      (&(ctx_pre # "_SM3_CTX" ->ₛ "block") +
        (Zlength Tail_2 - Zlength Tail_2) * sizeof(UCHAR))
      with (&(ctx_pre # "_SM3_CTX" ->ₛ "block")) by lia.
    replace (64 - 56) with 8 by lia.
    cancel.
    exact (sm3_full_bytes_length_multiple Message).
  - split_pures; dump_pre_spatial; try reflexivity; try assumption.
Qed.

Lemma proof_of_sm3_final_entail_wit_16_1_split_goal_1 : sm3_final_entail_wit_16_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_16_1_split_goal_2 : sm3_final_entail_wit_16_1_split_goal_2.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_16_1_split_goal_3 : sm3_final_entail_wit_16_1_split_goal_3.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_16_1_split_goal_4 : sm3_final_entail_wit_16_1_split_goal_4.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_16_1_split_goal_spatial : sm3_final_entail_wit_16_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_16_1 : sm3_final_entail_wit_16_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists State_2.
  Exists ((Tail_2 +:: 128) ++
          repeat_Z (unsigned_last_nbits 0 8) (64 - Zlength Tail_2 - 9)).
  Exists Tail_2.
  assert (Hcount_align : aligned_4 count).
  { rewrite PreH11.
    unfold aligned_4 in *.
    rewrite sizeof_uchar.
    rewrite Z.add_mod by lia.
    rewrite PreH13.
    reflexivity. }
  assert (Htail_mod : Zlength Tail_2 = Zlength Message mod 64).
  { rewrite PreH6. apply sm3_tail_length. }
  assert (Hzero :
    sm3_padding_zero_count (Zlength Message) = 55 - Zlength Tail_2).
  { unfold sm3_padding_zero_count.
    pose proof (Z.div_mod (Zlength Message) 64 ltac:(lia)) as Hdivmod.
    symmetry.
    apply Z.mod_unique with (q := -(Zlength Message / 64)); lia. }
  assert (Hzero_byte : unsigned_last_nbits 0 8 = 0) by reflexivity.
  assert (Hfinal_short :
    sm3_final_bytes Message =
      (((Tail_2 +:: 128) ++
        repeat_Z (unsigned_last_nbits 0 8) (64 - Zlength Tail_2 - 9)) ++
       u64_to_be_bytes (8 * Zlength Message))).
  { unfold sm3_final_bytes, repeat_Z.
    rewrite <- PreH6, Hzero, Hzero_byte.
    replace (64 - Zlength Tail_2 - 9) with (55 - Zlength Tail_2) by lia.
    rewrite !app_assoc.
    reflexivity. }
  assert (Hprefix_len :
    Zlength
      ((Tail_2 +:: 128) ++
       repeat_Z (unsigned_last_nbits 0 8) (64 - Zlength Tail_2 - 9)) = 56).
  { rewrite !Zlength_app, PreH2.
    simpl.
    change (Zlength Tail_2 + 1 + (64 - Zlength Tail_2 - 9) = 56).
    lia. }
  split_pure_spatial.
  - cancel (&(ctx_pre # "_SM3_CTX" ->ₛ "nblocks") # UInt64 |-> (Zlength Message ÷ 64)).
    cancel (&(ctx_pre # "_SM3_CTX" ->ₛ "num") # UInt64 |-> Zlength Tail_2).
    cancel (UCharArray.undef_full digest_pre 32).
    cancel store_sm3_ti.
    replace (64 - Zlength Tail_2 - 9) with (56 - (Zlength Tail_2 + 1)) by lia.
    rewrite <- PreH11.
    assert (Hcount_view :
      UCharArray.undef_full count 8 |-- UIntArray.undef_full count 2).
    { intros m Hundef.
      apply (uchar_undef_full8_to_uint_undef_full2 count Hcount_align).
      exact Hundef. }
    sep_apply_l_atomic Hcount_view.
    assert (Hmerge_range : 0 <= Zlength Tail_2 + 1 <= 56) by lia.
    cancel (store_u32_words &(ctx_pre # "_SM3_CTX" ->ₛ "digest") 8 State_2).
    cancel (UIntArray.undef_full count 2).
    exact
      (uchar_full_merge_swapped
         &(ctx_pre # "_SM3_CTX" ->ₛ "block")
         (Zlength Tail_2 + 1) 56
         (Tail_2 +:: 128)
         (repeat_Z (unsigned_last_nbits 0 8) (56 - (Zlength Tail_2 + 1)))
         Hmerge_range).
  - assert (Hprefix_resource :
      UCharArray.full &(ctx_pre # "_SM3_CTX" ->ₛ "block")
        (Zlength Tail_2 + 1) (Tail_2 +:: 128) |--
      “ u8_list_bounded (Tail_2 +:: 128) ” &&
      UCharArray.full &(ctx_pre # "_SM3_CTX" ->ₛ "block")
        (Zlength Tail_2 + 1) (Tail_2 +:: 128)).
    { intros m Hfull.
      split.
      - apply (uchar_full_values_bounded
                 &(ctx_pre # "_SM3_CTX" ->ₛ "block")
                 (Zlength Tail_2 + 1) (Tail_2 +:: 128)); exact Hfull.
      - exact Hfull. }
    sep_apply_l_atomic Hprefix_resource.
    Intros_p Hprefix_bound.
    split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; lia).
    + dump_pre_spatial.
      unfold u8_list_bounded in *.
      rewrite limb_list_bounded_app.
      tauto.
    + dump_pre_spatial.
      rewrite Hfinal_short.
      rewrite (Zlength_app
        ((Tail_2 +:: 128) ++
         repeat_Z (unsigned_last_nbits 0 8) (64 - Zlength Tail_2 - 9))
        (u64_to_be_bytes (8 * Zlength Message))).
      rewrite Hprefix_len, u64_to_be_bytes_length.
      replace (56 + 8 - 64) with 0 by lia.
      replace (56 + 8 - 8) with 56 by lia.
      replace 56 with
        (Zlength
          ((Tail_2 +:: 128) ++
           repeat_Z (unsigned_last_nbits 0 8) (64 - Zlength Tail_2 - 9)))
        by exact Hprefix_len.
      rewrite sublist_app_exact1.
      reflexivity.
    + dump_pre_spatial.
      rewrite Hfinal_short.
      rewrite (Zlength_app
        ((Tail_2 +:: 128) ++
         repeat_Z (unsigned_last_nbits 0 8) (64 - Zlength Tail_2 - 9))
        (u64_to_be_bytes (8 * Zlength Message))).
      rewrite Hprefix_len, u64_to_be_bytes_length.
      replace (56 + 8 - 64) with 0 by lia.
      rewrite Zsublist_nil by lia.
      rewrite app_nil_r.
      exact PreH12.
Qed.

Lemma proof_of_sm3_final_entail_wit_16_2_split_goal_1 : sm3_final_entail_wit_16_2_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_16_2_split_goal_2 : sm3_final_entail_wit_16_2_split_goal_2.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_16_2_split_goal_3 : sm3_final_entail_wit_16_2_split_goal_3.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_16_2_split_goal_spatial : sm3_final_entail_wit_16_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_16_2 : sm3_final_entail_wit_16_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists State_2.
  Exists (repeat_Z (unsigned_last_nbits 0 8) (64 - 8)).
  Exists Tail_2.
  assert (Hcount_align : aligned_4 count).
  { rewrite PreH12.
    unfold aligned_4 in *.
    rewrite sizeof_uchar, Z.add_mod by lia.
    rewrite PreH16.
    reflexivity. }
  assert (Hzero_byte : unsigned_last_nbits 0 8 = 0) by reflexivity.
  pose proof
    (sm3_final_long_padding_view Message Tail_2 PreH6 ltac:(lia)) as
    [Hfinal_long [Hfirst_len [Hfinal_len [Hfirst_block Hmiddle56]]]].
  assert (Hblock :
    BlockBytes = (Tail_2 +:: 128) ++ repeat_Z 0 (63 - Zlength Tail_2)).
  { rewrite PreH9. symmetry. exact Hfirst_block. }
  assert (Hprefix :
    repeat_Z (unsigned_last_nbits 0 8) (64 - 8) =
    sublist (Zlength (sm3_final_bytes Message) - 64)
      (Zlength (sm3_final_bytes Message) - 8) (sm3_final_bytes Message)).
  { rewrite Hzero_byte. replace (64 - 8) with 56 by lia.
    exact Hmiddle56. }
  split_pure_spatial.
  - rewrite Hprefix.
    replace (&(ctx_pre # "_SM3_CTX" ->ₛ "block") + 0 * sizeof (UCHAR)) with
      &(ctx_pre # "_SM3_CTX" ->ₛ "block") by lia.
    assert (Hlast8 :
      UCharArray.full count 8 (sublist 56 64 BlockBytes) |--
      UIntArray.undef_full count 2).
    { intros m Hfull.
      apply (uchar_undef_full8_to_uint_undef_full2 count Hcount_align).
      apply (UCharArray.full_to_undef_full
        count 8 (sublist 56 64 BlockBytes)).
      exact Hfull. }
    rewrite PreH12 in Hlast8.
    sep_apply_l_atomic Hlast8.
    cancel.
    rewrite PreH12.
    replace (64 - 8) with 56 by lia.
    cancel.
  - split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; lia).
    dump_pre_spatial.
    rewrite <- PreH9.
    exact PreH15.
Qed.

Lemma proof_of_sm3_final_entail_wit_17_split_goal_1 : sm3_final_entail_wit_17_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_17_split_goal_2 : sm3_final_entail_wit_17_split_goal_2.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_17_split_goal_3 : sm3_final_entail_wit_17_split_goal_3.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_17_split_goal_spatial : sm3_final_entail_wit_17_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_17 : sm3_final_entail_wit_17.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (FinalBlock :=
    sublist (Zlength (sm3_final_bytes Message) - 64)
      (Zlength (sm3_final_bytes Message)) (sm3_final_bytes Message)).
  Exists State_2 FinalBlock Tail_2.
  assert (Hquot : Zlength Message ÷ 64 = Zlength Message / 64).
  { apply Z.quot_div_nonneg; pose proof (Zlength_nonneg Message); lia. }
  assert (Htail_mod : Zlength Tail_2 = Zlength Message mod 64).
  { rewrite PreH3; apply sm3_tail_length. }
  assert (Hlength_parts :
    Zlength Message = 64 * (Zlength Message ÷ 64) + Zlength Tail_2).
  { rewrite Hquot, Htail_mod.
    pose proof (Z.div_mod (Zlength Message) 64 ltac:(lia)); lia. }
  assert (Hbit_range : 0 <= 8 * Zlength Message < 2 ^ 64).
  { pose proof (Zlength_nonneg Message).
    change (Zlength Message < 2305843009213693952) in PreH2.
    change (0 <= 8 * Zlength Message < 18446744073709551616).
    lia. }
  set (encoded_bits :=
    unsigned_last_nbits
      (unsigned_last_nbits (Z.shiftl (Zlength Message ÷ 64) 9) 64 +
       unsigned_last_nbits (Z.shiftl (Zlength Tail_2) 3) 64) 64).
  assert (Hencoded_bits : encoded_bits = 8 * Zlength Message).
  { unfold encoded_bits.
    assert (Hq_nonneg : 0 <= Zlength Message ÷ 64).
    { rewrite Hquot; apply Z.div_pos; pose proof (Zlength_nonneg Message); lia. }
    assert (Hq_shift :
      Z.shiftl (Zlength Message ÷ 64) 9 =
      512 * (Zlength Message ÷ 64)).
    { rewrite Z.shiftl_mul_pow2 by lia.
      change ((Zlength Message ÷ 64) * 512 =
        512 * (Zlength Message ÷ 64)).
      apply Z.mul_comm. }
    assert (Htail_shift : Z.shiftl (Zlength Tail_2) 3 = 8 * Zlength Tail_2).
    { rewrite Z.shiftl_mul_pow2 by lia.
      change (Zlength Tail_2 * 8 = 8 * Zlength Tail_2).
      apply Z.mul_comm. }
    rewrite (unsigned_last_nbits_eq
      (Z.shiftl (Zlength Message ÷ 64) 9) 64) by
      (rewrite Hq_shift;
       change (0 <= 512 * (Zlength Message ÷ 64) < 18446744073709551616);
       lia).
    rewrite (unsigned_last_nbits_eq
      (Z.shiftl (Zlength Tail_2) 3) 64) by
      (rewrite Htail_shift;
       change (0 <= 8 * Zlength Tail_2 < 18446744073709551616);
       lia).
    rewrite unsigned_last_nbits_eq.
    - rewrite Hq_shift, Htail_shift; lia.
    - rewrite Hq_shift, Htail_shift.
      change
        (0 <= 512 * (Zlength Message ÷ 64) + 8 * Zlength Tail_2 <
          18446744073709551616).
      replace
        (512 * (Zlength Message ÷ 64) + 8 * Zlength Tail_2)
        with (8 * (64 * (Zlength Message ÷ 64) + Zlength Tail_2)) by lia.
      rewrite <- Hlength_parts.
      exact Hbit_range. }
  set (high_word := Z.shiftr (Zlength Message ÷ 64) 23).
  set (low_word := unsigned_last_nbits encoded_bits 32).
  pose proof (sm3_message_length_words_be8 Message PreH2) as Hlength_words.
  cbn zeta in Hlength_words.
  rewrite <- Hquot in Hlength_words.
  fold high_word in Hlength_words.
  rewrite <- Hencoded_bits in Hlength_words.
  fold low_word in Hlength_words.
  destruct Hlength_words as [Hhigh_range [Hlow_range Hbe_split]].
  rewrite Hencoded_bits in Hbe_split.
  assert (Hcount_align : aligned_4 count) by exact PreH13.
  assert (Hblock_align : aligned_4 &(ctx_pre # "_SM3_CTX" ->ₛ "block")).
  { unfold aligned_4 in *.
    rewrite PreH12 in Hcount_align.
    rewrite sizeof_uchar, Z.add_mod in Hcount_align by lia.
    change (56 mod 4) with 0 in Hcount_align.
    rewrite Z.add_0_r in Hcount_align.
    rewrite Z.mod_mod in Hcount_align by lia.
    exact Hcount_align. }
  assert (Hland_wrap : forall value,
    Z.land (Z.shiftl value 8) 16711680 =
    Z.land (unsigned_last_nbits (Z.shiftl value 8) 32) 16711680).
  { intros value.
    assert (Hmask : unsigned_last_nbits 16711680 32 = 16711680).
    { apply unsigned_last_nbits_eq.
      change (0 <= 16711680 < 4294967296). lia. }
    pose proof
      (unsigned_last_nbits_land_clear_l
        (Z.shiftl value 8) 16711680 32 ltac:(lia)) as Hclear.
    rewrite Hmask in Hclear.
    symmetry. exact Hclear. }
  assert (Hcpu_high :
    Z.lor
      (Z.lor
        (Z.lor
          (unsigned_last_nbits (Z.shiftr high_word 24) 32)
          (Z.land (Z.shiftr high_word 8) 65280))
        (Z.land (Z.shiftl high_word 8) 16711680))
      (unsigned_last_nbits (Z.shiftl high_word 24) 32) =
    byte_swap32 high_word).
  { assert (Htop :
      unsigned_last_nbits (Z.shiftr high_word 24) 32 =
      Z.shiftr high_word 24).
    { apply unsigned_last_nbits_eq.
      rewrite Z.shiftr_div_pow2 by lia.
      change (0 <= high_word / 16777216 < 4294967296).
      split.
      - apply Z.div_pos.
        + exact (proj1 Hhigh_range).
        + lia.
      - apply Z.div_lt_upper_bound.
        + lia.
        + pose proof (proj2 Hhigh_range).
          nia. }
    rewrite Htop, Hland_wrap.
    apply byte_swap32_frontend_equiv.
    exact Hhigh_range. }
  assert (Hraw_low :
    unsigned_last_nbits
      (unsigned_last_nbits (Z.shiftl (Zlength Message ÷ 64) 9) 64 +
       unsigned_last_nbits (Z.shiftl (Zlength Tail_2) 3) 64) 32 =
    low_word).
  { unfold low_word, encoded_bits.
    rewrite unsigned_revolutive_less by lia.
    reflexivity. }
  assert (Hcpu_low :
    Z.lor
      (Z.lor
        (Z.lor
          (Z.shiftr
            (unsigned_last_nbits
              (unsigned_last_nbits (Z.shiftl (Zlength Message ÷ 64) 9) 64 +
               unsigned_last_nbits (Z.shiftl (Zlength Tail_2) 3) 64) 32) 24)
          (Z.land
            (Z.shiftr
              (unsigned_last_nbits
                (unsigned_last_nbits (Z.shiftl (Zlength Message ÷ 64) 9) 64 +
                 unsigned_last_nbits (Z.shiftl (Zlength Tail_2) 3) 64) 32) 8)
            65280))
        (Z.land
          (Z.shiftl
            (unsigned_last_nbits
              (unsigned_last_nbits (Z.shiftl (Zlength Message ÷ 64) 9) 64 +
               unsigned_last_nbits (Z.shiftl (Zlength Tail_2) 3) 64) 32) 8)
          16711680))
      (unsigned_last_nbits
        (Z.shiftl
          (unsigned_last_nbits
            (unsigned_last_nbits (Z.shiftl (Zlength Message ÷ 64) 9) 64 +
             unsigned_last_nbits (Z.shiftl (Zlength Tail_2) 3) 64) 32) 24) 32) =
    byte_swap32 low_word).
  { rewrite !Hraw_low, Hland_wrap.
    apply byte_swap32_frontend_equiv.
    exact Hlow_range. }
  pose proof (sm3_padding_zero_count_range (Zlength Message)) as Hpad_range.
  pose proof
    (sm3_final_bytes_length_at_least_block Message) as Hfinal_ge64.
  assert (Hprefix_part :
    sublist (Zlength (sm3_final_bytes Message) - 64)
      (Zlength (sm3_final_bytes Message) - 8) (sm3_final_bytes Message) =
    Prefix56).
  { symmetry; exact PreH8. }
  assert (Hfinal_suffix :
    sublist (Zlength (sm3_final_bytes Message) - 8)
      (Zlength (sm3_final_bytes Message)) (sm3_final_bytes Message) =
    u64_to_be_bytes (8 * Zlength Message)).
  { apply sm3_final_bytes_last_eight. }
  assert (Hfinal_block : FinalBlock =
    Prefix56 ++ u64_to_be_bytes (8 * Zlength Message)).
  { unfold FinalBlock.
    rewrite (sublist_split
      (Zlength (sm3_final_bytes Message) - 64)
      (Zlength (sm3_final_bytes Message))
      (Zlength (sm3_final_bytes Message) - 8)) by lia.
    rewrite Hprefix_part, Hfinal_suffix.
    reflexivity. }
  assert (Hfinal_len : Zlength FinalBlock = 64).
  { unfold FinalBlock.
    rewrite Zlength_sublist by lia.
    lia. }
  assert (Hfinal_bounded : u8_list_bounded FinalBlock).
  { unfold FinalBlock, u8_list_bounded.
    apply limb_list_bounded_sublist.
    - apply sm3_final_bytes_bounded. exact PreH1.
    - lia. }
  assert (Hcompress_align :
    sm3_compress_input_aligned &(ctx_pre # "_SM3_CTX" ->ₛ "block") 1).
  { unfold sm3_compress_input_aligned. right. exact Hblock_align. }
  split_pure_spatial.
  - cancel (store_u32_words &(ctx_pre # "_SM3_CTX" ->ₛ "digest") 8 State_2).
    cancel (&(ctx_pre # "_SM3_CTX" ->ₛ "nblocks") # UInt64 |-> (Zlength Message ÷ 64)).
    cancel (&(ctx_pre # "_SM3_CTX" ->ₛ "num") # UInt64 |-> Zlength Tail_2).
    cancel (UCharArray.undef_full digest_pre 32).
    cancel store_sm3_ti.
    rewrite sizeof_uint.
    replace (count + 1 * 4) with (count + 4) by lia.
    replace (count + 0 * 4) with count by lia.
    rewrite Hcpu_high, Hcpu_low.
    assert (Hswap_pair :
      store_uint (count + 4) (byte_swap32 low_word) **
      store_uint count (byte_swap32 high_word) |--
      store_uint count (byte_swap32 high_word) **
      store_uint (count + 4) (byte_swap32 low_word)).
    { cancel. }
    sep_apply Hswap_pair.
    sep_apply (two_store_uint_to_u8_full8 count
      (byte_swap32 high_word) (byte_swap32 low_word)).
    Intros high_bytes low_bytes.
    destruct H as
      [Hhigh_len [Hlow_len [Hhigh_bound [Hlow_bound
       [Hhigh_value [Hlow_value Hstored_align]]]]]].
    assert (Hhigh_bytes : high_bytes = uint_to_be_bytes 4 high_word).
    { apply u8_list_value_injective.
      - rewrite Hhigh_len, uint_to_be_bytes_length. reflexivity.
      - exact Hhigh_bound.
      - apply uint_to_be_bytes_bounded. lia.
      - rewrite Hhigh_value.
        symmetry.
        apply u8_list_value_uint_to_be_bytes4. exact Hhigh_range. }
    assert (Hlow_bytes : low_bytes = uint_to_be_bytes 4 low_word).
    { apply u8_list_value_injective.
      - rewrite Hlow_len, uint_to_be_bytes_length. reflexivity.
      - exact Hlow_bound.
      - apply uint_to_be_bytes_bounded. lia.
      - rewrite Hlow_value.
        symmetry.
        apply u8_list_value_uint_to_be_bytes4. exact Hlow_range. }
    rewrite Hhigh_bytes, Hlow_bytes, Hbe_split.
    rewrite PreH12.
    rewrite Hfinal_block.
    sep_apply_l_atomic
      (UCharArray.full_merge_to_full
        &(ctx_pre # "_SM3_CTX" ->ₛ "block") 56 64
        Prefix56 (u64_to_be_bytes (8 * Zlength Message)) ltac:(lia)).
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_sm3_final_entail_wit_20 : sm3_final_entail_wit_20.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (sm3_final_bytes_length_at_least_block Message) as Hfinal_ge64.
  assert (Hfinal_parts :
    sublist 0 (Zlength (sm3_final_bytes Message) - 64)
      (sm3_final_bytes Message) ++ BlockBytes_2 =
    sm3_final_bytes Message).
  { rewrite PreH10.
    symmetry.
    transitivity
      (sublist 0 (Zlength (sm3_final_bytes Message))
        (sm3_final_bytes Message)).
    - symmetry. apply sublist_self. reflexivity.
    - apply sublist_split; lia. }
  assert (Hfinal_prefix_len :
    Zlength
      (sublist 0 (Zlength (sm3_final_bytes Message) - 64)
        (sm3_final_bytes Message)) =
    Zlength (sm3_final_bytes Message) - 64).
  { rewrite Zlength_sublist by
      (pose proof (sm3_final_bytes_length Message); lia).
    lia. }
  assert (Hfinal_prefix_mod :
    Zlength
      (sublist 0 (Zlength (sm3_final_bytes Message) - 64)
        (sm3_final_bytes Message)) mod 64 = 0).
  { rewrite Hfinal_prefix_len.
    pose proof (sm3_final_bytes_length_multiple Message) as Hfinal_mod.
    pose proof
      (Z.div_mod (Zlength (sm3_final_bytes Message)) 64 ltac:(lia))
      as Hfinal_divmod.
    rewrite Hfinal_mod in Hfinal_divmod.
    replace (Zlength (sm3_final_bytes Message) - 64) with
      (64 * (Zlength (sm3_final_bytes Message) / 64 - 1)) by lia.
    rewrite Z.mul_comm, Z.mod_mul; lia. }
  assert (Hprefix_mod :
    Zlength
      (sm3_full_bytes Message ++
       sublist 0 (Zlength (sm3_final_bytes Message) - 64)
         (sm3_final_bytes Message)) mod 64 = 0).
  { rewrite Zlength_app, Z.add_mod by lia.
    rewrite sm3_full_bytes_length_multiple, Hfinal_prefix_mod.
    reflexivity. }
  assert (Hfinal_state :
    sm3_compress_bytes State BlockBytes_2 = sm3_digest_words Message).
  { rewrite PreH13.
    rewrite <- sm3_compress_bytes_app by exact Hprefix_mod.
    rewrite <- app_assoc, Hfinal_parts.
    rewrite sm3_compress_bytes_app by
      apply sm3_full_bytes_length_multiple.
    symmetry.
    apply sm3_digest_words_from_context. }
  Exists BlockBytes_2 (sm3_compress_bytes State BlockBytes_2) Tail_2.
  split_pure_spatial.
  - normalize.
    rewrite Hfinal_state.
    replace
      (&(ctx_pre # "_SM3_CTX" ->ₛ "block") + 0 * sizeof(UCHAR)) with
      (&(ctx_pre # "_SM3_CTX" ->ₛ "block")) by
      (rewrite sizeof_uchar; lia).
    replace (64 * 1) with 64 by lia.
    replace
      (&(ctx_pre # "_SM3_CTX" ->ₛ "digest") + 0 * sizeof(UINT)) with
      (&(ctx_pre # "_SM3_CTX" ->ₛ "digest")) by
      (rewrite sizeof_uint; lia).
    normalize.
    repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption; try reflexivity; try lia.
    all: try rewrite Hfinal_state.
    all: try apply sm3_digest_words_valid.
Qed.

Lemma proof_of_sm3_final_entail_wit_22_split_goal_1 : sm3_final_entail_wit_22_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_22_split_goal_2 : sm3_final_entail_wit_22_split_goal_2.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_22_split_goal_3 : sm3_final_entail_wit_22_split_goal_3.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_22 : sm3_final_entail_wit_22.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsubnil :
    sublist 0 (4 * 0) (sm3_digest_bytes Message) = @nil Z).
  { rewrite Zsublist_nil by lia. reflexivity. }
  assert (Hnil_bounded : u8_list_bounded (@nil Z)).
  { unfold u8_list_bounded, limb_list_bounded.
    intros index Hindex.
    rewrite Zlength_nil in Hindex.
    lia. }
  Exists (@nil Z) BlockBytes_2 FinalState_2 Tail_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_sm3_final_entail_wit_23_split_goal_1 : sm3_final_entail_wit_23_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_23_split_goal_2 : sm3_final_entail_wit_23_split_goal_2.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_23_split_goal_3 : sm3_final_entail_wit_23_split_goal_3.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_23 : sm3_final_entail_wit_23.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hword_range :
    0 <= Znth i FinalState_2 0 < 2 ^ 32).
  { unfold limb_list_bounded in PreH14.
    specialize (PreH14 i ltac:(lia)).
    unfold SM3_WORD_MODULUS in PreH14.
    exact PreH14. }
  assert (Hmask :
    Z.land (Z.shiftl (Znth i FinalState_2 0) 8) 16711680 =
    Z.land
      (unsigned_last_nbits (Z.shiftl (Znth i FinalState_2 0) 8) 32)
      16711680).
  { assert (Hmask32 : unsigned_last_nbits 16711680 32 = 16711680).
    { apply unsigned_last_nbits_eq.
      change (0 <= 16711680 < 4294967296).
      lia. }
    rewrite <- Hmask32.
    symmetry.
    apply unsigned_last_nbits_land_clear_l.
    lia. }
  assert (Hfrontend :
    Z.lor
      (Z.lor
        (Z.lor (Z.shiftr (Znth i FinalState_2 0) 24)
          (Z.land (Z.shiftr (Znth i FinalState_2 0) 8) 65280))
        (Z.land (Z.shiftl (Znth i FinalState_2 0) 8) 16711680))
      (unsigned_last_nbits (Z.shiftl (Znth i FinalState_2 0) 24) 32) =
    byte_swap32 (Znth i FinalState_2 0)).
  { rewrite Hmask.
    apply byte_swap32_frontend_equiv.
    exact Hword_range. }
  assert (Hword_value :
    u8_list_value word_bytes =
    u8_list_value (u32_to_be_bytes (Znth i FinalState_2 0))).
  { rewrite PreH1, Hfrontend.
    unfold u32_to_be_bytes.
    rewrite u8_list_value_uint_to_be_bytes4 by exact Hword_range.
    reflexivity. }
  assert (Hword_eq : word_bytes = u32_to_be_bytes (Znth i FinalState_2 0)).
  { apply u8_list_value_injective.
    - rewrite PreH3, u32_to_be_bytes_length. reflexivity.
    - exact PreH2.
    - apply u32_to_be_bytes_bounded. lia.
    - exact Hword_value. }
  assert (Houtput :
    OutputBytes_2 ++ word_bytes =
    sublist 0 (4 * (i + 1)) (sm3_digest_bytes Message)).
  { rewrite PreH19, Hword_eq, PreH12.
    unfold sm3_digest_bytes.
    apply u32_be_concat_prefix_step.
    rewrite (proj1 (sm3_digest_words_valid Message)).
    lia. }
  Exists (OutputBytes_2 ++ word_bytes) BlockBytes_2 FinalState_2 Tail_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + rewrite Zlength_app, PreH20, PreH3. lia.
    + apply (proj2 (limb_list_bounded_app SM2_BYTE_BASE _ _)).
      split; assumption.
Qed.

Lemma proof_of_sm3_final_entail_wit_24_split_goal_1 : sm3_final_entail_wit_24_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_24_split_goal_2 : sm3_final_entail_wit_24_split_goal_2.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_24_split_goal_spatial : sm3_final_entail_wit_24_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm3_final_entail_wit_24 : sm3_final_entail_wit_24.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi8 : i = 8) by lia.
  subst i.
  assert (Hdigest_len : Zlength (sm3_digest_bytes Message) = 32).
  { apply sm3_digest_bytes_length. }
  assert (Houtput : OutputBytes = sm3_digest_bytes Message).
  { rewrite PreH12.
    replace (4 * 8) with 32 by lia.
    apply sublist_self; lia. }
  repeat rewrite Houtput.
  assert (Hstore :
    store_byte_prefix digest_pre 32 (sm3_digest_bytes Message) |--
    byte_encoding.store_bytes digest_pre 32 (sm3_digest_bytes Message)).
  { apply store_byte_prefix_complete_to_store_bytes.
    exact Hdigest_len. }
  sep_apply_l_atomic Hstore.
  Exists BlockBytes_2 FinalState_2 Tail_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_sm3_final_partial_solve_wit_4_pure_split_goal_1 : sm3_final_partial_solve_wit_4_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_final_partial_solve_wit_4_pure : sm3_final_partial_solve_wit_4_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace
    (&(ctx_pre # "_SM3_CTX" ->ₛ "block") + 0 * sizeof(UCHAR))
    with (&(ctx_pre # "_SM3_CTX" ->ₛ "block")) by lia.
  exact PreH16.
Qed.

Lemma proof_of_sm3_final_partial_solve_wit_8_pure_split_goal_1 : sm3_final_partial_solve_wit_8_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm3_final_partial_solve_wit_8_pure : sm3_final_partial_solve_wit_8_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  replace
    (&(ctx_pre # "_SM3_CTX" ->ₛ "block") + 0 * sizeof(UCHAR))
    with (&(ctx_pre # "_SM3_CTX" ->ₛ "block")) by lia.
  exact PreH16.
Qed.
