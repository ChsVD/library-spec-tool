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
From SimpleC.EE.Applications_human.sm2.vc.sm3 Require Import sm3_init_goal.
From SimpleC.EE.Applications_human.sm2.vc.sm3 Require Import sm3_init_proof_auto.
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

Lemma proof_of_sm3_init_return_wit_1_split_goal_1 : sm3_init_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold u8_list_bounded, limb_list_bounded.
  intros i Hi.
  rewrite Zlength_nil in Hi.
  lia.
Qed.

Lemma proof_of_sm3_init_return_wit_1_split_goal_2 : sm3_init_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm3_init_return_wit_1_split_goal_3 : sm3_init_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm3_init_return_wit_1_split_goal_4 : sm3_init_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm3_init_return_wit_1_split_goal_5 : sm3_init_return_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm3_init_return_wit_1_split_goal_6 : sm3_init_return_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold sm3_compress_bytes, sm3_full_bytes, sm3_full_len, SM3_IV.
  cbn.
  repeat rewrite limb_list_bounded_cons_iff.
  unfold limb_list_bounded, SM3_WORD_MODULUS.
  cbn.
  repeat split; lia.
Qed.

Lemma proof_of_sm3_init_return_wit_1_split_goal_7 : sm3_init_return_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold sm3_tail, sm3_full_len.
  reflexivity.
Qed.

Lemma proof_of_sm3_init_return_wit_1_split_goal_8 : sm3_init_return_wit_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm3_init_return_wit_1_split_goal_9 : sm3_init_return_wit_1_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold sm3_tail, sm3_full_len, u8_list_bounded, limb_list_bounded.
  intros i Hi.
  rewrite Zlength_nil in Hi.
  lia.
Qed.

Lemma proof_of_sm3_init_return_wit_1_split_goal_spatial : sm3_init_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold sm3_tail, sm3_full_len, sm3_compress_bytes, sm3_full_bytes, SM3_IV.
  simpl.
  rewrite Zlength_nil.
  rewrite Z.add_0_r.
  rewrite UCharArray.full_empty.
  rewrite UIntArray.full_unfold.
  repeat rewrite UIntArray.seg_unfold.
  rewrite UIntArray.seg_empty.
  simpl.
  split_pure_spatial.
  - replace (&(ctx_pre # "_SM3_CTX" ->ₛ "block") + 0) with (&(ctx_pre # "_SM3_CTX" ->ₛ "block")) by lia.
    replace (&(ctx_pre # "_SM3_CTX" ->ₛ "digest") + 0) with (&(ctx_pre # "_SM3_CTX" ->ₛ "digest")) by lia.
    cancel.
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_sm3_init_return_wit_1 : sm3_init_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm3_init_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_sm3_init_return_wit_1_split_goal_1.
  - Goal_apply proof_of_sm3_init_return_wit_1_split_goal_2.
  - Goal_apply proof_of_sm3_init_return_wit_1_split_goal_3.
  - Goal_apply proof_of_sm3_init_return_wit_1_split_goal_4.
  - Goal_apply proof_of_sm3_init_return_wit_1_split_goal_5.
  - Goal_apply proof_of_sm3_init_return_wit_1_split_goal_6.
  - Goal_apply proof_of_sm3_init_return_wit_1_split_goal_7.
  - Goal_apply proof_of_sm3_init_return_wit_1_split_goal_8.
  - Goal_apply proof_of_sm3_init_return_wit_1_split_goal_9.
Qed.
