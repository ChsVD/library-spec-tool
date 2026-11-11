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
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_get_message_digest_goal.
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_get_message_digest_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_ecc_const_table.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_protocol.
Local Open Scope sac.

Lemma proof_of_sm2_get_message_digest_return_wit_1_split_goal_1 : sm2_get_message_digest_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_get_message_digest_return_wit_1 : sm2_get_message_digest_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm2_get_message_digest_partial_solve_wit_2_pure_split_goal_1 : sm2_get_message_digest_partial_solve_wit_2_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_get_message_digest_partial_solve_wit_2_pure_split_goal_2 : sm2_get_message_digest_partial_solve_wit_2_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2_get_message_digest_partial_solve_wit_2_pure : sm2_get_message_digest_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  change (sm3_update_data_aligned ZA_pre 32 0).
  apply sm3_update_data_aligned_empty.
  left; lia.
Qed.

Lemma proof_of_sm2_get_message_digest_partial_solve_wit_3_pure_split_goal_1 : sm2_get_message_digest_partial_solve_wit_3_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_get_message_digest_partial_solve_wit_3_pure_split_goal_2 : sm2_get_message_digest_partial_solve_wit_3_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2_get_message_digest_partial_solve_wit_3_pure : sm2_get_message_digest_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_bytes_length ZA_pre 32 ZABytes).
  Intros_p Hlen.
  prop_apply_p
    (store_bytes_address_space_bound msg_pre msg_len_pre Message).
  Intros_p Hmsg.
  entailer!.
  - rewrite app_nil_l, Hlen.
    change (0 <= msg_len_pre <= 4294967296) in Hmsg.
    unfold SM3_MAX_BYTES.
    lia.
  - rewrite app_nil_l.
    apply sm3_update_data_aligned_after_32_byte_prefix.
    + exact Hlen.
    + unfold sm2_message_input_aligned in PreH1.
      exact PreH1.
Qed.
