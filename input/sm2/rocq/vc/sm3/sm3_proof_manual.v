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
From SimpleC.EE.Applications_human.sm2.vc.sm3 Require Import sm3_goal.
From SimpleC.EE.Applications_human.sm2.vc.sm3 Require Import sm3_proof_auto.
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

Lemma proof_of_sm3_return_wit_1_split_goal_1 : sm3_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(simpl; reflexivity).
Qed.

Lemma proof_of_sm3_return_wit_1 : sm3_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm3_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_sm3_partial_solve_wit_2_pure_split_goal_1 : sm3_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p
    (store_bytes_address_space_bound data_pre datalen_pre Message).
  Intros_p Hbound. dump_pre_spatial.
  change (0 <= datalen_pre <= 4294967296) in Hbound.
  rewrite Zlength_nil. unfold SM3_MAX_BYTES. lia.
Qed.

Lemma proof_of_sm3_partial_solve_wit_2_pure_split_goal_2 : sm3_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite sm3_tail_length.
  simpl.
  unfold sm3_update_data_aligned.
  left.
  split; [reflexivity |].
  exact PreH3.
Qed.

Lemma proof_of_sm3_partial_solve_wit_2_pure : sm3_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm3_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_sm3_partial_solve_wit_2_pure_split_goal_2.
Qed.
