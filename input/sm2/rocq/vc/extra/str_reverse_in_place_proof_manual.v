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
From SimpleC.EE.Applications_human.sm2.vc.extra Require Import str_reverse_in_place_goal.
From SimpleC.EE.Applications_human.sm2.vc.extra Require Import str_reverse_in_place_proof_auto.
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

Lemma proof_of_str_reverse_in_place_entail_wit_2 : str_reverse_in_place_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia).
  Exists bytes 0.
  rewrite sizeof_uchar.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia; try assumption.
  apply byte_reverse_loop_state_initial.
Qed.

Lemma proof_of_str_reverse_in_place_entail_wit_3 : str_reverse_in_place_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia).
  subst len_pre.
  rewrite sizeof_uchar in PreH2, PreH3.
  Exists
    (replace_Znth (Zlength current_2 - 1 - index_2)
      (Znth index_2 current_2 0)
      (replace_Znth index_2
        (Znth (Zlength current_2 - 1 - index_2) current_2 0)
    current_2))
    (index_2 + 1).
  rewrite sizeof_uchar.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia; try assumption.
    + rewrite !Zlength_replace_Znth. reflexivity.
    + assert (Hstate_length : Zlength current_2 = Zlength bytes) by
        (unfold byte_reverse_loop_state in PreH10; tauto).
      rewrite Hstate_length.
      apply byte_reverse_loop_state_step; [exact PreH10 | lia].
Qed.

Lemma proof_of_str_reverse_in_place_return_wit_1_split_goal_1 : str_reverse_in_place_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold byte_reverse_loop_state in PreH10.
  rewrite !Zlength_correct, length_rev in *.
  lia.
Qed.

Lemma proof_of_str_reverse_in_place_return_wit_1_split_goal_2 : str_reverse_in_place_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  unfold u8_list_bounded in *.
  rewrite limb_list_bounded_rev.
  exact PreH5.
Qed.

Lemma proof_of_str_reverse_in_place_return_wit_1_split_goal_3 : str_reverse_in_place_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  apply (byte_reverse_loop_state_finished bytes current index PreH10).
  rewrite sizeof_uchar in PreH2, PreH3.
  unfold byte_reverse_loop_state in PreH10.
  lia.
Qed.

Lemma proof_of_str_reverse_in_place_return_wit_1 : str_reverse_in_place_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_str_reverse_in_place_return_wit_1_split_goal_1.
  - Goal_apply proof_of_str_reverse_in_place_return_wit_1_split_goal_2.
  - Goal_apply proof_of_str_reverse_in_place_return_wit_1_split_goal_3.
Qed.
