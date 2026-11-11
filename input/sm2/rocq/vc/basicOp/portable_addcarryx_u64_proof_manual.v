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
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import portable_addcarryx_u64_goal.
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import portable_addcarryx_u64_proof_auto.
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
Local Open Scope sac.

Lemma proof_of_portable_addcarryx_u64_return_wit_1_split_goal_1 : portable_addcarryx_u64_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_portable_addcarryx_u64_return_wit_1_split_goal_2 : portable_addcarryx_u64_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_portable_addcarryx_u64_return_wit_1 : portable_addcarryx_u64_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (addcarry64_mod_branches carry_in_pre a_pre b_pre
    ltac:(lia) ltac:(lia) ltac:(lia)) as H.
  cbn in H.
  unfold unsigned_last_nbits in PreH1, PreH2.
  cbn in PreH1, PreH2.
  replace (carry_in_pre mod 18446744073709551616) with carry_in_pre in H
    by (symmetry; apply Z.mod_small; lia).
  change (a_pre < 18446744073709551616) in PreH6.
  assert (Hsum_range :
    0 <= (a_pre + b_pre) mod 18446744073709551616 <
      18446744073709551616)
    by (apply Z.mod_pos_bound; lia).
  replace
    (((a_pre + b_pre) mod 18446744073709551616 + carry_in_pre)
       mod 18446744073709551616)
    with ((a_pre + b_pre) mod 18446744073709551616 + carry_in_pre) in H
    by (symmetry; apply Z.mod_small; lia).
  destruct H as [_ [H _]].
  specialize (H PreH1 PreH2).
  unfold unsigned_last_nbits in H.
  destruct H as [Hout [Hcarry Heq]].
  Exists
    (unsigned_last_nbits (a_pre + b_pre) 64 + carry_in_pre).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: unfold unsigned_last_nbits, U64_MOD; cbn; lia.
Qed. 

Lemma proof_of_portable_addcarryx_u64_return_wit_2_split_goal_1 : portable_addcarryx_u64_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_portable_addcarryx_u64_return_wit_2_split_goal_2 : portable_addcarryx_u64_return_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_portable_addcarryx_u64_return_wit_2_split_goal_3 : portable_addcarryx_u64_return_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_portable_addcarryx_u64_return_wit_2 : portable_addcarryx_u64_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (addcarry64_mod_branches carry_in_pre a_pre b_pre
    ltac:(lia) ltac:(lia) ltac:(lia)) as H.
  cbn in H.
  unfold unsigned_last_nbits in PreH1, PreH2.
  cbn in PreH1, PreH2.
  replace (carry_in_pre mod 18446744073709551616) with carry_in_pre in H
    by (symmetry; apply Z.mod_small; lia).
  destruct H as [_ [_ [H _]]].
  specialize (H PreH1 PreH2).
  unfold unsigned_last_nbits in H.
  destruct H as [Hout [Hcarry Heq]].
  Exists (unsigned_last_nbits
    (unsigned_last_nbits (a_pre + b_pre) 64 +
     carry_in_pre) 64).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: unfold unsigned_last_nbits, U64_MOD; cbn; lia.
Qed. 

Lemma proof_of_portable_addcarryx_u64_return_wit_3_split_goal_1 : portable_addcarryx_u64_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_portable_addcarryx_u64_return_wit_3_split_goal_2 : portable_addcarryx_u64_return_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_portable_addcarryx_u64_return_wit_3 : portable_addcarryx_u64_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (addcarry64_mod_branches carry_in_pre a_pre b_pre
    ltac:(lia) ltac:(lia) ltac:(lia)) as H.
  cbn in H.
  unfold unsigned_last_nbits in PreH1, PreH2.
  cbn in PreH1, PreH2.
  replace (carry_in_pre mod 18446744073709551616) with carry_in_pre in H
    by (symmetry; apply Z.mod_small; lia).
  destruct H as [_ [_ [_ H]]].
  specialize (H PreH1 PreH2).
  unfold unsigned_last_nbits in H.
  destruct H as [Hout [Hcarry Heq]].
  Exists (unsigned_last_nbits
    (unsigned_last_nbits (a_pre + b_pre) 64 +
     carry_in_pre) 64).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: unfold unsigned_last_nbits, U64_MOD; cbn; lia.
Qed. 
