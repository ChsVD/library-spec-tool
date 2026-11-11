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
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import portable_mulx_u64_goal.
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import portable_mulx_u64_proof_auto.
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

Lemma proof_of_portable_mulx_u64_return_wit_1_split_goal_1 : portable_mulx_u64_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_1_split_goal_2 : portable_mulx_u64_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_1_split_goal_3 : portable_mulx_u64_return_wit_1_split_goal_3.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_1_split_goal_4 : portable_mulx_u64_return_wit_1_split_goal_4.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_1_split_goal_5 : portable_mulx_u64_return_wit_1_split_goal_5.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_1 : portable_mulx_u64_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (mulx_partial_products_frontend a_pre b_pre)
    as [Hp0 [Hp1 [Hp2 Hp3]]].
  assert (Hmid :
    1 = 1 /\ mulx_mid a_pre b_pre < mulx_p1 a_pre b_pre \/
    1 = 0 /\ mulx_mid a_pre b_pre >= mulx_p1 a_pre b_pre).
  {
    left; split; [reflexivity |].
    unfold mulx_mid.
    rewrite Hp1, Hp2.
    exact PreH2.
  }
  assert (Hlo :
    1 = 1 /\ mulx_lo a_pre b_pre < mulx_mid_lo a_pre b_pre \/
    1 = 0 /\ mulx_lo a_pre b_pre >= mulx_mid_lo a_pre b_pre).
  {
    left; split; [reflexivity |].
    unfold mulx_lo, mulx_mid_lo, mulx_mid.
    rewrite Hp0, Hp1, Hp2.
    exact PreH1.
  }
  pose proof (mulx_u64_correct a_pre b_pre 1 1
    ltac:(lia) ltac:(lia) Hmid Hlo) as [Hlo_range [Hhi_range Hprod]].
  rewrite <- Hp0, <- Hp1, <- Hp2, <- Hp3.
  fold (mulx_mid a_pre b_pre).
  fold (mulx_mid_lo a_pre b_pre).
  fold (mulx_lo a_pre b_pre).
  fold (mulx_mid_hi a_pre b_pre 1).
  fold (mulx_hi a_pre b_pre 1 1).
  Exists (mulx_hi a_pre b_pre 1 1).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_portable_mulx_u64_return_wit_2_split_goal_1 : portable_mulx_u64_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_2_split_goal_2 : portable_mulx_u64_return_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_2_split_goal_3 : portable_mulx_u64_return_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_2_split_goal_4 : portable_mulx_u64_return_wit_2_split_goal_4.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_2_split_goal_5 : portable_mulx_u64_return_wit_2_split_goal_5.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_2 : portable_mulx_u64_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (mulx_partial_products_frontend a_pre b_pre)
    as [Hp0 [Hp1 [Hp2 Hp3]]].
  assert (Hmid :
    1 = 1 /\ mulx_mid a_pre b_pre < mulx_p1 a_pre b_pre \/
    1 = 0 /\ mulx_mid a_pre b_pre >= mulx_p1 a_pre b_pre).
  {
    left; split; [reflexivity |].
    unfold mulx_mid.
    rewrite Hp1, Hp2.
    exact PreH2.
  }
  assert (Hlo :
    0 = 1 /\ mulx_lo a_pre b_pre < mulx_mid_lo a_pre b_pre \/
    0 = 0 /\ mulx_lo a_pre b_pre >= mulx_mid_lo a_pre b_pre).
  {
    right; split; [reflexivity |].
    unfold mulx_lo, mulx_mid_lo, mulx_mid.
    rewrite Hp0, Hp1, Hp2.
    exact PreH1.
  }
  pose proof (mulx_u64_correct a_pre b_pre 1 0
    ltac:(lia) ltac:(lia) Hmid Hlo) as [Hlo_range [Hhi_range Hprod]].
  rewrite <- Hp0, <- Hp1, <- Hp2, <- Hp3.
  fold (mulx_mid a_pre b_pre).
  fold (mulx_mid_lo a_pre b_pre).
  fold (mulx_lo a_pre b_pre).
  fold (mulx_mid_hi a_pre b_pre 1).
  fold (mulx_hi a_pre b_pre 1 0).
  Exists (mulx_hi a_pre b_pre 1 0).
  split_pure_spatial.
  - unfold mulx_hi.
    repeat rewrite unsigned_unsigned_add_r by lia.
    reflexivity.
  - split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_portable_mulx_u64_return_wit_3_split_goal_1 : portable_mulx_u64_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_3_split_goal_2 : portable_mulx_u64_return_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_3_split_goal_3 : portable_mulx_u64_return_wit_3_split_goal_3.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_3_split_goal_4 : portable_mulx_u64_return_wit_3_split_goal_4.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_3_split_goal_5 : portable_mulx_u64_return_wit_3_split_goal_5.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_3 : portable_mulx_u64_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (mulx_partial_products_frontend a_pre b_pre)
    as [Hp0 [Hp1 [Hp2 Hp3]]].
  assert (Hmid :
    0 = 1 /\ mulx_mid a_pre b_pre < mulx_p1 a_pre b_pre \/
    0 = 0 /\ mulx_mid a_pre b_pre >= mulx_p1 a_pre b_pre).
  {
    right; split; [reflexivity |].
    unfold mulx_mid.
    rewrite Hp1, Hp2.
    exact PreH2.
  }
  assert (Hlo :
    1 = 1 /\ mulx_lo a_pre b_pre < mulx_mid_lo a_pre b_pre \/
    1 = 0 /\ mulx_lo a_pre b_pre >= mulx_mid_lo a_pre b_pre).
  {
    left; split; [reflexivity |].
    unfold mulx_lo, mulx_mid_lo, mulx_mid.
    rewrite Hp0, Hp1, Hp2.
    exact PreH1.
  }
  pose proof (mulx_u64_correct a_pre b_pre 0 1
    ltac:(lia) ltac:(lia) Hmid Hlo) as [Hlo_range [Hhi_range Hprod]].
  rewrite <- Hp0, <- Hp1, <- Hp2, <- Hp3.
  fold (mulx_mid a_pre b_pre).
  fold (mulx_mid_lo a_pre b_pre).
  fold (mulx_lo a_pre b_pre).
  fold (mulx_mid_hi a_pre b_pre 0).
  fold (mulx_hi a_pre b_pre 0 1).
  Exists (mulx_hi a_pre b_pre 0 1).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_portable_mulx_u64_return_wit_4_split_goal_1 : portable_mulx_u64_return_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_4_split_goal_2 : portable_mulx_u64_return_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_4_split_goal_3 : portable_mulx_u64_return_wit_4_split_goal_3.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_4_split_goal_4 : portable_mulx_u64_return_wit_4_split_goal_4.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_4_split_goal_5 : portable_mulx_u64_return_wit_4_split_goal_5.
Proof. Abort.

Lemma proof_of_portable_mulx_u64_return_wit_4 : portable_mulx_u64_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (mulx_partial_products_frontend a_pre b_pre)
    as [Hp0 [Hp1 [Hp2 Hp3]]].
  assert (Hmid :
    0 = 1 /\ mulx_mid a_pre b_pre < mulx_p1 a_pre b_pre \/
    0 = 0 /\ mulx_mid a_pre b_pre >= mulx_p1 a_pre b_pre).
  {
    right; split; [reflexivity |].
    unfold mulx_mid.
    rewrite Hp1, Hp2.
    exact PreH2.
  }
  assert (Hlo :
    0 = 1 /\ mulx_lo a_pre b_pre < mulx_mid_lo a_pre b_pre \/
    0 = 0 /\ mulx_lo a_pre b_pre >= mulx_mid_lo a_pre b_pre).
  {
    right; split; [reflexivity |].
    unfold mulx_lo, mulx_mid_lo, mulx_mid.
    rewrite Hp0, Hp1, Hp2.
    exact PreH1.
  }
  pose proof (mulx_u64_correct a_pre b_pre 0 0
    ltac:(lia) ltac:(lia) Hmid Hlo) as [Hlo_range [Hhi_range Hprod]].
  rewrite <- Hp0, <- Hp1, <- Hp2, <- Hp3.
  fold (mulx_mid a_pre b_pre).
  fold (mulx_mid_lo a_pre b_pre).
  fold (mulx_lo a_pre b_pre).
  fold (mulx_mid_hi a_pre b_pre 0).
  fold (mulx_hi a_pre b_pre 0 0).
  Exists (mulx_hi a_pre b_pre 0 0).
  split_pure_spatial.
  - unfold mulx_hi.
    repeat rewrite unsigned_unsigned_add_r by lia.
    reflexivity.
  - split_pures; dump_pre_spatial; lia.
Qed. 
