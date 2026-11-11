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
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import u32_eq_zero_goal.
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import u32_eq_zero_proof_auto.
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

Lemma proof_of_u32_eq_zero_return_wit_1_split_goal_1 : u32_eq_zero_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_eq_zero_return_wit_1 : u32_eq_zero_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (u256_limb_or x0 x1 x2 x3 = 0) in PreH1.
  apply u256_limb_or_eq_zero_iff__eq_zero in PreH1.
  destruct PreH1 as [-> [-> [-> ->]]].
  unfold store_u256, store_u256_limbs.
  Exists 0 0 0 0.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    try assumption;
    lia.
Qed. 

Lemma proof_of_u32_eq_zero_return_wit_2_split_goal_1 : u32_eq_zero_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_eq_zero_return_wit_2 : u32_eq_zero_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hneq : A <> 0).
  {
    intro HA.
    assert (Hzero : x0 = 0 /\ x1 = 0 /\ x2 = 0 /\ x3 = 0).
    {
      apply (proj1 (u256_of_limbs_eq_zero_iff__eq_zero
        x0 x1 x2 x3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
      rewrite <- PreH2.
      exact HA.
    }
    destruct Hzero as [-> [-> [-> ->]]].
    apply PreH1.
    reflexivity.
  }
  unfold store_u256, store_u256_limbs.
  Exists x0 x1 x2 x3.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    try assumption;
    lia.
Qed. 
