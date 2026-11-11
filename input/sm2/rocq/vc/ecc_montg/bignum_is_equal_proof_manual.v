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
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import bignum_is_equal_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import bignum_is_equal_proof_auto.
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
Local Open Scope sac.

Lemma proof_of_bignum_is_equal_return_wit_1_non_alias_split_goal_1 : bignum_is_equal_return_wit_1_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (proj1
       (u256_limb_diff_eq_zero_iff__eq
          x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2)
       PreH1) as Heq_limbs.
  destruct Heq_limbs as [H0 [H1 [H2 H3]]].
  rewrite PreH11, PreH2, H0, H1, H2, H3.
  reflexivity.
Qed.

Lemma proof_of_bignum_is_equal_return_wit_1_non_alias : bignum_is_equal_return_wit_1_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_bignum_is_equal_return_wit_1_non_alias_split_goal_1.
Qed. 

Lemma proof_of_bignum_is_equal_return_wit_2_non_alias_split_goal_1 : bignum_is_equal_return_wit_2_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intro HAB.
  assert (Hrepr :
    u256_of_limbs x0 x1 x2 x3 =
    u256_of_limbs x0_2 x1_2 x2_2 x3_2).
  {
    rewrite <- PreH11, <- PreH2.
    exact HAB.
  }
  pose proof
    (u256_of_limbs_injective
       x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
       (conj PreH19 PreH18)
       (conj PreH17 PreH16)
       (conj PreH15 PreH14)
       (conj PreH13 PreH12)
       (conj PreH10 PreH9)
       (conj PreH8 PreH7)
       (conj PreH6 PreH5)
       (conj PreH4 PreH3)
       Hrepr) as Heq_limbs.
  apply PreH1.
  apply
    (proj2
       (u256_limb_diff_eq_zero_iff__eq
          x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2)).
  exact Heq_limbs.
Qed.

Lemma proof_of_bignum_is_equal_return_wit_2_non_alias : bignum_is_equal_return_wit_2_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_bignum_is_equal_return_wit_2_non_alias_split_goal_1.
Qed. 

