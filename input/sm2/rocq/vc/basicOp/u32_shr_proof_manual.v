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
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import u32_shr_goal.
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import u32_shr_proof_auto.
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

Lemma proof_of_u32_shr_return_wit_1_split_goal_1 : u32_shr_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_shr_return_wit_1_split_goal_2 : u32_shr_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_shr_return_wit_1_split_goal_3 : u32_shr_return_wit_1_split_goal_3.
Proof. Abort.

Lemma proof_of_u32_shr_return_wit_1_split_goal_4 : u32_shr_return_wit_1_split_goal_4.
Proof. Abort.

Lemma proof_of_u32_shr_return_wit_1_split_goal_5 : u32_shr_return_wit_1_split_goal_5.
Proof. Abort.

Lemma proof_of_u32_shr_return_wit_1_split_goal_6 : u32_shr_return_wit_1_split_goal_6.
Proof. Abort.

Lemma proof_of_u32_shr_return_wit_1_split_goal_7 : u32_shr_return_wit_1_split_goal_7.
Proof. Abort.

Lemma proof_of_u32_shr_return_wit_1_split_goal_8 : u32_shr_return_wit_1_split_goal_8.
Proof. Abort.

Lemma proof_of_u32_shr_return_wit_1_split_goal_9 : u32_shr_return_wit_1_split_goal_9.
Proof. Abort.

Lemma proof_of_u32_shr_return_wit_1 : u32_shr_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_u256, store_u256_limbs.
  Exists
    (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits (Z.shiftl x1 63) 64))
    (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits (Z.shiftl x2 63) 64))
    (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits (Z.shiftl x3 63) 64))
    (Z.shiftr x3 1).
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - dump_pre_spatial.
    repeat split;
    rewrite ?u64_rshift_lor_add__u256_shift by lia;
    rewrite ?Z.shiftr_div_pow2 by lia;
    rewrite ?unsigned_last_nbits_shiftl_high__u256_shift by lia;
    change (2 ^ 1) with 2 in *;
    change (64 - 1) with 63 in *;
    pose proof (Z.div_mod x0 2 ltac:(lia)) as Hdm0;
    pose proof (Z.div_mod x1 2 ltac:(lia)) as Hdm1;
    pose proof (Z.div_mod x2 2 ltac:(lia)) as Hdm2;
    pose proof (Z.div_mod x3 2 ltac:(lia)) as Hdm3;
    pose proof (Z.mod_pos_bound x0 2 ltac:(lia)) as Hmod0;
    pose proof (Z.mod_pos_bound x1 2 ltac:(lia)) as Hmod1;
    pose proof (Z.mod_pos_bound x2 2 ltac:(lia)) as Hmod2;
    pose proof (Z.mod_pos_bound x3 2 ltac:(lia)) as Hmod3;
    try (cbv [u256_of_limbs U64_MOD] in *; nia).
    assert (HXnonneg : 0 <= X).
    {
      rewrite PreH1.
      pose proof
        (u256_of_limbs_range x0 x1 x2 x3
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HXrange.
      exact (proj1 HXrange).
    }
    rewrite Z.quot_div_nonneg by lia.
    rewrite PreH1.
    unfold u256_of_limbs.
    replace
      (x0 + x1 * U64_MOD +
        x2 * U64_MOD ^ 2 +
        x3 * U64_MOD ^ 3)
      with (x0 + (x1 * 2 ^ 63 + x2 * 2 ^ 127 + x3 * 2 ^ 191) * 2)
      by (cbv [U64_MOD]; ring).
    rewrite Z.div_add by lia.
    cbv [U64_MOD] in *.
    nia.
Qed. 
