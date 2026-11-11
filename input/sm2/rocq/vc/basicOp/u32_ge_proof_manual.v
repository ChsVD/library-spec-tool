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
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import u32_ge_goal.
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import u32_ge_proof_auto.
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

Lemma proof_of_u32_ge_return_wit_1_split_goal_1 : u32_ge_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_ge_return_wit_1 : u32_ge_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto || nia).
  unfold store_u256, store_u256_limbs.
  Exists x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial;
    cbv [u256_of_limbs U64_MOD] in *; nia.
Qed. 

Lemma proof_of_u32_ge_return_wit_2_split_goal_1 : u32_ge_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_ge_return_wit_2 : u32_ge_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto || nia).
  unfold store_u256, store_u256_limbs.
  Exists x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial;
    cbv [u256_of_limbs U64_MOD] in *; nia.
Qed. 

Lemma proof_of_u32_ge_return_wit_3_split_goal_1 : u32_ge_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_ge_return_wit_3 : u32_ge_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto || nia).
  unfold store_u256, store_u256_limbs.
  Exists x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial;
    cbv [u256_of_limbs U64_MOD] in *; nia.
Qed. 

Lemma proof_of_u32_ge_return_wit_4_split_goal_1 : u32_ge_return_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_ge_return_wit_4 : u32_ge_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto || nia).
  unfold store_u256, store_u256_limbs.
  Exists x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial;
    cbv [u256_of_limbs U64_MOD] in *; nia.
Qed. 

Lemma proof_of_u32_ge_return_wit_5_split_goal_1 : u32_ge_return_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_ge_return_wit_5 : u32_ge_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto || nia).
  unfold store_u256, store_u256_limbs.
  Exists x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial;
    cbv [u256_of_limbs U64_MOD] in *; nia.
Qed. 

Lemma proof_of_u32_ge_return_wit_6_split_goal_1 : u32_ge_return_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_ge_return_wit_6 : u32_ge_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto || nia).
  unfold store_u256, store_u256_limbs.
  Exists x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial;
    cbv [u256_of_limbs U64_MOD] in *; nia.
Qed. 

Lemma proof_of_u32_ge_return_wit_7_split_goal_1 : u32_ge_return_wit_7_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_ge_return_wit_7 : u32_ge_return_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto || nia).
  unfold store_u256, store_u256_limbs.
  Exists x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial;
    cbv [u256_of_limbs U64_MOD] in *; nia.
Qed. 

Lemma proof_of_u32_ge_return_wit_8_split_goal_1 : u32_ge_return_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_ge_return_wit_8 : u32_ge_return_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto || nia).
  unfold store_u256, store_u256_limbs.
  Exists x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial;
    cbv [u256_of_limbs U64_MOD] in *; nia.
Qed. 
