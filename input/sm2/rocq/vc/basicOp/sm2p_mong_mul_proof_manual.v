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
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import sm2p_mong_mul_goal.
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import sm2p_mong_mul_proof_auto.
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

Lemma proof_of_sm2p_mong_mul_return_wit_1_non_alias : sm2p_mong_mul_return_wit_1_non_alias.
Proof.
  LLM_pre_process ltac:(lia).
  Exists K_2 Zout_2.
  unfold store_u256.
  replace (&(x_pre # "u32" ->ₛ "v") + 0 * sizeof(UINT64))
    with (&(x_pre # "u32" ->ₛ "v")) by lia.
  replace (&(y_pre # "u32" ->ₛ "v") + 0 * sizeof(UINT64))
    with (&(y_pre # "u32" ->ₛ "v")) by lia.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    try assumption;
    lia.
Qed. 

Lemma proof_of_sm2p_mong_mul_return_wit_2_r_eq_x : sm2p_mong_mul_return_wit_2_r_eq_x.
Proof.
  LLM_pre_process ltac:(lia).
  Exists K_2 Zout_2.
  unfold store_u256.
  replace (&(y_pre # "u32" ->ₛ "v") + 0 * sizeof(UINT64))
    with (&(y_pre # "u32" ->ₛ "v")) by lia.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    try assumption;
    lia.
Qed. 

Lemma proof_of_sm2p_mong_mul_return_wit_3_r_eq_y : sm2p_mong_mul_return_wit_3_r_eq_y.
Proof.
  LLM_pre_process ltac:(lia).
  Exists K_2 Zout_2.
  unfold store_u256.
  replace (&(x_pre # "u32" ->ₛ "v") + 0 * sizeof(UINT64))
    with (&(x_pre # "u32" ->ₛ "v")) by lia.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    try assumption;
    lia.
Qed. 
