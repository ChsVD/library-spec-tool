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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import montg_inv_mod_n_ex_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import montg_inv_mod_n_ex_proof_auto.
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
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Local Open Scope sac.

Lemma proof_of_montg_inv_mod_n_ex_return_wit_1_in_place : montg_inv_mod_n_ex_return_wit_1_in_place.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists k_call_in z_call_in.
  unfold store_sm2_n, store_sm2_rhon, store_sm2_neg_inv_n.
  entailer!.
Qed. 

Lemma proof_of_montg_inv_mod_n_ex_return_wit_2_non_alias : montg_inv_mod_n_ex_return_wit_2_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists k_call_non z_call_non.
  unfold store_sm2_n, store_sm2_rhon, store_sm2_neg_inv_n.
  entailer!.
Qed. 

