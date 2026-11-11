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
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_inv_mod_p_ex_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_inv_mod_p_ex_proof_auto.
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
Import Snaive_C_Rules.
Local Open Scope sac.

Lemma proof_of_montg_inv_mod_p_ex_return_wit_1_non_alias : montg_inv_mod_p_ex_return_wit_1_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists Ainv_non_2.
  unfold store_sm2_p, store_sm2_rhop.
  entailer!.
Qed. 

Lemma proof_of_montg_inv_mod_p_ex_return_wit_2_in_place : montg_inv_mod_p_ex_return_wit_2_in_place.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists Ainv_in_2.
  unfold store_sm2_p, store_sm2_rhop.
  entailer!.
Qed. 

Lemma proof_of_montg_inv_mod_p_ex_derive_field_non_alias_by_non_alias : montg_inv_mod_p_ex_derive_field_non_alias_by_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_fp, store_mod, store_u256.
  rewrite !u32_v_field_address_eq.
  Intros.
  subst PA_field_non_alias; subst PR_field_non_alias.
  Exists A_field_non_alias.
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    Intros Ainv.
    Exists Ainv.
    pose proof (mont_p_range Ainv).
    entailer!.
Qed. 
