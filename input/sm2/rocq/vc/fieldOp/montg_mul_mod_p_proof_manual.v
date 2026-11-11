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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import montg_mul_mod_p_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import montg_mul_mod_p_proof_auto.
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
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Local Open Scope sac.

Lemma proof_of_montg_mul_mod_p_return_wit_1_non_alias : montg_mul_mod_p_return_wit_1_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists K_2 Zout_2.
  entailer!.
Qed.

Lemma proof_of_montg_mul_mod_p_return_wit_2_r_eq_a : montg_mul_mod_p_return_wit_2_r_eq_a.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists K_2 Zout_2.
  entailer!.
Qed.

Lemma proof_of_montg_mul_mod_p_return_wit_3_r_eq_b : montg_mul_mod_p_return_wit_3_r_eq_b.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists K_2 Zout_2.
  entailer!.
Qed.

Lemma proof_of_montg_mul_mod_p_derive_mont_r_eq_b_by_r_eq_b : montg_mul_mod_p_derive_mont_r_eq_b_by_r_eq_b.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename B_mont_r_eq_b into B.
  rename A_mont_r_eq_b into A.
  unfold store_fp, store_mod.
  Intros.
  Exists (mont_p A) (mont_p B).
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    Intros K Zout.
    assert (HZ : Zout = mont_p (A * B)).
    { eapply sm2p_montgomery_mul_from_equation; eauto. }
    pose proof (mont_p_range A).
    pose proof (mont_p_range B).
    pose proof (mont_p_range (A * B)).
    rewrite HZ.
    entailer!.
Qed.

Lemma proof_of_montg_mul_mod_p_derive_mont_r_eq_a_by_r_eq_a : montg_mul_mod_p_derive_mont_r_eq_a_by_r_eq_a.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename B_mont_r_eq_a into B.
  rename A_mont_r_eq_a into A.
  unfold store_fp, store_mod.
  Intros.
  Exists (mont_p A) (mont_p B).
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    Intros K Zout.
    assert (HZ : Zout = mont_p (A * B)).
    { eapply sm2p_montgomery_mul_from_equation; eauto. }
    pose proof (mont_p_range A).
    pose proof (mont_p_range B).
    pose proof (mont_p_range (A * B)).
    rewrite HZ.
    entailer!.
Qed.

Lemma proof_of_montg_mul_mod_p_derive_mont_non_alias_by_non_alias : montg_mul_mod_p_derive_mont_non_alias_by_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename B_mont_non_alias into B.
  rename A_mont_non_alias into A.
  unfold store_fp, store_mod.
  Intros.
  Exists (mont_p A) (mont_p B).
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    Intros K Zout.
    assert (HZ : Zout = mont_p (A * B)).
    { eapply sm2p_montgomery_mul_from_equation; eauto. }
    pose proof (mont_p_range A).
    pose proof (mont_p_range B).
    pose proof (mont_p_range (A * B)).
    rewrite HZ.
    entailer!.
Qed.
