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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import CopyJPoint_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import CopyJPoint_proof_auto.
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

Lemma proof_of_CopyJPoint_derive_mont_in_place_by_in_place : CopyJPoint_derive_mont_in_place_by_in_place.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename P_mont_in_place into P.
  match goal with
  | H : dst_pre = src_pre |- _ => rename H into Heq
  end.
  subst dst_pre.
  unfold store_mont_jpoint at 1.
  Intros X Y Z.
  unfold store_mont_jpoint_coords at 1.
  Intros_p HX.
  Intros_p HY.
  Intros_p HZ.
  Exists (mont_p X) (mont_p Y) (mont_p Z).
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    unfold store_mont_jpoint.
    Exists X Y Z.
    unfold store_mont_jpoint_coords.
    entailer!.
Qed. 

Lemma proof_of_CopyJPoint_derive_mont_non_alias_by_non_alias : CopyJPoint_derive_mont_non_alias_by_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename P_mont_non_alias into P.
  unfold store_mont_jpoint at 1.
  Intros X Y Z.
  unfold store_mont_jpoint_coords at 1.
  Intros_p HX.
  Intros_p HY.
  Intros_p HZ.
  Exists (mont_p X) (mont_p Y) (mont_p Z).
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    unfold store_mont_jpoint.
    Exists X Y Z X Y Z.
    unfold store_mont_jpoint_coords.
    entailer!.
Qed. 
