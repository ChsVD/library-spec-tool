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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import equ_to_JPoint_one_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import equ_to_JPoint_one_proof_auto.
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

Lemma proof_of_equ_to_JPoint_one_derive_point_by_base : equ_to_JPoint_one_derive_point_by_base.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename P_point into P.
  unfold store_jpoint_with_canonical_infinity.
  Intros JX JY JZ.
  match goal with
  | H : jpoint_represents JX JY JZ P /\ _ |- _ =>
      destruct H as [Hrep Hcanonical]
  end.
  pose proof
    (jpoint_represents_infinity_iff JX JY JZ P Hrep) as Hinf.
  Exists JX JY JZ.
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    entailer!.
    repeat apply derivable1_orp_elim.
    + Intros retval.
      Left.
      Exists retval JX JY JZ; entailer!; tauto.
    + Intros retval.
      Right.
      Exists retval JX JY JZ; entailer!.
      unfold canonical_jpoint_infinity in Hcanonical.
      tauto.
    + Intros retval.
      Right.
      Exists retval JX JY JZ; entailer!.
      unfold canonical_jpoint_infinity in Hcanonical.
      tauto.
    + Intros retval.
      Right.
      Exists retval JX JY JZ; entailer!.
      unfold canonical_jpoint_infinity in Hcanonical.
      tauto.
Qed. 
