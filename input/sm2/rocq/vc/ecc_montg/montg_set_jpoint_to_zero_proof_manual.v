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
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_set_jpoint_to_zero_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_set_jpoint_to_zero_proof_auto.
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

Lemma proof_of_montg_set_jpoint_to_zero_return_wit_1 : montg_set_jpoint_to_zero_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_montg_one, store_mont_jpoint_coords, store_jpoint_fields.
  assert (Hx :
    &((dst_pre) # "JPoint" ->ₛ "x" .ₛ "v") =
    &(((&(dst_pre # "JPoint" ->ₛ "x"))) # "u32" ->ₛ "v")).
  { csimpl. reflexivity. }
  assert (Hy :
    &((dst_pre) # "JPoint" ->ₛ "y" .ₛ "v") =
    &(((&(dst_pre # "JPoint" ->ₛ "y"))) # "u32" ->ₛ "v")).
  { csimpl. reflexivity. }
  assert (Hz :
    &((dst_pre) # "JPoint" ->ₛ "z" .ₛ "v") =
    &(((&(dst_pre # "JPoint" ->ₛ "z"))) # "u32" ->ₛ "v")).
  { csimpl. reflexivity. }
  rewrite Hx, Hy, Hz.
  unfold MONTG_ONE_Z.
  rewrite mont_p_zero.
  simpl.
  assert (Hone : 0 <= 1 < SM2_P_Z).
  { pose proof sm2_p_montgomery_bounds. lia. }
  assert (Hzero : 0 <= 0 < SM2_P_Z).
  { pose proof sm2_p_montgomery_bounds. lia. }
  unfold store_fp, store_mod, store_u256.
  entailer!.
  repeat rewrite Z.add_0_r.
  cancel.
  rewrite <- PreH4.
  unfold MONTG_ONE_Z.
  entailer!.
Qed. 

Lemma proof_of_montg_set_jpoint_to_zero_which_implies_wit_1 : montg_set_jpoint_to_zero_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_montg_set_jpoint_to_zero_derive_point_by_coords : montg_set_jpoint_to_zero_derive_point_by_coords.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cancel store_montg_one.
  cancel (UInt64Array.undef_full
    &(dst_pre # "JPoint" ->ₛ "x" .ₛ "v") 4).
  cancel (UInt64Array.undef_full
    &(dst_pre # "JPoint" ->ₛ "y" .ₛ "v") 4).
  cancel (UInt64Array.undef_full
    &(dst_pre # "JPoint" ->ₛ "z" .ₛ "v") 4).
  apply derivable1_wand_sepcon_adjoint.
  unfold store_mont_jpoint.
  Exists 1 1 0.
  split_pure_spatial.
  - entailer!.
  - dump_pre_spatial.
    pose proof sm2_p_gt_one.
    unfold jpoint_represents, ECInfinity, jpoint_infinity.
    cbn.
    lia.
Qed. 
