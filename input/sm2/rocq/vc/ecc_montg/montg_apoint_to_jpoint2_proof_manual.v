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
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_apoint_to_jpoint2_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_apoint_to_jpoint2_proof_auto.
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

Lemma proof_of_montg_apoint_to_jpoint2_return_wit_1 : montg_apoint_to_jpoint2_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Right.
  Exists 1 AY_non_alias AX_non_alias.
  unfold store_mont_afpoint_coords, store_mont_jpoint_coords,
    store_afpoint_fields, store_jpoint_fields, store_fp, store_mod,
    store_montg_one, MONTG_ONE_Z.
  split_pure_spatial.
  - replace (&("MONTG_ONE") + 0 * sizeof(UINT64))
      with (&("MONTG_ONE")) by lia.
    cancel.
    entailer!.
  - pose proof (mont_p_range 1).
    entailer!; lia.
Qed. 

Lemma proof_of_montg_apoint_to_jpoint2_return_wit_2 : montg_apoint_to_jpoint2_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Left.
  Exists 1 AY_non_alias AX_non_alias.
  unfold store_mont_afpoint_coords, store_mont_jpoint_coords,
    store_afpoint_fields, store_jpoint_fields, store_fp, store_mod,
    store_montg_one, MONTG_ONE_Z.
  split_pure_spatial.
  - replace (&("MONTG_ONE") + 0 * sizeof(UINT64))
      with (&("MONTG_ONE")) by lia.
    cancel.
    entailer!.
  - pose proof (mont_p_range 1).
    entailer!; lia.
Qed. 

Lemma proof_of_montg_apoint_to_jpoint2_which_implies_wit_1 : montg_apoint_to_jpoint2_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_montg_apoint_to_jpoint2_derive_point_non_alias_by_non_alias : montg_apoint_to_jpoint2_derive_point_non_alias_by_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_mont_afpoint at 1.
  Intros AX AY.
  rename H into Hrep.
  Exists AX AY.
  apply sepcon_cancel_end.
  - cancel (store_mont_afpoint_coords a_pre AX AY).
    cancel (UInt64Array.undef_full
      &((r_pre) # "JPoint" ->ₛ "x" .ₛ "v") 4).
    cancel (UInt64Array.undef_full
      &((r_pre) # "JPoint" ->ₛ "y" .ₛ "v") 4).
    cancel (UInt64Array.undef_full
      &((r_pre) # "JPoint" ->ₛ "z" .ₛ "v") 4).
    cancel store_bn_zero.
    cancel store_montg_one.
  - apply derivable1_wand_sepcon_adjoint.
    Split.
    + Split.
      * Intros RZ RY RX retval_2.
        assert (Hconvert :
          afpoint_to_jpoint_coordinates AX AY RX RY RZ).
        { unfold afpoint_to_jpoint_coordinates,
            afpoint_infinity, canonical_jpoint_infinity.
          left. tauto. }
        pose proof
          (afpoint_to_jpoint_coordinates_represents
             AX AY RX RY RZ P_point_non_alias Hrep Hconvert)
          as Hj.
        assert (Haf_store :
          store_mont_afpoint_coords a_pre AX AY |--
          store_mont_afpoint a_pre P_point_non_alias).
        { unfold store_mont_afpoint.
          Exists AX AY.
          unfold naive_C_Rules.derivable1.
          intros m Hm. split; auto. }
        assert (Hj_store :
          store_mont_jpoint_coords r_pre RX RY RZ |--
          store_mont_jpoint r_pre P_point_non_alias).
        { unfold store_mont_jpoint.
          Exists RX RY RZ.
          unfold naive_C_Rules.derivable1.
          intros m Hm. split; auto. }
        sep_apply_l_atomic Haf_store.
        sep_apply_l_atomic Hj_store.
        Exists 1.
        split_pure_spatial.
        -- cancel (store_mont_afpoint a_pre P_point_non_alias).
           cancel (store_mont_jpoint r_pre P_point_non_alias).
           cancel store_bn_zero.
           cancel store_montg_one.
        -- dump_pre_spatial. reflexivity.
      * Intros RZ RY RX retval_2.
        assert (Hconvert :
          afpoint_to_jpoint_coordinates AX AY RX RY RZ).
        { unfold afpoint_to_jpoint_coordinates.
          right. tauto. }
        pose proof
          (afpoint_to_jpoint_coordinates_represents
             AX AY RX RY RZ P_point_non_alias Hrep Hconvert)
          as Hj.
        assert (Haf_store :
          store_mont_afpoint_coords a_pre AX AY |--
          store_mont_afpoint a_pre P_point_non_alias).
        { unfold store_mont_afpoint.
          Exists AX AY.
          unfold naive_C_Rules.derivable1.
          intros m Hm. split; auto. }
        assert (Hj_store :
          store_mont_jpoint_coords r_pre RX RY RZ |--
          store_mont_jpoint r_pre P_point_non_alias).
        { unfold store_mont_jpoint.
          Exists RX RY RZ.
          unfold naive_C_Rules.derivable1.
          intros m Hm. split; auto. }
        sep_apply_l_atomic Haf_store.
        sep_apply_l_atomic Hj_store.
        Exists 1.
        split_pure_spatial.
        -- cancel (store_mont_afpoint a_pre P_point_non_alias).
           cancel (store_mont_jpoint r_pre P_point_non_alias).
           cancel store_bn_zero.
           cancel store_montg_one.
        -- dump_pre_spatial. reflexivity.
    + Intros RZ RY RX retval_2.
      assert (Hconvert :
        afpoint_to_jpoint_coordinates AX AY RX RY RZ).
      { unfold afpoint_to_jpoint_coordinates.
        right. tauto. }
      pose proof
        (afpoint_to_jpoint_coordinates_represents
           AX AY RX RY RZ P_point_non_alias Hrep Hconvert)
        as Hj.
      assert (Haf_store :
        store_mont_afpoint_coords a_pre AX AY |--
        store_mont_afpoint a_pre P_point_non_alias).
      { unfold store_mont_afpoint.
        Exists AX AY.
        unfold naive_C_Rules.derivable1.
        intros m Hm. split; auto. }
      assert (Hj_store :
        store_mont_jpoint_coords r_pre RX RY RZ |--
        store_mont_jpoint r_pre P_point_non_alias).
      { unfold store_mont_jpoint.
        Exists RX RY RZ.
        unfold naive_C_Rules.derivable1.
        intros m Hm. split; auto. }
      sep_apply_l_atomic Haf_store.
      sep_apply_l_atomic Hj_store.
      Exists 1.
      split_pure_spatial.
      * cancel (store_mont_afpoint a_pre P_point_non_alias).
        cancel (store_mont_jpoint r_pre P_point_non_alias).
        cancel store_bn_zero.
        cancel store_montg_one.
      * dump_pre_spatial. reflexivity.
Qed. 
