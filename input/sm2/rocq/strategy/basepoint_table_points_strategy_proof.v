Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import basepoint_table_points_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_ecc_const_table.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_basepoint_mul.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma basepoint_table_points_strategy10_correctness : basepoint_table_points_strategy10.
  pre_process_default.
  assert (Hidx :
    0 <= limb * 8 * 256 + window * 256 + byte < SM2_TABLE_RECORDS)
    by (unfold SM2_TABLE_RECORDS; nia).
  sep_apply_l_atomic
    (StructAFPointArray.full_split_to_missing_i
      base (limb * 8 * 256 + window * 256 + byte)
      SM2_TABLE_RECORDS (sm2_table_flatten SM2_BASE_TABLE_DATA)
      zero_record_afpoint).
  - entailer!.
  - assert (Hflat :
      limb * 8 * 256 + window * 256 + byte =
      sm2_base_table_flat_index limb window byte).
    {
      unfold sm2_base_table_flat_index.
      rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
      rewrite !Z2Nat.id by lia.
      lia.
    }
    rewrite Hflat.
    rewrite (sm2_base_table_flatten_record_at
      limb window byte ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (Haddr :
      selected =
      base + sm2_base_table_flat_index limb window byte *
        StoreStructAFPointAsElement.sizeA).
    {
      rewrite H5, sizeof_AFPoint_layout.
      unfold sm2_base_table_flat_index,
        StoreStructAFPointAsElement.sizeA,
        StoreStructu32AsElement.sizeA.
      rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
      rewrite !Z2Nat.id by lia.
      rewrite sizeof_uint64.
      nia.
    }
    rewrite Haddr.
    split_pure_spatial.
    + transitivity
        (StructAFPointArray.missing_i base
          (sm2_base_table_flat_index limb window byte)
          0 SM2_TABLE_RECORDS
          (sm2_table_flatten SM2_BASE_TABLE_DATA) **
         StructPredAFPoint
          (base + sm2_base_table_flat_index limb window byte *
            StoreStructAFPointAsElement.sizeA)
          (sm2_base_table_record_at limb window byte)).
      * apply derivable1_sepcon_comm.
      * apply derivable1_sepcon_mono; [apply derivable1_refl |].
        apply (proj1 (derivable1_wand_sepcon_adjoint _ _ _)).
        eapply derivable1_trans; [apply derivable1_sepcon_emp_l |].
        apply StructPredAFPoint_to_store_afpoint.
        unfold sm2_table_term.
        apply sm2_base_table_record_at_represents; lia.
    + prop_apply
        (StructPredAFPoint_well_formed
          (base + sm2_base_table_flat_index limb window byte *
            StoreStructAFPointAsElement.sizeA)
          (sm2_base_table_record_at limb window byte)).
      entailer!.
Qed.

Lemma basepoint_table_points_strategy20_correctness : basepoint_table_points_strategy20.
  pre_process_default.
  transitivity
    (StructPredAFPoint
      (base + sm2_base_table_flat_index limb window byte *
        StoreStructAFPointAsElement.sizeA)
      (sm2_mont_base_table_record_at limb window byte) **
     StructAFPointArray.missing_i base
      (sm2_base_table_flat_index limb window byte)
      0 SM2_TABLE_RECORDS
      (sm2_table_flatten SM2_MONT_BASE_TABLE_DATA)).
  - apply sm2_mont_base_table_extract_record; lia.
  - assert (Hflat :
      limb * 8 * 256 + window * 256 + byte =
      sm2_base_table_flat_index limb window byte).
    {
      unfold sm2_base_table_flat_index.
      rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
      rewrite !Z2Nat.id by lia.
      lia.
    }
    rewrite Hflat.
    assert (Haddr :
      selected =
      base + sm2_base_table_flat_index limb window byte *
        StoreStructAFPointAsElement.sizeA).
    {
      rewrite H5, sizeof_AFPoint_layout.
      unfold sm2_base_table_flat_index,
        StoreStructAFPointAsElement.sizeA,
        StoreStructu32AsElement.sizeA.
      rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
      rewrite !Z2Nat.id by lia.
      rewrite sizeof_uint64.
      nia.
    }
    rewrite Haddr.
    split_pure_spatial.
    + transitivity
        (StructAFPointArray.missing_i base
          (sm2_base_table_flat_index limb window byte)
          0 SM2_TABLE_RECORDS
          (sm2_table_flatten SM2_MONT_BASE_TABLE_DATA) **
         StructPredAFPoint
          (base + sm2_base_table_flat_index limb window byte *
            StoreStructAFPointAsElement.sizeA)
          (sm2_mont_base_table_record_at limb window byte)).
      * apply derivable1_sepcon_comm.
      * apply derivable1_sepcon_mono; [apply derivable1_refl |].
        apply (proj1 (derivable1_wand_sepcon_adjoint _ _ _)).
        eapply derivable1_trans; [apply derivable1_sepcon_emp_l |].
        destruct (sm2_mont_base_table_record_at_values
          limb window byte ltac:(lia) ltac:(lia) ltac:(lia))
          as [Hx Hy].
        apply (StructPredAFPoint_to_store_mont_afpoint _ _
          (sm2_record_x (sm2_base_table_record_at limb window byte))
          (sm2_record_y (sm2_base_table_record_at limb window byte)) _).
        -- unfold sm2_table_term.
           apply sm2_base_table_record_at_represents; lia.
        -- exact Hx.
        -- exact Hy.
    + transitivity
        (“ record_afpoint_well_formed
          (sm2_mont_base_table_record_at limb window byte) ” **
         StructAFPointArray.missing_i base
          (sm2_base_table_flat_index limb window byte)
          0 SM2_TABLE_RECORDS
          (sm2_table_flatten SM2_MONT_BASE_TABLE_DATA)).
      * apply derivable1_sepcon_mono.
        -- apply StructPredAFPoint_well_formed.
        -- apply derivable1_refl.
      * entailer!.
Qed.

Lemma basepoint_table_points_strategy11_correctness : basepoint_table_points_strategy11.
  pre_process_default.
  assert (Hidx :
    0 <= sm2_base_table_flat_index limb window byte < SM2_TABLE_RECORDS).
  {
    unfold sm2_base_table_flat_index, SM2_TABLE_RECORDS.
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
    rewrite !Z2Nat.id by lia.
    nia.
  }
  assert (Hflat :
    limb * 8 * 256 + window * 256 + byte =
    sm2_base_table_flat_index limb window byte).
  {
    unfold sm2_base_table_flat_index.
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
    rewrite !Z2Nat.id by lia.
    lia.
  }
  assert (Haddr :
    selected =
    base + sm2_base_table_flat_index limb window byte *
      StoreStructAFPointAsElement.sizeA).
  {
    rewrite H6, sizeof_AFPoint_layout.
    unfold sm2_base_table_flat_index,
      StoreStructAFPointAsElement.sizeA,
      StoreStructu32AsElement.sizeA.
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
    rewrite !Z2Nat.id by lia.
    rewrite sizeof_uint64.
    nia.
  }
  rewrite Hflat, Haddr.
  transitivity
    (StructAFPointArray.missing_i base
      (sm2_base_table_flat_index limb window byte)
      0 SM2_TABLE_RECORDS
      (sm2_table_flatten SM2_BASE_TABLE_DATA) **
     StructPredAFPoint
      (base + sm2_base_table_flat_index limb window byte *
        StoreStructAFPointAsElement.sizeA)
      (sm2_base_table_record_at limb window byte)).
  - apply derivable1_sepcon_mono; [apply derivable1_refl |].
    apply store_afpoint_to_StructPredAFPoint.
    + exact H.
    + unfold sm2_table_term.
      apply sm2_base_table_record_at_represents; lia.
  - rewrite <- (sm2_base_table_flatten_record_at
      limb window byte ltac:(lia) ltac:(lia) ltac:(lia)).
    apply struct_afpoint_array_missing_i_restore_full.
    + exact Hidx.
    + apply sm2_base_table_flatten_length.
Qed.

Lemma basepoint_table_points_strategy21_correctness : basepoint_table_points_strategy21.
  pre_process_default.
  assert (Hidx :
    0 <= sm2_base_table_flat_index limb window byte < SM2_TABLE_RECORDS).
  {
    unfold sm2_base_table_flat_index, SM2_TABLE_RECORDS.
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
    rewrite !Z2Nat.id by lia.
    nia.
  }
  assert (Hflat :
    limb * 8 * 256 + window * 256 + byte =
    sm2_base_table_flat_index limb window byte).
  {
    unfold sm2_base_table_flat_index.
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
    rewrite !Z2Nat.id by lia.
    lia.
  }
  assert (Haddr :
    selected =
    base + sm2_base_table_flat_index limb window byte *
      StoreStructAFPointAsElement.sizeA).
  {
    rewrite H6, sizeof_AFPoint_layout.
    unfold sm2_base_table_flat_index,
      StoreStructAFPointAsElement.sizeA,
      StoreStructu32AsElement.sizeA.
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
    rewrite !Z2Nat.id by lia.
    rewrite sizeof_uint64.
    nia.
  }
  rewrite Hflat, Haddr.
  transitivity
    (StructAFPointArray.missing_i base
      (sm2_base_table_flat_index limb window byte)
      0 SM2_TABLE_RECORDS
      (sm2_table_flatten SM2_MONT_BASE_TABLE_DATA) **
     StructPredAFPoint
      (base + sm2_base_table_flat_index limb window byte *
        StoreStructAFPointAsElement.sizeA)
      (sm2_mont_base_table_record_at limb window byte)).
  - apply derivable1_sepcon_mono; [apply derivable1_refl |].
    destruct (sm2_mont_base_table_record_at_values
      limb window byte ltac:(lia) ltac:(lia) ltac:(lia))
      as [Hx Hy].
    apply (store_mont_afpoint_to_StructPredAFPoint _ _
      (sm2_record_x (sm2_base_table_record_at limb window byte))
      (sm2_record_y (sm2_base_table_record_at limb window byte)) _).
    + exact H.
    + unfold sm2_table_term.
      apply sm2_base_table_record_at_represents; lia.
    + exact Hx.
    + exact Hy.
  - rewrite <- (sm2_mont_base_table_flatten_record_at
      limb window byte ltac:(lia) ltac:(lia) ltac:(lia)).
    apply struct_afpoint_array_missing_i_restore_full.
    + exact Hidx.
    + apply sm2_mont_base_table_flatten_length.
Qed.
