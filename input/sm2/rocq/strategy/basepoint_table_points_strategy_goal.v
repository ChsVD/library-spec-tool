Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
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

Definition basepoint_table_points_strategy10 :=
  forall (selected : Z) (window : Z) (base : Z) (limb : Z) (byte : Z),
    TT &&
    (“ (Z.le 0 limb) ”) &&
    (“ (Z.lt limb 4) ”) &&
    (“ (Z.le 0 window) ”) &&
    (“ (Z.lt window 8) ”) &&
    (“ (Z.le 0 byte) ”) &&
    (“ (Z.lt byte 256) ”) &&
    (“ (selected = (Z.add (Z.add (Z.add base (Z.mul limb (Z.mul (Z.mul (@sizeof_front_end_type (FET_alias ("AFPoint"))) 256) 8))) (Z.mul window (Z.mul (@sizeof_front_end_type (FET_alias ("AFPoint"))) 256))) (Z.mul byte (@sizeof_front_end_type (FET_alias ("AFPoint")))))) ”) &&
    emp **
    ((StructAFPointArray.full base ( SM2_TABLE_RECORDS) ( sm2_table_flatten ( SM2_BASE_TABLE_DATA))))
    |--
    (
    TT &&
    (“ (record_afpoint_well_formed ( sm2_base_table_record_at limb window byte)) ”) &&
    emp **
    ((StructAFPointArray.missing_i base (Z.add (Z.add (Z.mul (Z.mul limb 8) 256) (Z.mul window 256)) byte) 0 ( SM2_TABLE_RECORDS) ( sm2_table_flatten ( SM2_BASE_TABLE_DATA))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_afpoint selected ( sm2_point_mul ( sm2_table_term byte limb window) ( SM2_G_POINT))))
    ).

Definition basepoint_table_points_strategy20 :=
  forall (selected : Z) (window : Z) (base : Z) (limb : Z) (byte : Z),
    TT &&
    (“ (Z.le 0 limb) ”) &&
    (“ (Z.lt limb 4) ”) &&
    (“ (Z.le 0 window) ”) &&
    (“ (Z.lt window 8) ”) &&
    (“ (Z.le 0 byte) ”) &&
    (“ (Z.lt byte 256) ”) &&
    (“ (selected = (Z.add (Z.add (Z.add base (Z.mul limb (Z.mul (Z.mul (@sizeof_front_end_type (FET_alias ("AFPoint"))) 256) 8))) (Z.mul window (Z.mul (@sizeof_front_end_type (FET_alias ("AFPoint"))) 256))) (Z.mul byte (@sizeof_front_end_type (FET_alias ("AFPoint")))))) ”) &&
    emp **
    ((StructAFPointArray.full base ( SM2_TABLE_RECORDS) ( sm2_table_flatten ( SM2_MONT_BASE_TABLE_DATA))))
    |--
    (
    TT &&
    (“ (record_afpoint_well_formed ( sm2_mont_base_table_record_at limb window byte)) ”) &&
    emp **
    ((StructAFPointArray.missing_i base (Z.add (Z.add (Z.mul (Z.mul limb 8) 256) (Z.mul window 256)) byte) 0 ( SM2_TABLE_RECORDS) ( sm2_table_flatten ( SM2_MONT_BASE_TABLE_DATA))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_mont_afpoint selected ( sm2_point_mul ( sm2_table_term byte limb window) ( SM2_G_POINT))))
    ).

Definition basepoint_table_points_strategy11 :=
  forall (selected : Z) (window : Z) (base : Z) (limb : Z) (byte : Z),
    TT &&
    (“ (record_afpoint_well_formed ( sm2_base_table_record_at limb window byte)) ”) &&
    (“ (Z.le 0 limb) ”) &&
    (“ (Z.lt limb 4) ”) &&
    (“ (Z.le 0 window) ”) &&
    (“ (Z.lt window 8) ”) &&
    (“ (Z.le 0 byte) ”) &&
    (“ (Z.lt byte 256) ”) &&
    (“ (selected = (Z.add (Z.add (Z.add base (Z.mul limb (Z.mul (Z.mul (@sizeof_front_end_type (FET_alias ("AFPoint"))) 256) 8))) (Z.mul window (Z.mul (@sizeof_front_end_type (FET_alias ("AFPoint"))) 256))) (Z.mul byte (@sizeof_front_end_type (FET_alias ("AFPoint")))))) ”) &&
    emp **
    ((StructAFPointArray.missing_i base (Z.add (Z.add (Z.mul (Z.mul limb 8) 256) (Z.mul window 256)) byte) 0 ( SM2_TABLE_RECORDS) ( sm2_table_flatten ( SM2_BASE_TABLE_DATA)))) **
    ((store_afpoint selected ( sm2_point_mul ( sm2_table_term byte limb window) ( SM2_G_POINT))))
    |--
    (
    TT &&
    emp **
    ((StructAFPointArray.full base ( SM2_TABLE_RECORDS) ( sm2_table_flatten ( SM2_BASE_TABLE_DATA))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition basepoint_table_points_strategy21 :=
  forall (selected : Z) (window : Z) (base : Z) (limb : Z) (byte : Z),
    TT &&
    (“ (record_afpoint_well_formed ( sm2_mont_base_table_record_at limb window byte)) ”) &&
    (“ (Z.le 0 limb) ”) &&
    (“ (Z.lt limb 4) ”) &&
    (“ (Z.le 0 window) ”) &&
    (“ (Z.lt window 8) ”) &&
    (“ (Z.le 0 byte) ”) &&
    (“ (Z.lt byte 256) ”) &&
    (“ (selected = (Z.add (Z.add (Z.add base (Z.mul limb (Z.mul (Z.mul (@sizeof_front_end_type (FET_alias ("AFPoint"))) 256) 8))) (Z.mul window (Z.mul (@sizeof_front_end_type (FET_alias ("AFPoint"))) 256))) (Z.mul byte (@sizeof_front_end_type (FET_alias ("AFPoint")))))) ”) &&
    emp **
    ((StructAFPointArray.missing_i base (Z.add (Z.add (Z.mul (Z.mul limb 8) 256) (Z.mul window 256)) byte) 0 ( SM2_TABLE_RECORDS) ( sm2_table_flatten ( SM2_MONT_BASE_TABLE_DATA)))) **
    ((store_mont_afpoint selected ( sm2_point_mul ( sm2_table_term byte limb window) ( SM2_G_POINT))))
    |--
    (
    TT &&
    emp **
    ((StructAFPointArray.full base ( SM2_TABLE_RECORDS) ( sm2_table_flatten ( SM2_MONT_BASE_TABLE_DATA))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type basepoint_table_points_Strategy_Correct.

  Axiom basepoint_table_points_strategy10_correctness : basepoint_table_points_strategy10.
  Axiom basepoint_table_points_strategy20_correctness : basepoint_table_points_strategy20.
  Axiom basepoint_table_points_strategy11_correctness : basepoint_table_points_strategy11.
  Axiom basepoint_table_points_strategy21_correctness : basepoint_table_points_strategy21.

End basepoint_table_points_Strategy_Correct.
