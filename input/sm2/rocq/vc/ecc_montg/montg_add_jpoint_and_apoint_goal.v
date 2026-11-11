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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.montg_add_jpoint_and_apoint_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_precompute_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_precompute_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_x_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_x_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_y_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_y_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_overwrite_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_overwrite_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_facts_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_facts_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_compare_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_compare_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_result_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_result_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_cleanup_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_and_apoint_cleanup_strategy_proof.

(*----- Function montg_add_jpoint_and_apoint -----*)

Definition montg_add_jpoint_and_apoint_safety_wit_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (P_r_eq_a = ECInfinity)) (PreH3 : (r_pre = a_pre)) (PreH4 : (retval = 0)) ,
  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (P_non_alias = ECInfinity)) (PreH3 : (retval = 0)) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_3_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (P_r_eq_a <> ECInfinity)) (PreH3 : (r_pre = a_pre)) (PreH4 : (retval <> 0)) ,
  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_4_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (P_non_alias <> ECInfinity)) (PreH3 : (retval <> 0)) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_5_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (retval = 1)) (PreH3 : (P_r_eq_a = ECInfinity)) (PreH4 : (r_pre = a_pre)) (PreH5 : (retval <> 0)) ,
  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_mont_jpoint r_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_6_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (retval = 1)) (PreH3 : (P_non_alias = ECInfinity)) (PreH4 : (retval <> 0)) ,
  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_mont_jpoint r_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_7_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (Q_r_eq_a = ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_r_eq_a <> ECInfinity)) (PreH5 : (r_pre = a_pre)) (PreH6 : (retval = 0)) (PreH7 : (retval_2 = 0)) ,
  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_8_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (Q_non_alias = ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval = 0)) (PreH6 : (retval_2 = 0)) ,
  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_9_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (Q_r_eq_a <> ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_r_eq_a <> ECInfinity)) (PreH5 : (r_pre = a_pre)) (PreH6 : (retval = 0)) (PreH7 : (retval_2 <> 0)) ,
  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_10_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (Q_non_alias <> ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval = 0)) (PreH6 : (retval_2 <> 0)) ,
  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_11_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (retval_2 = 1)) (PreH3 : (Q_r_eq_a = ECInfinity)) (PreH4 : (retval = 0)) (PreH5 : (P_r_eq_a <> ECInfinity)) (PreH6 : (r_pre = a_pre)) (PreH7 : (retval = 0)) (PreH8 : (retval_2 <> 0)) ,
  (store_mont_jpoint r_pre P_r_eq_a )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_12_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (Q_non_alias = ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval = 0)) (PreH6 : (retval_2 <> 0)) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_jpoint r_pre P_non_alias )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_13_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH2 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH5 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) (PreH14 : ((mont_p (BY)) < SM2_P_Z)) (PreH15 : (0 <= (mont_p (BY)))) (PreH16 : ((mont_p (BX)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BX)))) (PreH18 : (AZ <> 0)) (PreH19 : (AZ < SM2_P_Z)) (PreH20 : (0 <= AZ)) (PreH21 : (AY < SM2_P_Z)) (PreH22 : (0 <= AY)) (PreH23 : (AX < SM2_P_Z)) (PreH24 : (0 <= AX)) (PreH25 : (BY < SM2_P_Z)) (PreH26 : (0 <= BY)) (PreH27 : (BX < SM2_P_Z)) (PreH28 : (0 <= BX)) (PreH29 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH30 : (afpoint_represents BX BY Q_r_eq_a )) (PreH31 : (retval_2 = 0)) (PreH32 : (Q_r_eq_a <> ECInfinity)) (PreH33 : (retval = 0)) (PreH34 : (P_r_eq_a <> ECInfinity)) (PreH35 : (r_pre = a_pre)) (PreH36 : (retval = 0)) (PreH37 : (retval_2 = 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_14_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH2 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH5 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) (PreH14 : ((mont_p (BY)) < SM2_P_Z)) (PreH15 : (0 <= (mont_p (BY)))) (PreH16 : ((mont_p (BX)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BX)))) (PreH18 : (AZ <> 0)) (PreH19 : (AZ < SM2_P_Z)) (PreH20 : (0 <= AZ)) (PreH21 : (AY < SM2_P_Z)) (PreH22 : (0 <= AY)) (PreH23 : (AX < SM2_P_Z)) (PreH24 : (0 <= AX)) (PreH25 : (BY < SM2_P_Z)) (PreH26 : (0 <= BY)) (PreH27 : (BX < SM2_P_Z)) (PreH28 : (0 <= BX)) (PreH29 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH30 : (afpoint_represents BX BY Q_r_eq_a )) (PreH31 : (retval_2 = 0)) (PreH32 : (Q_r_eq_a <> ECInfinity)) (PreH33 : (retval = 0)) (PreH34 : (P_r_eq_a <> ECInfinity)) (PreH35 : (r_pre = a_pre)) (PreH36 : (retval = 0)) (PreH37 : (retval_2 = 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_15_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH2 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH5 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) (PreH14 : ((mont_p (BY)) < SM2_P_Z)) (PreH15 : (0 <= (mont_p (BY)))) (PreH16 : ((mont_p (BX)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BX)))) (PreH18 : (AZ <> 0)) (PreH19 : (AZ < SM2_P_Z)) (PreH20 : (0 <= AZ)) (PreH21 : (AY < SM2_P_Z)) (PreH22 : (0 <= AY)) (PreH23 : (AX < SM2_P_Z)) (PreH24 : (0 <= AX)) (PreH25 : (BY < SM2_P_Z)) (PreH26 : (0 <= BY)) (PreH27 : (BX < SM2_P_Z)) (PreH28 : (0 <= BX)) (PreH29 : (jpoint_represents AX AY AZ P_non_alias )) (PreH30 : (afpoint_represents BX BY Q_non_alias )) (PreH31 : (retval_2 = 0)) (PreH32 : (Q_non_alias <> ECInfinity)) (PreH33 : (retval = 0)) (PreH34 : (P_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (retval_2 = 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_16_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH2 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH5 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) (PreH14 : ((mont_p (BY)) < SM2_P_Z)) (PreH15 : (0 <= (mont_p (BY)))) (PreH16 : ((mont_p (BX)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BX)))) (PreH18 : (AZ <> 0)) (PreH19 : (AZ < SM2_P_Z)) (PreH20 : (0 <= AZ)) (PreH21 : (AY < SM2_P_Z)) (PreH22 : (0 <= AY)) (PreH23 : (AX < SM2_P_Z)) (PreH24 : (0 <= AX)) (PreH25 : (BY < SM2_P_Z)) (PreH26 : (0 <= BY)) (PreH27 : (BX < SM2_P_Z)) (PreH28 : (0 <= BX)) (PreH29 : (jpoint_represents AX AY AZ P_non_alias )) (PreH30 : (afpoint_represents BX BY Q_non_alias )) (PreH31 : (retval_2 = 0)) (PreH32 : (Q_non_alias <> ECInfinity)) (PreH33 : (retval = 0)) (PreH34 : (P_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (retval_2 = 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_17_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_18_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_19_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 <> 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_20_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 <> 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_21_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 <> 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_22_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 <> 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_23_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 <> 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_24_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 <> 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_25_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 1)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH3 : (retval_3 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH34 : (afpoint_represents BX BY Q_r_eq_a )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_r_eq_a <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_r_eq_a <> ECInfinity)) (PreH39 : (r_pre = a_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 = 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_26_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 1)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH3 : (retval_3 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_non_alias )) (PreH34 : (afpoint_represents BX BY Q_non_alias )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_non_alias <> ECInfinity)) (PreH39 : (retval = 0)) (PreH40 : (retval_2 = 0)) (PreH41 : (retval_3 <> 0)) (PreH42 : (retval_4 = 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_27_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH3 : (retval_3 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH34 : (afpoint_represents BX BY Q_r_eq_a )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_r_eq_a <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_r_eq_a <> ECInfinity)) (PreH39 : (r_pre = a_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 <> 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_28_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH3 : (retval_3 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_non_alias )) (PreH34 : (afpoint_represents BX BY Q_non_alias )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_non_alias <> ECInfinity)) (PreH39 : (retval = 0)) (PreH40 : (retval_2 = 0)) (PreH41 : (retval_3 <> 0)) (PreH42 : (retval_4 <> 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ False ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_29_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (P_r_eq_a = Q_r_eq_a)) (PreH3 : (retval_4 = 1)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH5 : (retval_3 = 1)) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH7 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH9 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH10 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH11 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : ((mont_p (BY)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BY)))) (PreH22 : ((mont_p (BX)) < SM2_P_Z)) (PreH23 : (0 <= (mont_p (BX)))) (PreH24 : (AZ <> 0)) (PreH25 : (AZ < SM2_P_Z)) (PreH26 : (0 <= AZ)) (PreH27 : (AY < SM2_P_Z)) (PreH28 : (0 <= AY)) (PreH29 : (AX < SM2_P_Z)) (PreH30 : (0 <= AX)) (PreH31 : (BY < SM2_P_Z)) (PreH32 : (0 <= BY)) (PreH33 : (BX < SM2_P_Z)) (PreH34 : (0 <= BX)) (PreH35 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH36 : (afpoint_represents BX BY Q_r_eq_a )) (PreH37 : (retval_2 = 0)) (PreH38 : (Q_r_eq_a <> ECInfinity)) (PreH39 : (retval = 0)) (PreH40 : (P_r_eq_a <> ECInfinity)) (PreH41 : (r_pre = a_pre)) (PreH42 : (retval = 0)) (PreH43 : (retval_2 = 0)) (PreH44 : (retval_3 <> 0)) (PreH45 : (retval_4 <> 0)) ,
  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_jpoint r_pre (sm2_point_double (P_r_eq_a)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_30_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (P_non_alias = Q_non_alias)) (PreH2 : (retval_4 = 1)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_non_alias )) (PreH35 : (afpoint_represents BX BY Q_non_alias )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_non_alias <> ECInfinity)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 <> 0)) ,
  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_double (P_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_31_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : ((sm2_point_add (P_r_eq_a) (Q_r_eq_a)) = ECInfinity)) (PreH2 : (retval_4 = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH35 : (afpoint_represents BX BY Q_r_eq_a )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_r_eq_a <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_r_eq_a <> ECInfinity)) (PreH40 : (r_pre = a_pre)) (PreH41 : (retval = 0)) (PreH42 : (retval_2 = 0)) (PreH43 : (retval_3 <> 0)) (PreH44 : (retval_4 = 0)) ,
  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_mont_jpoint r_pre ECInfinity )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_sm2_p )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_32_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : ((sm2_point_add (P_non_alias) (Q_non_alias)) = ECInfinity)) (PreH2 : (retval_4 = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_non_alias )) (PreH35 : (afpoint_represents BX BY Q_non_alias )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_non_alias <> ECInfinity)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 = 0)) ,
  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_mont_jpoint r_pre ECInfinity )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_33_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) )) (PreH2 : (&((r_pre)  # "JPoint" ->ₛ "z") = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y"))) (PreH4 : (retval_3 = 0)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH35 : (afpoint_represents BX BY Q_r_eq_a )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_r_eq_a <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_r_eq_a <> ECInfinity)) (PreH40 : (r_pre = a_pre)) (PreH41 : (retval = 0)) (PreH42 : (retval_2 = 0)) (PreH43 : (retval_3 = 0)) ,
  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_add_jpoint_and_apoint_safety_wit_34_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_non_alias) (Q_non_alias)) )) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_non_alias )) (PreH33 : (afpoint_represents BX BY Q_non_alias )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_non_alias <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_add_jpoint_and_apoint_entail_wit_1_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (P_r_eq_a <> ECInfinity)) (PreH3 : (r_pre = a_pre)) (PreH4 : (retval = 0)) ,
  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_1_2_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (P_r_eq_a = ECInfinity)) (PreH3 : (r_pre = a_pre)) (PreH4 : (retval_3 = 0)) ,
  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_1_3_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (P_non_alias <> ECInfinity)) (PreH3 : (retval_2 = 0)) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_1_4_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (P_non_alias = ECInfinity)) (PreH3 : (retval_3 = 0)) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_2_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (P_r_eq_a <> ECInfinity)) (PreH3 : (r_pre = a_pre)) (PreH4 : (retval_3 <> 0)) ,
  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (P_r_eq_a = ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 1) ” 
  &&  “ (P_non_alias = ECInfinity) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_2_2_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (P_r_eq_a = ECInfinity)) (PreH3 : (r_pre = a_pre)) (PreH4 : (retval <> 0)) ,
  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (retval = 1) ” 
  &&  “ (P_r_eq_a = ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 1) ” 
  &&  “ (P_non_alias = ECInfinity) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_2_3_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (P_non_alias <> ECInfinity)) (PreH3 : (retval_3 <> 0)) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (P_r_eq_a = ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 1) ” 
  &&  “ (P_non_alias = ECInfinity) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_2_4_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (P_non_alias = ECInfinity)) (PreH3 : (retval_2 <> 0)) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (P_r_eq_a = ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (retval_2 = 1) ” 
  &&  “ (P_non_alias = ECInfinity) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_3_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (Q_r_eq_a <> ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_r_eq_a <> ECInfinity)) (PreH5 : (r_pre = a_pre)) (PreH6 : (retval = 0)) (PreH7 : (retval_2 = 0)) ,
  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (retval_3: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_3_2_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_5: Z) (PreH1 : (retval_5 = 1)) (PreH2 : (Q_r_eq_a = ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_r_eq_a <> ECInfinity)) (PreH5 : (r_pre = a_pre)) (PreH6 : (retval = 0)) (PreH7 : (retval_5 = 0)) ,
  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (retval_3: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_3_3_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (Q_non_alias <> ECInfinity)) (PreH3 : (retval_3 = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval_3 = 0)) (PreH6 : (retval_4 = 0)) ,
  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (retval: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_3_4_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (retval_5: Z) (PreH1 : (retval_5 = 1)) (PreH2 : (Q_non_alias = ECInfinity)) (PreH3 : (retval_3 = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval_3 = 0)) (PreH6 : (retval_5 = 0)) ,
  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (retval: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_4_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (Q_r_eq_a <> ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_r_eq_a <> ECInfinity)) (PreH5 : (r_pre = a_pre)) (PreH6 : (retval = 0)) (PreH7 : (retval_5 <> 0)) ,
  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z) ,
  “ (retval_2 = 1) ” 
  &&  “ (Q_r_eq_a = ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (retval_3: Z) ,
  “ (retval_4 = 1) ” 
  &&  “ (Q_non_alias = ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_4_2_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (Q_r_eq_a = ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_r_eq_a <> ECInfinity)) (PreH5 : (r_pre = a_pre)) (PreH6 : (retval = 0)) (PreH7 : (retval_2 <> 0)) ,
  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (retval_2 = 1) ” 
  &&  “ (Q_r_eq_a = ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (retval_3: Z) ,
  “ (retval_4 = 1) ” 
  &&  “ (Q_non_alias = ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_4_3_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (Q_non_alias <> ECInfinity)) (PreH3 : (retval_3 = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval_3 = 0)) (PreH6 : (retval_5 <> 0)) ,
  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (retval: Z) ,
  “ (retval_2 = 1) ” 
  &&  “ (Q_r_eq_a = ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (retval_4 = 1) ” 
  &&  “ (Q_non_alias = ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_4_4_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 1)) (PreH2 : (Q_non_alias = ECInfinity)) (PreH3 : (retval_3 = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval_3 = 0)) (PreH6 : (retval_4 <> 0)) ,
  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (retval: Z) ,
  “ (retval_2 = 1) ” 
  &&  “ (Q_r_eq_a = ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (retval_4 = 1) ” 
  &&  “ (Q_non_alias = ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_5_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (Q_r_eq_a <> ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_r_eq_a <> ECInfinity)) (PreH5 : (r_pre = a_pre)) (PreH6 : (retval = 0)) (PreH7 : (retval_2 = 0)) ,
  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (y: Z)  (x: Z) ,
  “ (afpoint_represents x y Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_afpoint_coords b_pre x y )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (y_2: Z)  (x_2: Z)  (retval_4: Z)  (retval_3: Z) ,
  “ (afpoint_represents x_2 y_2 Q_non_alias ) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_mont_afpoint_coords b_pre x_2 y_2 )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_5_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (Q_non_alias <> ECInfinity)) (PreH3 : (retval_3 = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval_3 = 0)) (PreH6 : (retval_4 = 0)) ,
  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (y: Z)  (x: Z)  (retval_2: Z)  (retval: Z) ,
  “ (afpoint_represents x y Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_afpoint_coords b_pre x y )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (y_2: Z)  (x_2: Z) ,
  “ (afpoint_represents x_2 y_2 Q_non_alias ) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_mont_afpoint_coords b_pre x_2 y_2 )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_6_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (PreH1 : (afpoint_represents x y Q_r_eq_a )) (PreH2 : (retval_2 = 0)) (PreH3 : (Q_r_eq_a <> ECInfinity)) (PreH4 : (retval = 0)) (PreH5 : (P_r_eq_a <> ECInfinity)) (PreH6 : (r_pre = a_pre)) (PreH7 : (retval = 0)) (PreH8 : (retval_2 = 0)) ,
  (store_mont_afpoint_coords b_pre x y )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (z: Z)  (y_2: Z)  (x_2: Z) ,
  “ (jpoint_represents x_2 y_2 z P_r_eq_a ) ” 
  &&  “ (afpoint_represents x y Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_jpoint_coords a_pre x_2 y_2 z )
  **  (store_mont_afpoint_coords b_pre x y )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (z_2: Z)  (y_4: Z)  (x_4: Z)  (y_3: Z)  (x_3: Z)  (retval_4: Z)  (retval_3: Z) ,
  “ (jpoint_represents x_4 y_4 z_2 P_non_alias ) ” 
  &&  “ (afpoint_represents x_3 y_3 Q_non_alias ) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_mont_jpoint_coords a_pre x_4 y_4 z_2 )
  **  (store_mont_afpoint_coords b_pre x_3 y_3 )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_6_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (retval_4: Z) (x_3: Z) (y_3: Z) (PreH1 : (afpoint_represents x_3 y_3 Q_non_alias )) (PreH2 : (retval_4 = 0)) (PreH3 : (Q_non_alias <> ECInfinity)) (PreH4 : (retval_3 = 0)) (PreH5 : (P_non_alias <> ECInfinity)) (PreH6 : (retval_3 = 0)) (PreH7 : (retval_4 = 0)) ,
  (store_mont_afpoint_coords b_pre x_3 y_3 )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (z: Z)  (y_2: Z)  (x_2: Z)  (y: Z)  (x: Z)  (retval_2: Z)  (retval: Z) ,
  “ (jpoint_represents x_2 y_2 z P_r_eq_a ) ” 
  &&  “ (afpoint_represents x y Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_jpoint_coords a_pre x_2 y_2 z )
  **  (store_mont_afpoint_coords b_pre x y )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (z_2: Z)  (y_4: Z)  (x_4: Z) ,
  “ (jpoint_represents x_4 y_4 z_2 P_non_alias ) ” 
  &&  “ (afpoint_represents x_3 y_3 Q_non_alias ) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_mont_jpoint_coords a_pre x_4 y_4 z_2 )
  **  (store_mont_afpoint_coords b_pre x_3 y_3 )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_7_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (z: Z) (PreH1 : (jpoint_represents x_2 y_2 z P_r_eq_a )) (PreH2 : (afpoint_represents x y Q_r_eq_a )) (PreH3 : (retval_2 = 0)) (PreH4 : (Q_r_eq_a <> ECInfinity)) (PreH5 : (retval = 0)) (PreH6 : (P_r_eq_a <> ECInfinity)) (PreH7 : (r_pre = a_pre)) (PreH8 : (retval = 0)) (PreH9 : (retval_2 = 0)) ,
  (store_mont_jpoint_coords a_pre x_2 y_2 z )
  **  (store_mont_afpoint_coords b_pre x y )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (jpoint_represents x_2 y_2 z P_r_eq_a ) ” 
  &&  “ (afpoint_represents x y Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_afpoint_fields b_pre (mont_p (x)) (mont_p (y)) )
  **  (store_mont_jpoint_coords a_pre x_2 y_2 z )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (z_2: Z)  (y_4: Z)  (x_4: Z)  (y_3: Z)  (x_3: Z)  (retval_4: Z)  (retval_3: Z) ,
  “ (y_3 < SM2_P_Z) ” 
  &&  “ (0 <= y_3) ” 
  &&  “ (x_3 < SM2_P_Z) ” 
  &&  “ (0 <= x_3) ” 
  &&  “ (jpoint_represents x_4 y_4 z_2 P_non_alias ) ” 
  &&  “ (afpoint_represents x_3 y_3 Q_non_alias ) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_afpoint_fields b_pre (mont_p (x_3)) (mont_p (y_3)) )
  **  (store_mont_jpoint_coords a_pre x_4 y_4 z_2 )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_7_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (retval_4: Z) (x_3: Z) (y_3: Z) (x_4: Z) (y_4: Z) (z_2: Z) (PreH1 : (jpoint_represents x_4 y_4 z_2 P_non_alias )) (PreH2 : (afpoint_represents x_3 y_3 Q_non_alias )) (PreH3 : (retval_4 = 0)) (PreH4 : (Q_non_alias <> ECInfinity)) (PreH5 : (retval_3 = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval_3 = 0)) (PreH8 : (retval_4 = 0)) ,
  (store_mont_jpoint_coords a_pre x_4 y_4 z_2 )
  **  (store_mont_afpoint_coords b_pre x_3 y_3 )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (z: Z)  (y_2: Z)  (x_2: Z)  (y: Z)  (x: Z)  (retval_2: Z)  (retval: Z) ,
  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (jpoint_represents x_2 y_2 z P_r_eq_a ) ” 
  &&  “ (afpoint_represents x y Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_afpoint_fields b_pre (mont_p (x)) (mont_p (y)) )
  **  (store_mont_jpoint_coords a_pre x_2 y_2 z )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (y_3 < SM2_P_Z) ” 
  &&  “ (0 <= y_3) ” 
  &&  “ (x_3 < SM2_P_Z) ” 
  &&  “ (0 <= x_3) ” 
  &&  “ (jpoint_represents x_4 y_4 z_2 P_non_alias ) ” 
  &&  “ (afpoint_represents x_3 y_3 Q_non_alias ) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_afpoint_fields b_pre (mont_p (x_3)) (mont_p (y_3)) )
  **  (store_mont_jpoint_coords a_pre x_4 y_4 z_2 )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_8_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (z: Z) (PreH1 : (y < SM2_P_Z)) (PreH2 : (0 <= y)) (PreH3 : (x < SM2_P_Z)) (PreH4 : (0 <= x)) (PreH5 : (jpoint_represents x_2 y_2 z P_r_eq_a )) (PreH6 : (afpoint_represents x y Q_r_eq_a )) (PreH7 : (retval_2 = 0)) (PreH8 : (Q_r_eq_a <> ECInfinity)) (PreH9 : (retval = 0)) (PreH10 : (P_r_eq_a <> ECInfinity)) (PreH11 : (r_pre = a_pre)) (PreH12 : (retval = 0)) (PreH13 : (retval_2 = 0)) ,
  (store_afpoint_fields b_pre (mont_p (x)) (mont_p (y)) )
  **  (store_mont_jpoint_coords a_pre x_2 y_2 z )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (jpoint_represents x_2 y_2 z P_r_eq_a ) ” 
  &&  “ (afpoint_represents x y Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_fields a_pre (mont_p (x_2)) (mont_p (y_2)) (mont_p (z)) )
  **  (store_afpoint_fields b_pre (mont_p (x)) (mont_p (y)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (z_2: Z)  (y_4: Z)  (x_4: Z)  (y_3: Z)  (x_3: Z)  (retval_4: Z)  (retval_3: Z) ,
  “ (z_2 < SM2_P_Z) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (y_4 < SM2_P_Z) ” 
  &&  “ (0 <= y_4) ” 
  &&  “ (x_4 < SM2_P_Z) ” 
  &&  “ (0 <= x_4) ” 
  &&  “ (y_3 < SM2_P_Z) ” 
  &&  “ (0 <= y_3) ” 
  &&  “ (x_3 < SM2_P_Z) ” 
  &&  “ (0 <= x_3) ” 
  &&  “ (jpoint_represents x_4 y_4 z_2 P_non_alias ) ” 
  &&  “ (afpoint_represents x_3 y_3 Q_non_alias ) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_jpoint_fields a_pre (mont_p (x_4)) (mont_p (y_4)) (mont_p (z_2)) )
  **  (store_afpoint_fields b_pre (mont_p (x_3)) (mont_p (y_3)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_8_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (retval_4: Z) (x_3: Z) (y_3: Z) (x_4: Z) (y_4: Z) (z_2: Z) (PreH1 : (y_3 < SM2_P_Z)) (PreH2 : (0 <= y_3)) (PreH3 : (x_3 < SM2_P_Z)) (PreH4 : (0 <= x_3)) (PreH5 : (jpoint_represents x_4 y_4 z_2 P_non_alias )) (PreH6 : (afpoint_represents x_3 y_3 Q_non_alias )) (PreH7 : (retval_4 = 0)) (PreH8 : (Q_non_alias <> ECInfinity)) (PreH9 : (retval_3 = 0)) (PreH10 : (P_non_alias <> ECInfinity)) (PreH11 : (retval_3 = 0)) (PreH12 : (retval_4 = 0)) ,
  (store_afpoint_fields b_pre (mont_p (x_3)) (mont_p (y_3)) )
  **  (store_mont_jpoint_coords a_pre x_4 y_4 z_2 )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (z: Z)  (y_2: Z)  (x_2: Z)  (y: Z)  (x: Z)  (retval_2: Z)  (retval: Z) ,
  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (jpoint_represents x_2 y_2 z P_r_eq_a ) ” 
  &&  “ (afpoint_represents x y Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_fields a_pre (mont_p (x_2)) (mont_p (y_2)) (mont_p (z)) )
  **  (store_afpoint_fields b_pre (mont_p (x)) (mont_p (y)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (z_2 < SM2_P_Z) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (y_4 < SM2_P_Z) ” 
  &&  “ (0 <= y_4) ” 
  &&  “ (x_4 < SM2_P_Z) ” 
  &&  “ (0 <= x_4) ” 
  &&  “ (y_3 < SM2_P_Z) ” 
  &&  “ (0 <= y_3) ” 
  &&  “ (x_3 < SM2_P_Z) ” 
  &&  “ (0 <= x_3) ” 
  &&  “ (jpoint_represents x_4 y_4 z_2 P_non_alias ) ” 
  &&  “ (afpoint_represents x_3 y_3 Q_non_alias ) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_jpoint_fields a_pre (mont_p (x_4)) (mont_p (y_4)) (mont_p (z_2)) )
  **  (store_afpoint_fields b_pre (mont_p (x_3)) (mont_p (y_3)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_9_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : (AZ < SM2_P_Z)) (PreH2 : (0 <= AZ)) (PreH3 : (AY < SM2_P_Z)) (PreH4 : (0 <= AY)) (PreH5 : (AX < SM2_P_Z)) (PreH6 : (0 <= AX)) (PreH7 : (BY < SM2_P_Z)) (PreH8 : (0 <= BY)) (PreH9 : (BX < SM2_P_Z)) (PreH10 : (0 <= BX)) (PreH11 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH12 : (afpoint_represents BX BY Q_r_eq_a )) (PreH13 : (retval_2 = 0)) (PreH14 : (Q_r_eq_a <> ECInfinity)) (PreH15 : (retval = 0)) (PreH16 : (P_r_eq_a <> ECInfinity)) (PreH17 : (r_pre = a_pre)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_jpoint_fields a_pre (mont_p (AX)) (mont_p (AY)) (mont_p (AZ)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_fields a_pre (mont_p (AX)) (mont_p (AY)) (mont_p (AZ)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (retval_3: Z) ,
  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_jpoint_fields a_pre (mont_p (AX)) (mont_p (AY)) (mont_p (AZ)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_9_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (retval_4: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : (AZ < SM2_P_Z)) (PreH2 : (0 <= AZ)) (PreH3 : (AY < SM2_P_Z)) (PreH4 : (0 <= AY)) (PreH5 : (AX < SM2_P_Z)) (PreH6 : (0 <= AX)) (PreH7 : (BY < SM2_P_Z)) (PreH8 : (0 <= BY)) (PreH9 : (BX < SM2_P_Z)) (PreH10 : (0 <= BX)) (PreH11 : (jpoint_represents AX AY AZ P_non_alias )) (PreH12 : (afpoint_represents BX BY Q_non_alias )) (PreH13 : (retval_4 = 0)) (PreH14 : (Q_non_alias <> ECInfinity)) (PreH15 : (retval_3 = 0)) (PreH16 : (P_non_alias <> ECInfinity)) (PreH17 : (retval_3 = 0)) (PreH18 : (retval_4 = 0)) ,
  (store_jpoint_fields a_pre (mont_p (AX)) (mont_p (AY)) (mont_p (AZ)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (retval: Z) ,
  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_fields a_pre (mont_p (AX)) (mont_p (AY)) (mont_p (AZ)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_jpoint_fields a_pre (mont_p (AX)) (mont_p (AY)) (mont_p (AZ)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_10_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH17 : (afpoint_represents BX BY Q_r_eq_a )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_r_eq_a <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_r_eq_a <> ECInfinity)) (PreH22 : (r_pre = a_pre)) (PreH23 : (retval = 0)) (PreH24 : (retval_2 = 0)) ,
  (store_u256_limbs ( &( "BN_ZERO" ) ) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "D" ) ) (Zmod (((mont_p ((maja_s2 (BY) (AZ)))) - (mont_p (AY)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "D" ) ) (Zmod (((mont_p ((maja_s2 (BY) (AZ)))) - (mont_p (AY)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_3: Z)  (retval_4: Z) ,
  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "D" ) ) (Zmod (((mont_p ((maja_s2 (BY) (AZ)))) - (mont_p (AY)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_10_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (retval_4: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_non_alias )) (PreH17 : (afpoint_represents BX BY Q_non_alias )) (PreH18 : (retval_4 = 0)) (PreH19 : (Q_non_alias <> ECInfinity)) (PreH20 : (retval_3 = 0)) (PreH21 : (P_non_alias <> ECInfinity)) (PreH22 : (retval_3 = 0)) (PreH23 : (retval_4 = 0)) ,
  (store_u256_limbs ( &( "BN_ZERO" ) ) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "D" ) ) (Zmod (((mont_p ((maja_s2 (BY) (AZ)))) - (mont_p (AY)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "D" ) ) (Zmod (((mont_p ((maja_s2 (BY) (AZ)))) - (mont_p (AY)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "D" ) ) (Zmod (((mont_p ((maja_s2 (BY) (AZ)))) - (mont_p (AY)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_11_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : ((mont_p (BY)) < SM2_P_Z)) (PreH11 : (0 <= (mont_p (BY)))) (PreH12 : ((mont_p (BX)) < SM2_P_Z)) (PreH13 : (0 <= (mont_p (BX)))) (PreH14 : (AZ <> 0)) (PreH15 : (AZ < SM2_P_Z)) (PreH16 : (0 <= AZ)) (PreH17 : (AY < SM2_P_Z)) (PreH18 : (0 <= AY)) (PreH19 : (AX < SM2_P_Z)) (PreH20 : (0 <= AX)) (PreH21 : (BY < SM2_P_Z)) (PreH22 : (0 <= BY)) (PreH23 : (BX < SM2_P_Z)) (PreH24 : (0 <= BX)) (PreH25 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH26 : (afpoint_represents BX BY Q_r_eq_a )) (PreH27 : (retval_2 = 0)) (PreH28 : (Q_r_eq_a <> ECInfinity)) (PreH29 : (retval = 0)) (PreH30 : (P_r_eq_a <> ECInfinity)) (PreH31 : (r_pre = a_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 = 0)) ,
  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "D" ) ) (Zmod (((mont_p ((maja_s2 (BY) (AZ)))) - (mont_p (AY)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  (“ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_3: Z)  (retval_4: Z) ,
  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_11_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_3: Z) (retval_4: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : ((mont_p (BY)) < SM2_P_Z)) (PreH11 : (0 <= (mont_p (BY)))) (PreH12 : ((mont_p (BX)) < SM2_P_Z)) (PreH13 : (0 <= (mont_p (BX)))) (PreH14 : (AZ <> 0)) (PreH15 : (AZ < SM2_P_Z)) (PreH16 : (0 <= AZ)) (PreH17 : (AY < SM2_P_Z)) (PreH18 : (0 <= AY)) (PreH19 : (AX < SM2_P_Z)) (PreH20 : (0 <= AX)) (PreH21 : (BY < SM2_P_Z)) (PreH22 : (0 <= BY)) (PreH23 : (BX < SM2_P_Z)) (PreH24 : (0 <= BX)) (PreH25 : (jpoint_represents AX AY AZ P_non_alias )) (PreH26 : (afpoint_represents BX BY Q_non_alias )) (PreH27 : (retval_4 = 0)) (PreH28 : (Q_non_alias <> ECInfinity)) (PreH29 : (retval_3 = 0)) (PreH30 : (P_non_alias <> ECInfinity)) (PreH31 : (retval_3 = 0)) (PreH32 : (retval_4 = 0)) ,
  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "D" ) ) (Zmod (((mont_p ((maja_s2 (BY) (AZ)))) - (mont_p (AY)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (“ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_12_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  (“ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (EX (retval_6: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_4: Z)  (retval_5: Z) ,
  “ (retval_6 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_12_2_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_7: Z) (PreH1 : (retval_7 = 1)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_7 = 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  (EX (retval_3: Z) ,
  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (EX (retval_6: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_4: Z)  (retval_5: Z) ,
  “ (retval_6 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_12_3_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_4: Z) (retval_5: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_6: Z) (PreH1 : (retval_6 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_5 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval_4 = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval_4 = 0)) (PreH38 : (retval_5 = 0)) (PreH39 : (retval_6 = 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval_3: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (“ (retval_6 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_12_4_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_4: Z) (retval_5: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_7: Z) (PreH1 : (retval_7 = 1)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_5 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval_4 = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval_4 = 0)) (PreH38 : (retval_5 = 0)) (PreH39 : (retval_7 = 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval_3: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (EX (retval_6: Z) ,
  “ (retval_6 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_13_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_7: Z) (PreH1 : (retval_7 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_7 <> 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  (EX (retval_3: Z) ,
  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (EX (retval_6: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_4: Z)  (retval_5: Z) ,
  “ (retval_6 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 <> 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_13_2_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 <> 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  (“ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (EX (retval_6: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_4: Z)  (retval_5: Z) ,
  “ (retval_6 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 <> 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_13_3_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_4: Z) (retval_5: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_7: Z) (PreH1 : (retval_7 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_5 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval_4 = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval_4 = 0)) (PreH38 : (retval_5 = 0)) (PreH39 : (retval_7 <> 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval_3: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (EX (retval_6: Z) ,
  “ (retval_6 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 <> 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_13_4_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_4: Z) (retval_5: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_6: Z) (PreH1 : (retval_6 = 1)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_5 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval_4 = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval_4 = 0)) (PreH38 : (retval_5 = 0)) (PreH39 : (retval_6 <> 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval_3: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (“ (retval_6 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 <> 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_14_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH3 : (retval_3 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH34 : (afpoint_represents BX BY Q_r_eq_a )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_r_eq_a <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_r_eq_a <> ECInfinity)) (PreH39 : (r_pre = a_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 = 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  (“ (retval_4 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (EX (retval_8: Z)  (retval_7: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_5: Z)  (retval_6: Z) ,
  “ (retval_8 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_14_2_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_9: Z) (PreH1 : (retval_9 = 1)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH3 : (retval_3 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH34 : (afpoint_represents BX BY Q_r_eq_a )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_r_eq_a <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_r_eq_a <> ECInfinity)) (PreH39 : (r_pre = a_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_9 = 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  (EX (retval_4: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (EX (retval_8: Z)  (retval_7: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_5: Z)  (retval_6: Z) ,
  “ (retval_8 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_14_3_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_5: Z) (retval_6: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 0)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH3 : (retval_7 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_non_alias )) (PreH34 : (afpoint_represents BX BY Q_non_alias )) (PreH35 : (retval_6 = 0)) (PreH36 : (Q_non_alias <> ECInfinity)) (PreH37 : (retval_5 = 0)) (PreH38 : (P_non_alias <> ECInfinity)) (PreH39 : (retval_5 = 0)) (PreH40 : (retval_6 = 0)) (PreH41 : (retval_7 <> 0)) (PreH42 : (retval_8 = 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval_4: Z)  (retval_3: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (“ (retval_8 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_14_4_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_5: Z) (retval_6: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_7: Z) (retval_9: Z) (PreH1 : (retval_9 = 1)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH3 : (retval_7 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_non_alias )) (PreH34 : (afpoint_represents BX BY Q_non_alias )) (PreH35 : (retval_6 = 0)) (PreH36 : (Q_non_alias <> ECInfinity)) (PreH37 : (retval_5 = 0)) (PreH38 : (P_non_alias <> ECInfinity)) (PreH39 : (retval_5 = 0)) (PreH40 : (retval_6 = 0)) (PreH41 : (retval_7 <> 0)) (PreH42 : (retval_9 = 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval_4: Z)  (retval_3: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (EX (retval_8: Z) ,
  “ (retval_8 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_15_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_9: Z) (PreH1 : (retval_9 = 0)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH3 : (retval_3 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH34 : (afpoint_represents BX BY Q_r_eq_a )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_r_eq_a <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_r_eq_a <> ECInfinity)) (PreH39 : (r_pre = a_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_9 <> 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  (EX (retval_4: Z) ,
  “ (retval_4 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (EX (retval_8: Z)  (retval_7: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_5: Z)  (retval_6: Z) ,
  “ (retval_8 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 <> 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_15_2_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 1)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH3 : (retval_3 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH34 : (afpoint_represents BX BY Q_r_eq_a )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_r_eq_a <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_r_eq_a <> ECInfinity)) (PreH39 : (r_pre = a_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 <> 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  (“ (retval_4 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (EX (retval_8: Z)  (retval_7: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_5: Z)  (retval_6: Z) ,
  “ (retval_8 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 <> 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_15_3_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_5: Z) (retval_6: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_7: Z) (retval_9: Z) (PreH1 : (retval_9 = 0)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH3 : (retval_7 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_non_alias )) (PreH34 : (afpoint_represents BX BY Q_non_alias )) (PreH35 : (retval_6 = 0)) (PreH36 : (Q_non_alias <> ECInfinity)) (PreH37 : (retval_5 = 0)) (PreH38 : (P_non_alias <> ECInfinity)) (PreH39 : (retval_5 = 0)) (PreH40 : (retval_6 = 0)) (PreH41 : (retval_7 <> 0)) (PreH42 : (retval_9 <> 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval_4: Z)  (retval_3: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ (retval_4 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (EX (retval_8: Z) ,
  “ (retval_8 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 <> 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_15_4_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_5: Z) (retval_6: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 1)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH3 : (retval_7 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_non_alias )) (PreH34 : (afpoint_represents BX BY Q_non_alias )) (PreH35 : (retval_6 = 0)) (PreH36 : (Q_non_alias <> ECInfinity)) (PreH37 : (retval_5 = 0)) (PreH38 : (P_non_alias <> ECInfinity)) (PreH39 : (retval_5 = 0)) (PreH40 : (retval_6 = 0)) (PreH41 : (retval_7 <> 0)) (PreH42 : (retval_8 <> 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval_4: Z)  (retval_3: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ (retval_4 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one ))
  ||
  (“ (retval_8 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 <> 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_16_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 1)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH3 : (retval_3 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH34 : (afpoint_represents BX BY Q_r_eq_a )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_r_eq_a <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_r_eq_a <> ECInfinity)) (PreH39 : (r_pre = a_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 <> 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  (“ (retval_4 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (EX (retval_8: Z)  (retval_7: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_5: Z)  (retval_6: Z) ,
  “ (retval_8 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 <> 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_16_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_5: Z) (retval_6: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 1)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH3 : (retval_7 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_non_alias )) (PreH34 : (afpoint_represents BX BY Q_non_alias )) (PreH35 : (retval_6 = 0)) (PreH36 : (Q_non_alias <> ECInfinity)) (PreH37 : (retval_5 = 0)) (PreH38 : (P_non_alias <> ECInfinity)) (PreH39 : (retval_5 = 0)) (PreH40 : (retval_6 = 0)) (PreH41 : (retval_7 <> 0)) (PreH42 : (retval_8 <> 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval_4: Z)  (retval_3: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ (retval_4 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (“ (retval_8 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 <> 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_17_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 1)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH3 : (retval_3 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH34 : (afpoint_represents BX BY Q_r_eq_a )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_r_eq_a <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_r_eq_a <> ECInfinity)) (PreH39 : (r_pre = a_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 <> 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  (“ (P_r_eq_a = Q_r_eq_a) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (EX (retval_8: Z)  (retval_7: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_5: Z)  (retval_6: Z) ,
  “ (P_non_alias = Q_non_alias) ” 
  &&  “ (retval_8 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 <> 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_17_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_5: Z) (retval_6: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 1)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH3 : (retval_7 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_non_alias )) (PreH34 : (afpoint_represents BX BY Q_non_alias )) (PreH35 : (retval_6 = 0)) (PreH36 : (Q_non_alias <> ECInfinity)) (PreH37 : (retval_5 = 0)) (PreH38 : (P_non_alias <> ECInfinity)) (PreH39 : (retval_5 = 0)) (PreH40 : (retval_6 = 0)) (PreH41 : (retval_7 <> 0)) (PreH42 : (retval_8 <> 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval_4: Z)  (retval_3: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ (P_r_eq_a = Q_r_eq_a) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (“ (P_non_alias = Q_non_alias) ” 
  &&  “ (retval_8 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 <> 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_18_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (P_r_eq_a = Q_r_eq_a)) (PreH3 : (retval_4 = 1)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH5 : (retval_3 = 1)) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH7 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH9 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH10 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH11 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : ((mont_p (BY)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BY)))) (PreH22 : ((mont_p (BX)) < SM2_P_Z)) (PreH23 : (0 <= (mont_p (BX)))) (PreH24 : (AZ <> 0)) (PreH25 : (AZ < SM2_P_Z)) (PreH26 : (0 <= AZ)) (PreH27 : (AY < SM2_P_Z)) (PreH28 : (0 <= AY)) (PreH29 : (AX < SM2_P_Z)) (PreH30 : (0 <= AX)) (PreH31 : (BY < SM2_P_Z)) (PreH32 : (0 <= BY)) (PreH33 : (BX < SM2_P_Z)) (PreH34 : (0 <= BX)) (PreH35 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH36 : (afpoint_represents BX BY Q_r_eq_a )) (PreH37 : (retval_2 = 0)) (PreH38 : (Q_r_eq_a <> ECInfinity)) (PreH39 : (retval = 0)) (PreH40 : (P_r_eq_a <> ECInfinity)) (PreH41 : (r_pre = a_pre)) (PreH42 : (retval = 0)) (PreH43 : (retval_2 = 0)) (PreH44 : (retval_3 <> 0)) (PreH45 : (retval_4 <> 0)) ,
  (store_mont_jpoint r_pre (sm2_point_double (P_r_eq_a)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  (“ (r_pre = a_pre) ” 
  &&  “ (P_r_eq_a = Q_r_eq_a) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_jpoint r_pre (sm2_point_double (P_r_eq_a)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (EX (retval_5: Z)  (retval_6: Z)  (x0_2: Z)  (x1_2: Z)  (x2_2: Z)  (x3_2: Z)  (retval_7: Z)  (retval_8: Z) ,
  “ (P_non_alias = Q_non_alias) ” 
  &&  “ (retval_8 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 <> 0) ”
  &&  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_double (P_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_18_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_5: Z) (retval_6: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (P_non_alias = Q_non_alias)) (PreH2 : (retval_8 = 1)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH4 : (retval_7 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_non_alias )) (PreH35 : (afpoint_represents BX BY Q_non_alias )) (PreH36 : (retval_6 = 0)) (PreH37 : (Q_non_alias <> ECInfinity)) (PreH38 : (retval_5 = 0)) (PreH39 : (P_non_alias <> ECInfinity)) (PreH40 : (retval_5 = 0)) (PreH41 : (retval_6 = 0)) (PreH42 : (retval_7 <> 0)) (PreH43 : (retval_8 <> 0)) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_double (P_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  (EX (retval: Z)  (retval_2: Z)  (x0: Z)  (x1: Z)  (x2: Z)  (x3: Z)  (retval_3: Z)  (retval_4: Z) ,
  “ (r_pre = a_pre) ” 
  &&  “ (P_r_eq_a = Q_r_eq_a) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_jpoint r_pre (sm2_point_double (P_r_eq_a)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (“ (P_non_alias = Q_non_alias) ” 
  &&  “ (retval_8 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 <> 0) ”
  &&  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_double (P_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_19_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH3 : (retval_3 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH34 : (afpoint_represents BX BY Q_r_eq_a )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_r_eq_a <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_r_eq_a <> ECInfinity)) (PreH39 : (r_pre = a_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 = 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  (“ (retval_4 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (EX (retval_8: Z)  (retval_7: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_5: Z)  (retval_6: Z) ,
  “ (retval_8 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_19_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_5: Z) (retval_6: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 0)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH3 : (retval_7 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_non_alias )) (PreH34 : (afpoint_represents BX BY Q_non_alias )) (PreH35 : (retval_6 = 0)) (PreH36 : (Q_non_alias <> ECInfinity)) (PreH37 : (retval_5 = 0)) (PreH38 : (P_non_alias <> ECInfinity)) (PreH39 : (retval_5 = 0)) (PreH40 : (retval_6 = 0)) (PreH41 : (retval_7 <> 0)) (PreH42 : (retval_8 = 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval_4: Z)  (retval_3: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (“ (retval_8 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_20_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH3 : (retval_3 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH34 : (afpoint_represents BX BY Q_r_eq_a )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_r_eq_a <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_r_eq_a <> ECInfinity)) (PreH39 : (r_pre = a_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  (“ ((sm2_point_add (P_r_eq_a) (Q_r_eq_a)) = ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (EX (retval_8: Z)  (retval_7: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_5: Z)  (retval_6: Z) ,
  “ ((sm2_point_add (P_non_alias) (Q_non_alias)) = ECInfinity) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_20_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_5: Z) (retval_6: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 0)) (PreH2 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH3 : (retval_7 = 1)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_non_alias )) (PreH34 : (afpoint_represents BX BY Q_non_alias )) (PreH35 : (retval_6 = 0)) (PreH36 : (Q_non_alias <> ECInfinity)) (PreH37 : (retval_5 = 0)) (PreH38 : (P_non_alias <> ECInfinity)) (PreH39 : (retval_5 = 0)) (PreH40 : (retval_6 = 0)) (PreH41 : (retval_7 <> 0)) (PreH42 : (retval_8 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval_4: Z)  (retval_3: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ ((sm2_point_add (P_r_eq_a) (Q_r_eq_a)) = ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (“ ((sm2_point_add (P_non_alias) (Q_non_alias)) = ECInfinity) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_21_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : ((sm2_point_add (P_r_eq_a) (Q_r_eq_a)) = ECInfinity)) (PreH2 : (retval_4 = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH35 : (afpoint_represents BX BY Q_r_eq_a )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_r_eq_a <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_r_eq_a <> ECInfinity)) (PreH40 : (r_pre = a_pre)) (PreH41 : (retval = 0)) (PreH42 : (retval_2 = 0)) (PreH43 : (retval_3 <> 0)) (PreH44 : (retval_4 = 0)) ,
  (store_montg_one )
  **  (store_mont_jpoint r_pre ECInfinity )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((sm2_point_add (P_r_eq_a) (Q_r_eq_a)) = ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_mont_jpoint r_pre ECInfinity )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_sm2_p )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (EX (retval_5: Z)  (retval_6: Z)  (x0_2: Z)  (x1_2: Z)  (x2_2: Z)  (x3_2: Z)  (retval_7: Z)  (retval_8: Z) ,
  “ ((sm2_point_add (P_non_alias) (Q_non_alias)) = ECInfinity) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_mont_jpoint r_pre ECInfinity )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
.

Definition montg_add_jpoint_and_apoint_entail_wit_21_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_5: Z) (retval_6: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_7: Z) (retval_8: Z) (PreH1 : ((sm2_point_add (P_non_alias) (Q_non_alias)) = ECInfinity)) (PreH2 : (retval_8 = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH4 : (retval_7 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_non_alias )) (PreH35 : (afpoint_represents BX BY Q_non_alias )) (PreH36 : (retval_6 = 0)) (PreH37 : (Q_non_alias <> ECInfinity)) (PreH38 : (retval_5 = 0)) (PreH39 : (P_non_alias <> ECInfinity)) (PreH40 : (retval_5 = 0)) (PreH41 : (retval_6 = 0)) (PreH42 : (retval_7 <> 0)) (PreH43 : (retval_8 = 0)) ,
  (store_montg_one )
  **  (store_mont_jpoint r_pre ECInfinity )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (EX (retval: Z)  (retval_2: Z)  (x0: Z)  (x1: Z)  (x2: Z)  (x3: Z)  (retval_3: Z)  (retval_4: Z) ,
  “ ((sm2_point_add (P_r_eq_a) (Q_r_eq_a)) = ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_mont_jpoint r_pre ECInfinity )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_sm2_p )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((sm2_point_add (P_non_alias) (Q_non_alias)) = ECInfinity) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_mont_jpoint r_pre ECInfinity )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
.

Definition montg_add_jpoint_and_apoint_entail_wit_22_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  (“ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (EX (retval_6: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_4: Z)  (retval_5: Z) ,
  “ (retval_6 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_22_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_4: Z) (retval_5: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_6: Z) (PreH1 : (retval_6 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_5 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval_4 = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval_4 = 0)) (PreH38 : (retval_5 = 0)) (PreH39 : (retval_6 = 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval_3: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (retval_2: Z) ,
  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (“ (retval_6 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_23_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "z") = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y"))) (PreH3 : (retval_3 = 0)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH34 : (afpoint_represents BX BY Q_r_eq_a )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_r_eq_a <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_r_eq_a <> ECInfinity)) (PreH39 : (r_pre = a_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 = 0)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  (“ (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) ) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "z") = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (EX (retval_4: Z)  (retval_5: Z)  (x0_2: Z)  (x1_2: Z)  (x2_2: Z)  (x3_2: Z)  (retval_6: Z) ,
  “ (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_non_alias) (Q_non_alias)) ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_23_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_4: Z) (retval_5: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_6: Z) (PreH1 : (retval_6 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_5 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval_4 = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval_4 = 0)) (PreH38 : (retval_5 = 0)) (PreH39 : (retval_6 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  (EX (retval: Z)  (retval_2: Z)  (x0: Z)  (x1: Z)  (x2: Z)  (x3: Z)  (retval_3: Z) ,
  “ (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) ) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "z") = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (“ (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_non_alias) (Q_non_alias)) ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_24_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) )) (PreH2 : (&((r_pre)  # "JPoint" ->ₛ "z") = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y"))) (PreH4 : (retval_3 = 0)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH35 : (afpoint_represents BX BY Q_r_eq_a )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_r_eq_a <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_r_eq_a <> ECInfinity)) (PreH40 : (r_pre = a_pre)) (PreH41 : (retval = 0)) (PreH42 : (retval_2 = 0)) (PreH43 : (retval_3 = 0)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  (“ (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) ) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "z") = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (EX (retval_4: Z)  (retval_5: Z)  (x0_2: Z)  (x1_2: Z)  (x2_2: Z)  (x3_2: Z)  (retval_6: Z) ,
  “ (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_non_alias) (Q_non_alias)) ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_entail_wit_24_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval_4: Z) (retval_5: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_6: Z) (PreH1 : (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_non_alias) (Q_non_alias)) )) (PreH2 : (retval_6 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH9 : (x3_2 < U64_MOD)) (PreH10 : (0 <= x3_2)) (PreH11 : (x2_2 < U64_MOD)) (PreH12 : (0 <= x2_2)) (PreH13 : (x1_2 < U64_MOD)) (PreH14 : (0 <= x1_2)) (PreH15 : (x0_2 < U64_MOD)) (PreH16 : (0 <= x0_2)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_non_alias )) (PreH33 : (afpoint_represents BX BY Q_non_alias )) (PreH34 : (retval_5 = 0)) (PreH35 : (Q_non_alias <> ECInfinity)) (PreH36 : (retval_4 = 0)) (PreH37 : (P_non_alias <> ECInfinity)) (PreH38 : (retval_4 = 0)) (PreH39 : (retval_5 = 0)) (PreH40 : (retval_6 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  (EX (retval: Z)  (retval_2: Z)  (x0: Z)  (x1: Z)  (x2: Z)  (x3: Z)  (retval_3: Z) ,
  “ (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) ) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "z") = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
  ||
  (“ (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_non_alias) (Q_non_alias)) ) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one ))
.

Definition montg_add_jpoint_and_apoint_return_wit_1_r_eq_a := 
(
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) )) (PreH2 : (&((r_pre)  # "JPoint" ->ₛ "z") = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y"))) (PreH4 : (retval_3 = 0)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH35 : (afpoint_represents BX BY Q_r_eq_a )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_r_eq_a <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_r_eq_a <> ECInfinity)) (PreH40 : (r_pre = a_pre)) (PreH41 : (retval = 0)) (PreH42 : (retval_2 = 0)) (PreH43 : (retval_3 = 0)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
|--
  “ (1 = 1) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_mont_jpoint r_pre (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (r_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) )) (PreH2 : (&((r_pre)  # "JPoint" ->ₛ "z") = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y"))) (PreH4 : (retval_3 = 0)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH35 : (afpoint_represents BX BY Q_r_eq_a )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_r_eq_a <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_r_eq_a <> ECInfinity)) (PreH40 : (r_pre = a_pre)) (PreH41 : (retval = 0)) (PreH42 : (retval_2 = 0)) (PreH43 : (retval_3 = 0)) ,
  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_montg_one )
|--
  EX (z: Z)  (y_2: Z)  (x_2: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) = (mont_p (x_2))) ” 
  &&  “ ((Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) = (mont_p (y_2))) ” 
  &&  “ ((mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) = (mont_p (z))) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (jpoint_represents x_2 y_2 z (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) ) ” 
  &&  “ ((mont_p (BX)) = (mont_p (x))) ” 
  &&  “ ((mont_p (BY)) = (mont_p (y))) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (afpoint_represents x y Q_r_eq_a ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition montg_add_jpoint_and_apoint_return_wit_2_non_alias := 
(
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_non_alias) (Q_non_alias)) )) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_non_alias )) (PreH33 : (afpoint_represents BX BY Q_non_alias )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_non_alias <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
|--
  “ (1 = 1) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_add (P_non_alias) (Q_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (jpoint_represents (maja_rx (AX) (AY) (AZ) (BX) (BY)) (maja_ry (AX) (AY) (AZ) (BX) (BY)) (maja_rz (AX) (BX) (AZ)) (sm2_point_add (P_non_alias) (Q_non_alias)) )) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_non_alias )) (PreH33 : (afpoint_represents BX BY Q_non_alias )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_non_alias <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_montg_one )
|--
  EX (z_2: Z)  (y_3: Z)  (x_3: Z)  (z: Z)  (y_2: Z)  (x_2: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) = (mont_p (x_3))) ” 
  &&  “ ((Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) = (mont_p (y_3))) ” 
  &&  “ ((mont_p ((AZ * (maja_h (AX) (BX) (AZ)) ))) = (mont_p (z_2))) ” 
  &&  “ (z_2 < SM2_P_Z) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (y_3 < SM2_P_Z) ” 
  &&  “ (0 <= y_3) ” 
  &&  “ (x_3 < SM2_P_Z) ” 
  &&  “ (0 <= x_3) ” 
  &&  “ (jpoint_represents x_3 y_3 z_2 (sm2_point_add (P_non_alias) (Q_non_alias)) ) ” 
  &&  “ ((mont_p (AX)) = (mont_p (x_2))) ” 
  &&  “ ((mont_p (AY)) = (mont_p (y_2))) ” 
  &&  “ ((mont_p (AZ)) = (mont_p (z))) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (jpoint_represents x_2 y_2 z P_non_alias ) ” 
  &&  “ ((mont_p (BX)) = (mont_p (x))) ” 
  &&  “ ((mont_p (BY)) = (mont_p (y))) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (afpoint_represents x y Q_non_alias ) ”
  &&  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition montg_add_jpoint_and_apoint_return_wit_3_r_eq_a := 
(
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : ((sm2_point_add (P_r_eq_a) (Q_r_eq_a)) = ECInfinity)) (PreH2 : (retval_4 = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH35 : (afpoint_represents BX BY Q_r_eq_a )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_r_eq_a <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_r_eq_a <> ECInfinity)) (PreH40 : (r_pre = a_pre)) (PreH41 : (retval = 0)) (PreH42 : (retval_2 = 0)) (PreH43 : (retval_3 <> 0)) (PreH44 : (retval_4 = 0)) ,
  (store_montg_one )
  **  (store_mont_jpoint r_pre ECInfinity )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_sm2_p )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
|--
  “ (1 = 1) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_mont_jpoint r_pre (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (r_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : ((sm2_point_add (P_r_eq_a) (Q_r_eq_a)) = ECInfinity)) (PreH2 : (retval_4 = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH35 : (afpoint_represents BX BY Q_r_eq_a )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_r_eq_a <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_r_eq_a <> ECInfinity)) (PreH40 : (r_pre = a_pre)) (PreH41 : (retval = 0)) (PreH42 : (retval_2 = 0)) (PreH43 : (retval_3 <> 0)) (PreH44 : (retval_4 = 0)) ,
  (store_montg_one )
  **  (store_mont_jpoint r_pre ECInfinity )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (z: Z)  (y_2: Z)  (x_2: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p (x_2)) = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ ((mont_p (x_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (x_2))) ” 
  &&  “ ((mont_p (y_2)) = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((mont_p (y_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (y_2))) ” 
  &&  “ ((mont_p (z)) = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (z)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (z))) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (jpoint_represents x_2 y_2 z (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) ) ” 
  &&  “ ((mont_p (BX)) = (mont_p (x))) ” 
  &&  “ ((mont_p (BY)) = (mont_p (y))) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (afpoint_represents x y Q_r_eq_a ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition montg_add_jpoint_and_apoint_return_wit_4_non_alias := 
(
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : ((sm2_point_add (P_non_alias) (Q_non_alias)) = ECInfinity)) (PreH2 : (retval_4 = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_non_alias )) (PreH35 : (afpoint_represents BX BY Q_non_alias )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_non_alias <> ECInfinity)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 = 0)) ,
  (store_montg_one )
  **  (store_mont_jpoint r_pre ECInfinity )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
|--
  “ (1 = 1) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_add (P_non_alias) (Q_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (r_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : ((sm2_point_add (P_non_alias) (Q_non_alias)) = ECInfinity)) (PreH2 : (retval_4 = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_non_alias )) (PreH35 : (afpoint_represents BX BY Q_non_alias )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_non_alias <> ECInfinity)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 = 0)) ,
  (store_montg_one )
  **  (store_mont_jpoint r_pre ECInfinity )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (z_2: Z)  (y_3: Z)  (x_3: Z)  (z: Z)  (y_2: Z)  (x_2: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p (x_3)) = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ ((mont_p (x_3)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (x_3))) ” 
  &&  “ ((mont_p (y_3)) = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((mont_p (y_3)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (y_3))) ” 
  &&  “ ((mont_p (z_2)) = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (z_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (z_2))) ” 
  &&  “ (z_2 < SM2_P_Z) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (y_3 < SM2_P_Z) ” 
  &&  “ (0 <= y_3) ” 
  &&  “ (x_3 < SM2_P_Z) ” 
  &&  “ (0 <= x_3) ” 
  &&  “ (jpoint_represents x_3 y_3 z_2 (sm2_point_add (P_non_alias) (Q_non_alias)) ) ” 
  &&  “ ((mont_p (AZ)) = (mont_p (z))) ” 
  &&  “ ((mont_p (AX)) = (mont_p (x_2))) ” 
  &&  “ ((mont_p (AY)) = (mont_p (y_2))) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (jpoint_represents x_2 y_2 z P_non_alias ) ” 
  &&  “ ((mont_p (BX)) = (mont_p (x))) ” 
  &&  “ ((mont_p (BY)) = (mont_p (y))) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (afpoint_represents x y Q_non_alias ) ”
  &&  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition montg_add_jpoint_and_apoint_return_wit_5_r_eq_a := 
(
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (P_r_eq_a = Q_r_eq_a)) (PreH3 : (retval_4 = 1)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH5 : (retval_3 = 1)) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH7 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH9 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH10 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH11 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : ((mont_p (BY)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BY)))) (PreH22 : ((mont_p (BX)) < SM2_P_Z)) (PreH23 : (0 <= (mont_p (BX)))) (PreH24 : (AZ <> 0)) (PreH25 : (AZ < SM2_P_Z)) (PreH26 : (0 <= AZ)) (PreH27 : (AY < SM2_P_Z)) (PreH28 : (0 <= AY)) (PreH29 : (AX < SM2_P_Z)) (PreH30 : (0 <= AX)) (PreH31 : (BY < SM2_P_Z)) (PreH32 : (0 <= BY)) (PreH33 : (BX < SM2_P_Z)) (PreH34 : (0 <= BX)) (PreH35 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH36 : (afpoint_represents BX BY Q_r_eq_a )) (PreH37 : (retval_2 = 0)) (PreH38 : (Q_r_eq_a <> ECInfinity)) (PreH39 : (retval = 0)) (PreH40 : (P_r_eq_a <> ECInfinity)) (PreH41 : (r_pre = a_pre)) (PreH42 : (retval = 0)) (PreH43 : (retval_2 = 0)) (PreH44 : (retval_3 <> 0)) (PreH45 : (retval_4 <> 0)) ,
  (store_mont_jpoint r_pre (sm2_point_double (P_r_eq_a)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
|--
  “ (1 = 1) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_mont_jpoint r_pre (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (r_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (P_r_eq_a = Q_r_eq_a)) (PreH3 : (retval_4 = 1)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH5 : (retval_3 = 1)) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH7 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH9 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH10 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH11 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : ((mont_p (BY)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BY)))) (PreH22 : ((mont_p (BX)) < SM2_P_Z)) (PreH23 : (0 <= (mont_p (BX)))) (PreH24 : (AZ <> 0)) (PreH25 : (AZ < SM2_P_Z)) (PreH26 : (0 <= AZ)) (PreH27 : (AY < SM2_P_Z)) (PreH28 : (0 <= AY)) (PreH29 : (AX < SM2_P_Z)) (PreH30 : (0 <= AX)) (PreH31 : (BY < SM2_P_Z)) (PreH32 : (0 <= BY)) (PreH33 : (BX < SM2_P_Z)) (PreH34 : (0 <= BX)) (PreH35 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH36 : (afpoint_represents BX BY Q_r_eq_a )) (PreH37 : (retval_2 = 0)) (PreH38 : (Q_r_eq_a <> ECInfinity)) (PreH39 : (retval = 0)) (PreH40 : (P_r_eq_a <> ECInfinity)) (PreH41 : (r_pre = a_pre)) (PreH42 : (retval = 0)) (PreH43 : (retval_2 = 0)) (PreH44 : (retval_3 <> 0)) (PreH45 : (retval_4 <> 0)) ,
  (store_mont_jpoint r_pre (sm2_point_double (P_r_eq_a)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_montg_one )
|--
  EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (z: Z)  (y_2: Z)  (x_2: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p (x_2)) = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ ((mont_p (x_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (x_2))) ” 
  &&  “ ((mont_p (y_2)) = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((mont_p (y_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (y_2))) ” 
  &&  “ ((mont_p (z)) = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (z)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (z))) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (jpoint_represents x_2 y_2 z (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) ) ” 
  &&  “ ((mont_p (BX)) = (mont_p (x))) ” 
  &&  “ ((mont_p (BY)) = (mont_p (y))) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (afpoint_represents x y Q_r_eq_a ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition montg_add_jpoint_and_apoint_return_wit_6_non_alias := 
(
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (P_non_alias = Q_non_alias)) (PreH2 : (retval_4 = 1)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_non_alias )) (PreH35 : (afpoint_represents BX BY Q_non_alias )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_non_alias <> ECInfinity)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 <> 0)) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_double (P_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
|--
  “ (1 = 1) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_add (P_non_alias) (Q_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (r_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (P_non_alias = Q_non_alias)) (PreH2 : (retval_4 = 1)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_non_alias )) (PreH35 : (afpoint_represents BX BY Q_non_alias )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_non_alias <> ECInfinity)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 <> 0)) ,
  (store_mont_jpoint r_pre (sm2_point_double (P_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_montg_one )
|--
  EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (z: Z)  (y_2: Z)  (x_2: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p (x_2)) = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ ((mont_p (x_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (x_2))) ” 
  &&  “ ((mont_p (y_2)) = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((mont_p (y_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (y_2))) ” 
  &&  “ ((mont_p (z)) = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (z)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (z))) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (jpoint_represents x_2 y_2 z (sm2_point_add (P_non_alias) (Q_non_alias)) ) ” 
  &&  “ ((mont_p (BX)) = (mont_p (x))) ” 
  &&  “ ((mont_p (BY)) = (mont_p (y))) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (afpoint_represents x y Q_non_alias ) ”
  &&  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition montg_add_jpoint_and_apoint_return_wit_7_r_eq_a := 
(
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (retval_2 = 1)) (PreH3 : (Q_r_eq_a = ECInfinity)) (PreH4 : (retval = 0)) (PreH5 : (P_r_eq_a <> ECInfinity)) (PreH6 : (r_pre = a_pre)) (PreH7 : (retval = 0)) (PreH8 : (retval_2 <> 0)) ,
  (store_mont_jpoint r_pre P_r_eq_a )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 = 1) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_mont_jpoint r_pre (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (r_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (retval_2 = 1)) (PreH3 : (Q_r_eq_a = ECInfinity)) (PreH4 : (retval = 0)) (PreH5 : (P_r_eq_a <> ECInfinity)) (PreH6 : (r_pre = a_pre)) (PreH7 : (retval = 0)) (PreH8 : (retval_2 <> 0)) ,
  (store_mont_jpoint r_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (z: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p (x)) = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((mont_p (x)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (x))) ” 
  &&  “ ((mont_p (y)) = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (y)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (y))) ” 
  &&  “ ((mont_p (z)) = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (z)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (z))) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (jpoint_represents x y z (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition montg_add_jpoint_and_apoint_return_wit_8_non_alias := 
(
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (Q_non_alias = ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval = 0)) (PreH6 : (retval_2 <> 0)) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_jpoint r_pre P_non_alias )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 = 1) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_add (P_non_alias) (Q_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (r_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (Q_non_alias = ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval = 0)) (PreH6 : (retval_2 <> 0)) ,
  (store_mont_jpoint r_pre P_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (z: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p (x)) = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((mont_p (x)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (x))) ” 
  &&  “ ((mont_p (y)) = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (y)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (y))) ” 
  &&  “ ((mont_p (z)) = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (z)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (z))) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (jpoint_represents x y z (sm2_point_add (P_non_alias) (Q_non_alias)) ) ”
  &&  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition montg_add_jpoint_and_apoint_return_wit_9_r_eq_a := 
(
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (retval = 1)) (PreH3 : (P_r_eq_a = ECInfinity)) (PreH4 : (r_pre = a_pre)) (PreH5 : (retval <> 0)) ,
  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_mont_jpoint r_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 = 1) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_mont_jpoint r_pre (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (r_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (retval = 1)) (PreH3 : (P_r_eq_a = ECInfinity)) (PreH4 : (r_pre = a_pre)) (PreH5 : (retval <> 0)) ,
  (store_mont_jpoint r_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (z: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p (x)) = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((mont_p (x)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (x))) ” 
  &&  “ ((mont_p (y)) = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (y)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (y))) ” 
  &&  “ ((mont_p (z)) = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (z)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (z))) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (jpoint_represents x y z (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition montg_add_jpoint_and_apoint_return_wit_10_non_alias := 
(
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (retval = 1)) (PreH3 : (P_non_alias = ECInfinity)) (PreH4 : (retval <> 0)) ,
  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_mont_jpoint r_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 = 1) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_add (P_non_alias) (Q_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (r_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (retval = 1)) (PreH3 : (P_non_alias = ECInfinity)) (PreH4 : (retval <> 0)) ,
  (store_mont_jpoint r_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (z: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p (x)) = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((mont_p (x)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (x))) ” 
  &&  “ ((mont_p (y)) = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (y)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (y))) ” 
  &&  “ ((mont_p (z)) = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (z)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (z))) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (jpoint_represents x y z (sm2_point_add (P_non_alias) (Q_non_alias)) ) ”
  &&  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition montg_add_jpoint_and_apoint_partial_solve_wit_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (PreH1 : (r_pre = a_pre)) ,
  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (r_pre = a_pre) ”
  &&  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) ,
  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_3_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (P_r_eq_a = ECInfinity)) (PreH3 : (r_pre = a_pre)) (PreH4 : (retval <> 0)) ,
  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (retval = 1) ” 
  &&  “ (P_r_eq_a = ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_4_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (P_non_alias = ECInfinity)) (PreH3 : (retval <> 0)) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (retval = 1) ” 
  &&  “ (P_non_alias = ECInfinity) ” 
  &&  “ (retval <> 0) ”
  &&  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_5_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (P_r_eq_a <> ECInfinity)) (PreH3 : (r_pre = a_pre)) (PreH4 : (retval = 0)) ,
  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_6_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (P_non_alias <> ECInfinity)) (PreH3 : (retval = 0)) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_7_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (Q_r_eq_a = ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_r_eq_a <> ECInfinity)) (PreH5 : (r_pre = a_pre)) (PreH6 : (retval = 0)) (PreH7 : (retval_2 <> 0)) ,
  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (r_pre = a_pre) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_7_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (Q_r_eq_a = ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_r_eq_a <> ECInfinity)) (PreH5 : (r_pre = a_pre)) (PreH6 : (retval = 0)) (PreH7 : (retval_2 <> 0)) ,
  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (r_pre = a_pre) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (Q_r_eq_a = ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_mont_afpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_7_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_7_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_7_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_8_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (Q_non_alias = ECInfinity)) (PreH3 : (retval = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval = 0)) (PreH6 : (retval_2 <> 0)) ,
  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (store_mont_jpoint a_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (retval_2 = 1) ” 
  &&  “ (Q_non_alias = ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_mont_afpoint b_pre Q_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_9_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : (AZ <> 0)) (PreH2 : (AZ < SM2_P_Z)) (PreH3 : (0 <= AZ)) (PreH4 : (AY < SM2_P_Z)) (PreH5 : (0 <= AY)) (PreH6 : (AX < SM2_P_Z)) (PreH7 : (0 <= AX)) (PreH8 : (BY < SM2_P_Z)) (PreH9 : (0 <= BY)) (PreH10 : (BX < SM2_P_Z)) (PreH11 : (0 <= BX)) (PreH12 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH13 : (afpoint_represents BX BY Q_r_eq_a )) (PreH14 : (retval_2 = 0)) (PreH15 : (Q_r_eq_a <> ECInfinity)) (PreH16 : (retval = 0)) (PreH17 : (P_r_eq_a <> ECInfinity)) (PreH18 : (r_pre = a_pre)) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_jpoint_fields a_pre (mont_p (AX)) (mont_p (AY)) (mont_p (AZ)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= AZ) ” 
  &&  “ (AZ < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_9_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : (AZ <> 0)) (PreH2 : (AZ < SM2_P_Z)) (PreH3 : (0 <= AZ)) (PreH4 : (AY < SM2_P_Z)) (PreH5 : (0 <= AY)) (PreH6 : (AX < SM2_P_Z)) (PreH7 : (0 <= AX)) (PreH8 : (BY < SM2_P_Z)) (PreH9 : (0 <= BY)) (PreH10 : (BX < SM2_P_Z)) (PreH11 : (0 <= BX)) (PreH12 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH13 : (afpoint_represents BX BY Q_r_eq_a )) (PreH14 : (retval_2 = 0)) (PreH15 : (Q_r_eq_a <> ECInfinity)) (PreH16 : (retval = 0)) (PreH17 : (P_r_eq_a <> ECInfinity)) (PreH18 : (r_pre = a_pre)) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_jpoint_fields a_pre (mont_p (AX)) (mont_p (AY)) (mont_p (AZ)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= AZ) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (UInt64Array.undef_full &(( &( "Zsqr" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_9_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_9_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_9_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_10_non_alias_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : (AZ <> 0)) (PreH2 : (AZ < SM2_P_Z)) (PreH3 : (0 <= AZ)) (PreH4 : (AY < SM2_P_Z)) (PreH5 : (0 <= AY)) (PreH6 : (AX < SM2_P_Z)) (PreH7 : (0 <= AX)) (PreH8 : (BY < SM2_P_Z)) (PreH9 : (0 <= BY)) (PreH10 : (BX < SM2_P_Z)) (PreH11 : (0 <= BX)) (PreH12 : (jpoint_represents AX AY AZ P_non_alias )) (PreH13 : (afpoint_represents BX BY Q_non_alias )) (PreH14 : (retval_2 = 0)) (PreH15 : (Q_non_alias <> ECInfinity)) (PreH16 : (retval = 0)) (PreH17 : (P_non_alias <> ECInfinity)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_jpoint_fields a_pre (mont_p (AX)) (mont_p (AY)) (mont_p (AZ)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= AZ) ” 
  &&  “ (AZ < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_10_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : (AZ <> 0)) (PreH2 : (AZ < SM2_P_Z)) (PreH3 : (0 <= AZ)) (PreH4 : (AY < SM2_P_Z)) (PreH5 : (0 <= AY)) (PreH6 : (AX < SM2_P_Z)) (PreH7 : (0 <= AX)) (PreH8 : (BY < SM2_P_Z)) (PreH9 : (0 <= BY)) (PreH10 : (BX < SM2_P_Z)) (PreH11 : (0 <= BX)) (PreH12 : (jpoint_represents AX AY AZ P_non_alias )) (PreH13 : (afpoint_represents BX BY Q_non_alias )) (PreH14 : (retval_2 = 0)) (PreH15 : (Q_non_alias <> ECInfinity)) (PreH16 : (retval = 0)) (PreH17 : (P_non_alias <> ECInfinity)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_jpoint_fields a_pre (mont_p (AX)) (mont_p (AY)) (mont_p (AZ)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= AZ) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (UInt64Array.undef_full &(( &( "Zsqr" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_10_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_10_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_10_non_alias_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_11_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : (AZ <> 0)) (PreH2 : (AZ < SM2_P_Z)) (PreH3 : (0 <= AZ)) (PreH4 : (AY < SM2_P_Z)) (PreH5 : (0 <= AY)) (PreH6 : (AX < SM2_P_Z)) (PreH7 : (0 <= AX)) (PreH8 : (BY < SM2_P_Z)) (PreH9 : (0 <= BY)) (PreH10 : (BX < SM2_P_Z)) (PreH11 : (0 <= BX)) (PreH12 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH13 : (afpoint_represents BX BY Q_r_eq_a )) (PreH14 : (retval_2 = 0)) (PreH15 : (Q_r_eq_a <> ECInfinity)) (PreH16 : (retval = 0)) (PreH17 : (P_r_eq_a <> ECInfinity)) (PreH18 : (r_pre = a_pre)) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((AZ * AZ ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (0 <= BX) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= (maja_z2 (AZ))) ” 
  &&  “ ((maja_z2 (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_11_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : (AZ <> 0)) (PreH2 : (AZ < SM2_P_Z)) (PreH3 : (0 <= AZ)) (PreH4 : (AY < SM2_P_Z)) (PreH5 : (0 <= AY)) (PreH6 : (AX < SM2_P_Z)) (PreH7 : (0 <= AX)) (PreH8 : (BY < SM2_P_Z)) (PreH9 : (0 <= BY)) (PreH10 : (BX < SM2_P_Z)) (PreH11 : (0 <= BX)) (PreH12 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH13 : (afpoint_represents BX BY Q_r_eq_a )) (PreH14 : (retval_2 = 0)) (PreH15 : (Q_r_eq_a <> ECInfinity)) (PreH16 : (retval = 0)) (PreH17 : (P_r_eq_a <> ECInfinity)) (PreH18 : (r_pre = a_pre)) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((AZ * AZ ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_montg_one )
|--
  “ (0 <= BX) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= (maja_z2 (AZ))) ” 
  &&  “ ((maja_z2 (AZ)) < SM2_P_Z) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (UInt64Array.undef_full &(( &( "A" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_11_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_11_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_11_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_12_non_alias_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : (AZ <> 0)) (PreH2 : (AZ < SM2_P_Z)) (PreH3 : (0 <= AZ)) (PreH4 : (AY < SM2_P_Z)) (PreH5 : (0 <= AY)) (PreH6 : (AX < SM2_P_Z)) (PreH7 : (0 <= AX)) (PreH8 : (BY < SM2_P_Z)) (PreH9 : (0 <= BY)) (PreH10 : (BX < SM2_P_Z)) (PreH11 : (0 <= BX)) (PreH12 : (jpoint_represents AX AY AZ P_non_alias )) (PreH13 : (afpoint_represents BX BY Q_non_alias )) (PreH14 : (retval_2 = 0)) (PreH15 : (Q_non_alias <> ECInfinity)) (PreH16 : (retval = 0)) (PreH17 : (P_non_alias <> ECInfinity)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((AZ * AZ ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= BX) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= (maja_z2 (AZ))) ” 
  &&  “ ((maja_z2 (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_12_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : (AZ <> 0)) (PreH2 : (AZ < SM2_P_Z)) (PreH3 : (0 <= AZ)) (PreH4 : (AY < SM2_P_Z)) (PreH5 : (0 <= AY)) (PreH6 : (AX < SM2_P_Z)) (PreH7 : (0 <= AX)) (PreH8 : (BY < SM2_P_Z)) (PreH9 : (0 <= BY)) (PreH10 : (BX < SM2_P_Z)) (PreH11 : (0 <= BX)) (PreH12 : (jpoint_represents AX AY AZ P_non_alias )) (PreH13 : (afpoint_represents BX BY Q_non_alias )) (PreH14 : (retval_2 = 0)) (PreH15 : (Q_non_alias <> ECInfinity)) (PreH16 : (retval = 0)) (PreH17 : (P_non_alias <> ECInfinity)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((AZ * AZ ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_afpoint_fields b_pre (mont_p (BX)) (mont_p (BY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= BX) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= (maja_z2 (AZ))) ” 
  &&  “ ((maja_z2 (AZ)) < SM2_P_Z) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (UInt64Array.undef_full &(( &( "A" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_12_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_12_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_12_non_alias_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_13_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH17 : (afpoint_represents BX BY Q_r_eq_a )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_r_eq_a <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_r_eq_a <> ECInfinity)) (PreH22 : (r_pre = a_pre)) (PreH23 : (retval = 0)) (PreH24 : (retval_2 = 0)) ,
  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((BX * (maja_z2 (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (0 <= AZ) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= (maja_z2 (AZ))) ” 
  &&  “ ((maja_z2 (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_13_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH17 : (afpoint_represents BX BY Q_r_eq_a )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_r_eq_a <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_r_eq_a <> ECInfinity)) (PreH22 : (r_pre = a_pre)) (PreH23 : (retval = 0)) (PreH24 : (retval_2 = 0)) ,
  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((BX * (maja_z2 (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (store_montg_one )
|--
  “ (0 <= AZ) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= (maja_z2 (AZ))) ” 
  &&  “ ((maja_z2 (AZ)) < SM2_P_Z) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((BX * (maja_z2 (AZ)) ))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_13_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_13_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_13_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_14_non_alias_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_non_alias )) (PreH17 : (afpoint_represents BX BY Q_non_alias )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_non_alias <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_non_alias <> ECInfinity)) (PreH22 : (retval = 0)) (PreH23 : (retval_2 = 0)) ,
  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((BX * (maja_z2 (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= AZ) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= (maja_z2 (AZ))) ” 
  &&  “ ((maja_z2 (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_14_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_non_alias )) (PreH17 : (afpoint_represents BX BY Q_non_alias )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_non_alias <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_non_alias <> ECInfinity)) (PreH22 : (retval = 0)) (PreH23 : (retval_2 = 0)) ,
  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((BX * (maja_z2 (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= AZ) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= (maja_z2 (AZ))) ” 
  &&  “ ((maja_z2 (AZ)) < SM2_P_Z) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((BX * (maja_z2 (AZ)) ))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_14_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_14_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_14_non_alias_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_15_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH17 : (afpoint_represents BX BY Q_r_eq_a )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_r_eq_a <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_r_eq_a <> ECInfinity)) (PreH22 : (r_pre = a_pre)) (PreH23 : (retval = 0)) (PreH24 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((AZ * (maja_z2 (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((BX * (maja_z2 (AZ)) ))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (0 <= BY) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= (maja_z3 (AZ))) ” 
  &&  “ ((maja_z3 (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_15_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH17 : (afpoint_represents BX BY Q_r_eq_a )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_r_eq_a <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_r_eq_a <> ECInfinity)) (PreH22 : (r_pre = a_pre)) (PreH23 : (retval = 0)) (PreH24 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((AZ * (maja_z2 (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((BX * (maja_z2 (AZ)) ))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (store_montg_one )
|--
  “ (0 <= BY) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= (maja_z3 (AZ))) ” 
  &&  “ ((maja_z3 (AZ)) < SM2_P_Z) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (UInt64Array.undef_full &(( &( "B" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((BX * (maja_z2 (AZ)) ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_15_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_15_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_15_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_16_non_alias_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_non_alias )) (PreH17 : (afpoint_represents BX BY Q_non_alias )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_non_alias <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_non_alias <> ECInfinity)) (PreH22 : (retval = 0)) (PreH23 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((AZ * (maja_z2 (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((BX * (maja_z2 (AZ)) ))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= BY) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= (maja_z3 (AZ))) ” 
  &&  “ ((maja_z3 (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_16_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_non_alias )) (PreH17 : (afpoint_represents BX BY Q_non_alias )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_non_alias <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_non_alias <> ECInfinity)) (PreH22 : (retval = 0)) (PreH23 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((AZ * (maja_z2 (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((BX * (maja_z2 (AZ)) ))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= BY) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= (maja_z3 (AZ))) ” 
  &&  “ ((maja_z3 (AZ)) < SM2_P_Z) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (UInt64Array.undef_full &(( &( "B" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((BX * (maja_z2 (AZ)) ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_16_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_16_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_16_non_alias_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_17_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH17 : (afpoint_represents BX BY Q_r_eq_a )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_r_eq_a <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_r_eq_a <> ECInfinity)) (PreH22 : (r_pre = a_pre)) (PreH23 : (retval = 0)) (PreH24 : (retval_2 = 0)) ,
  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((BY * (maja_z3 (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((BX * (maja_z2 (AZ)) ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (store_montg_one )
|--
  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (UInt64Array.undef_full &(( &( "C" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((BY * (maja_z3 (AZ)) ))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_18_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_non_alias )) (PreH17 : (afpoint_represents BX BY Q_non_alias )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_non_alias <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_non_alias <> ECInfinity)) (PreH22 : (retval = 0)) (PreH23 : (retval_2 = 0)) ,
  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((BY * (maja_z3 (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((BX * (maja_z2 (AZ)) ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UndefStructPredu32 ( &( "C" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (UInt64Array.undef_full &(( &( "C" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((BY * (maja_z3 (AZ)) ))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_19_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH17 : (afpoint_represents BX BY Q_r_eq_a )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_r_eq_a <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_r_eq_a <> ECInfinity)) (PreH22 : (r_pre = a_pre)) (PreH23 : (retval = 0)) (PreH24 : (retval_2 = 0)) ,
  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((BY * (maja_z3 (AZ)) ))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (store_montg_one )
|--
  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (UInt64Array.undef_full &(( &( "D" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_20_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_non_alias )) (PreH17 : (afpoint_represents BX BY Q_non_alias )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_non_alias <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_non_alias <> ECInfinity)) (PreH22 : (retval = 0)) (PreH23 : (retval_2 = 0)) ,
  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((BY * (maja_z3 (AZ)) ))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UndefStructPredu32 ( &( "D" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (UInt64Array.undef_full &(( &( "D" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_21_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_non_alias )) (PreH17 : (afpoint_represents BX BY Q_non_alias )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_non_alias <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_non_alias <> ECInfinity)) (PreH22 : (retval = 0)) (PreH23 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "D" ) ) (Zmod (((mont_p ((maja_s2 (BY) (AZ)))) - (mont_p (AY)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_bn_zero )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "D" ) ) (Zmod (((mont_p ((maja_s2 (BY) (AZ)))) - (mont_p (AY)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_22_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (PreH1 : ((mont_p (BY)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (BY)))) (PreH3 : ((mont_p (BX)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (BX)))) (PreH5 : (AZ <> 0)) (PreH6 : (AZ < SM2_P_Z)) (PreH7 : (0 <= AZ)) (PreH8 : (AY < SM2_P_Z)) (PreH9 : (0 <= AY)) (PreH10 : (AX < SM2_P_Z)) (PreH11 : (0 <= AX)) (PreH12 : (BY < SM2_P_Z)) (PreH13 : (0 <= BY)) (PreH14 : (BX < SM2_P_Z)) (PreH15 : (0 <= BX)) (PreH16 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH17 : (afpoint_represents BX BY Q_r_eq_a )) (PreH18 : (retval_2 = 0)) (PreH19 : (Q_r_eq_a <> ECInfinity)) (PreH20 : (retval = 0)) (PreH21 : (P_r_eq_a <> ECInfinity)) (PreH22 : (r_pre = a_pre)) (PreH23 : (retval = 0)) (PreH24 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "D" ) ) (Zmod (((mont_p ((maja_s2 (BY) (AZ)))) - (mont_p (AY)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_bn_zero )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "D" ) ) (Zmod (((mont_p ((maja_s2 (BY) (AZ)))) - (mont_p (AY)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (Zmod (((mont_p ((maja_u2 (BX) (AZ)))) - (mont_p (AX)) )) (SM2_P_Z)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_23_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH2 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH5 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) (PreH14 : ((mont_p (BY)) < SM2_P_Z)) (PreH15 : (0 <= (mont_p (BY)))) (PreH16 : ((mont_p (BX)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BX)))) (PreH18 : (AZ <> 0)) (PreH19 : (AZ < SM2_P_Z)) (PreH20 : (0 <= AZ)) (PreH21 : (AY < SM2_P_Z)) (PreH22 : (0 <= AY)) (PreH23 : (AX < SM2_P_Z)) (PreH24 : (0 <= AX)) (PreH25 : (BY < SM2_P_Z)) (PreH26 : (0 <= BY)) (PreH27 : (BX < SM2_P_Z)) (PreH28 : (0 <= BX)) (PreH29 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH30 : (afpoint_represents BX BY Q_r_eq_a )) (PreH31 : (retval_2 = 0)) (PreH32 : (Q_r_eq_a <> ECInfinity)) (PreH33 : (retval = 0)) (PreH34 : (P_r_eq_a <> ECInfinity)) (PreH35 : (r_pre = a_pre)) (PreH36 : (retval = 0)) (PreH37 : (retval_2 = 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_24_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH2 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH5 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) (PreH14 : ((mont_p (BY)) < SM2_P_Z)) (PreH15 : (0 <= (mont_p (BY)))) (PreH16 : ((mont_p (BX)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BX)))) (PreH18 : (AZ <> 0)) (PreH19 : (AZ < SM2_P_Z)) (PreH20 : (0 <= AZ)) (PreH21 : (AY < SM2_P_Z)) (PreH22 : (0 <= AY)) (PreH23 : (AX < SM2_P_Z)) (PreH24 : (0 <= AX)) (PreH25 : (BY < SM2_P_Z)) (PreH26 : (0 <= BY)) (PreH27 : (BX < SM2_P_Z)) (PreH28 : (0 <= BX)) (PreH29 : (jpoint_represents AX AY AZ P_non_alias )) (PreH30 : (afpoint_represents BX BY Q_non_alias )) (PreH31 : (retval_2 = 0)) (PreH32 : (Q_non_alias <> ECInfinity)) (PreH33 : (retval = 0)) (PreH34 : (P_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (retval_2 = 0)) ,
  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_25_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 <> 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_26_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 <> 0)) ,
  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (store_u256_limbs (&(( &( "D" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (&(( &( "C" ) )->ₛ "v") + (0 * sizeof(UINT64))) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_27_r_eq_a_pure := 
(
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (P_r_eq_a = Q_r_eq_a)) (PreH2 : (retval_4 = 1)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH35 : (afpoint_represents BX BY Q_r_eq_a )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_r_eq_a <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_r_eq_a <> ECInfinity)) (PreH40 : (r_pre = a_pre)) (PreH41 : (retval = 0)) (PreH42 : (retval_2 = 0)) (PreH43 : (retval_3 <> 0)) (PreH44 : (retval_4 <> 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  EX (x: Z)  (y: Z)  (z: Z) ,
  “ (r_pre = a_pre) ” 
  &&  “ (jpoint_represents x y z Q_r_eq_a ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ ((mont_p (AY)) = (mont_p (y))) ” 
  &&  “ ((mont_p (AX)) = (mont_p (x))) ” 
  &&  “ ((mont_p (AZ)) = (mont_p (z))) ”
) \/
(
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (P_r_eq_a = Q_r_eq_a)) (PreH2 : (retval_4 = 1)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH35 : (afpoint_represents BX BY Q_r_eq_a )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_r_eq_a <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_r_eq_a <> ECInfinity)) (PreH40 : (r_pre = a_pre)) (PreH41 : (retval = 0)) (PreH42 : (retval_2 = 0)) (PreH43 : (retval_3 <> 0)) (PreH44 : (retval_4 <> 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  EX (x: Z)  (y: Z)  (z: Z) ,
  “ (jpoint_represents x y z Q_r_eq_a ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ ((mont_p (AY)) = (mont_p (y))) ” 
  &&  “ ((mont_p (AX)) = (mont_p (x))) ” 
  &&  “ ((mont_p (AZ)) = (mont_p (z))) ”
).

Definition montg_add_jpoint_and_apoint_partial_solve_wit_27_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (P_r_eq_a = Q_r_eq_a)) (PreH2 : (retval_4 = 1)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH35 : (afpoint_represents BX BY Q_r_eq_a )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_r_eq_a <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_r_eq_a <> ECInfinity)) (PreH40 : (r_pre = a_pre)) (PreH41 : (retval = 0)) (PreH42 : (retval_2 = 0)) (PreH43 : (retval_3 <> 0)) (PreH44 : (retval_4 <> 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  EX (x: Z)  (y: Z)  (z: Z) ,
  “ (r_pre = a_pre) ” 
  &&  “ (jpoint_represents x y z Q_r_eq_a ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ ((mont_p (AY)) = (mont_p (y))) ” 
  &&  “ ((mont_p (AX)) = (mont_p (x))) ” 
  &&  “ ((mont_p (AZ)) = (mont_p (z))) ” 
  &&  “ (P_r_eq_a = Q_r_eq_a) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_27_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_27_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_27_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_28_non_alias_pure := 
(
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (P_non_alias = Q_non_alias)) (PreH2 : (retval_4 = 1)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_non_alias )) (PreH35 : (afpoint_represents BX BY Q_non_alias )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_non_alias <> ECInfinity)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 <> 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  EX (x: Z)  (y: Z)  (z: Z) ,
  “ (jpoint_represents x y z Q_non_alias ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ ((mont_p (AY)) = (mont_p (y))) ” 
  &&  “ ((mont_p (AX)) = (mont_p (x))) ” 
  &&  “ ((mont_p (AZ)) = (mont_p (z))) ”
) \/
(
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (P_non_alias = Q_non_alias)) (PreH2 : (retval_4 = 1)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_non_alias )) (PreH35 : (afpoint_represents BX BY Q_non_alias )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_non_alias <> ECInfinity)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 <> 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  EX (x: Z)  (y: Z)  (z: Z) ,
  “ (jpoint_represents x y z Q_non_alias ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ ((mont_p (AY)) = (mont_p (y))) ” 
  &&  “ ((mont_p (AX)) = (mont_p (x))) ” 
  &&  “ ((mont_p (AZ)) = (mont_p (z))) ”
).

Definition montg_add_jpoint_and_apoint_partial_solve_wit_28_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (P_non_alias = Q_non_alias)) (PreH2 : (retval_4 = 1)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_non_alias )) (PreH35 : (afpoint_represents BX BY Q_non_alias )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_non_alias <> ECInfinity)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 <> 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  EX (x: Z)  (y: Z)  (z: Z) ,
  “ (jpoint_represents x y z Q_non_alias ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ ((mont_p (AY)) = (mont_p (y))) ” 
  &&  “ ((mont_p (AX)) = (mont_p (x))) ” 
  &&  “ ((mont_p (AZ)) = (mont_p (z))) ” 
  &&  “ (P_non_alias = Q_non_alias) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) = 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_mont_jpoint a_pre P_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_28_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_28_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_28_non_alias_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_29_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : ((sm2_point_add (P_r_eq_a) (Q_r_eq_a)) = ECInfinity)) (PreH2 : (retval_4 = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH35 : (afpoint_represents BX BY Q_r_eq_a )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_r_eq_a <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_r_eq_a <> ECInfinity)) (PreH40 : (r_pre = a_pre)) (PreH41 : (retval = 0)) (PreH42 : (retval_2 = 0)) (PreH43 : (retval_3 <> 0)) (PreH44 : (retval_4 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  “ ((sm2_point_add (P_r_eq_a) (Q_r_eq_a)) = ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_montg_one )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_30_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (retval_4: Z) (PreH1 : ((sm2_point_add (P_non_alias) (Q_non_alias)) = ECInfinity)) (PreH2 : (retval_4 = 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0)) (PreH4 : (retval_3 = 1)) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0)) (PreH6 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH8 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH9 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH10 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : ((mont_p (BY)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BY)))) (PreH21 : ((mont_p (BX)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (BX)))) (PreH23 : (AZ <> 0)) (PreH24 : (AZ < SM2_P_Z)) (PreH25 : (0 <= AZ)) (PreH26 : (AY < SM2_P_Z)) (PreH27 : (0 <= AY)) (PreH28 : (AX < SM2_P_Z)) (PreH29 : (0 <= AX)) (PreH30 : (BY < SM2_P_Z)) (PreH31 : (0 <= BY)) (PreH32 : (BX < SM2_P_Z)) (PreH33 : (0 <= BX)) (PreH34 : (jpoint_represents AX AY AZ P_non_alias )) (PreH35 : (afpoint_represents BX BY Q_non_alias )) (PreH36 : (retval_2 = 0)) (PreH37 : (Q_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (P_non_alias <> ECInfinity)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 <> 0)) (PreH43 : (retval_4 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ ((sm2_point_add (P_non_alias) (Q_non_alias)) = ECInfinity) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) <> 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) = 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_montg_one )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_31_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (0 <= (maja_h (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h (AX) (BX) (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_31_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  “ (0 <= (maja_h (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h (AX) (BX) (AZ)) < SM2_P_Z) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_31_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_31_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_31_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_32_non_alias_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= (maja_h (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h (AX) (BX) (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_32_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_z3 (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= (maja_h (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h (AX) (BX) (AZ)) < SM2_P_Z) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_32_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_32_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_32_non_alias_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_33_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (0 <= (maja_h (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h (AX) (BX) (AZ)) < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h2 (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h2 (AX) (BX) (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_33_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  “ (0 <= (maja_h (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h (AX) (BX) (AZ)) < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h2 (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h2 (AX) (BX) (AZ)) < SM2_P_Z) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_h2 (AX) (BX) (AZ)))) )
  **  (UInt64Array.undef_full &(( &( "Ccub" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_33_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_33_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_33_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_34_non_alias_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= (maja_h (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h (AX) (BX) (AZ)) < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h2 (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h2 (AX) (BX) (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_34_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "Ccub" ) ) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= (maja_h (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h (AX) (BX) (AZ)) < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h2 (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h2 (AX) (BX) (AZ)) < SM2_P_Z) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_h2 (AX) (BX) (AZ)))) )
  **  (UInt64Array.undef_full &(( &( "Ccub" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_34_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_34_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_34_non_alias_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_35_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (0 <= AX) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h2 (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h2 (AX) (BX) (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_35_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (store_montg_one )
|--
  “ (0 <= AX) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h2 (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h2 (AX) (BX) (AZ)) < SM2_P_Z) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_h2 (AX) (BX) (AZ)))) )
  **  (UInt64Array.undef_full &(( &( "E" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_35_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_35_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_35_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_36_non_alias_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= AX) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h2 (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h2 (AX) (BX) (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_36_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UndefStructPredu32 ( &( "E" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= AX) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h2 (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h2 (AX) (BX) (AZ)) < SM2_P_Z) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_h2 (AX) (BX) (AZ)))) )
  **  (UInt64Array.undef_full &(( &( "E" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_36_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_36_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_36_non_alias_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_37_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((AX * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
|--
  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_38_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((AX * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_39_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (Zmod ((2 * (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_39_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (Zmod ((2 * (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_two_u1h2 (AX) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_39_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_39_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_39_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_40_non_alias_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (Zmod ((2 * (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_40_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (Zmod ((2 * (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p (((maja_h (AX) (BX) (AZ)) * (maja_h2 (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_two_u1h2 (AX) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_40_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_40_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_40_non_alias_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_41_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH33 : (afpoint_represents BX BY Q_r_eq_a )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_r_eq_a <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_r_eq_a <> ECInfinity)) (PreH38 : (r_pre = a_pre)) (PreH39 : (retval = 0)) (PreH40 : (retval_2 = 0)) (PreH41 : (retval_3 = 0)) ,
  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (Zmod (((mont_p ((maja_h3 (AX) (BX) (AZ)))) + (mont_p ((maja_two_u1h2 (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (0 <= (maja_r (AY) (BY) (AZ))) ” 
  &&  “ ((maja_r (AY) (BY) (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_41_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH33 : (afpoint_represents BX BY Q_r_eq_a )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_r_eq_a <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_r_eq_a <> ECInfinity)) (PreH38 : (r_pre = a_pre)) (PreH39 : (retval = 0)) (PreH40 : (retval_2 = 0)) (PreH41 : (retval_3 = 0)) ,
  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (Zmod (((mont_p ((maja_h3 (AX) (BX) (AZ)))) + (mont_p ((maja_two_u1h2 (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
|--
  “ (0 <= (maja_r (AY) (BY) (AZ))) ” 
  &&  “ ((maja_r (AY) (BY) (AZ)) < SM2_P_Z) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (Zmod (((mont_p ((maja_h3 (AX) (BX) (AZ)))) + (mont_p ((maja_two_u1h2 (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_41_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_41_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_41_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_42_non_alias_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_non_alias )) (PreH33 : (afpoint_represents BX BY Q_non_alias )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_non_alias <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (Zmod (((mont_p ((maja_h3 (AX) (BX) (AZ)))) + (mont_p ((maja_two_u1h2 (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= (maja_r (AY) (BY) (AZ))) ” 
  &&  “ ((maja_r (AY) (BY) (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_42_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_non_alias )) (PreH33 : (afpoint_represents BX BY Q_non_alias )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_non_alias <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (Zmod (((mont_p ((maja_h3 (AX) (BX) (AZ)))) + (mont_p ((maja_two_u1h2 (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= (maja_r (AY) (BY) (AZ))) ” 
  &&  “ ((maja_r (AY) (BY) (AZ)) < SM2_P_Z) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (Zmod (((mont_p ((maja_h3 (AX) (BX) (AZ)))) + (mont_p ((maja_two_u1h2 (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_42_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_42_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_42_non_alias_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_43_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (((maja_r (AY) (BY) (AZ)) * (maja_r (AY) (BY) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (Zmod (((mont_p ((maja_h3 (AX) (BX) (AZ)))) + (mont_p ((maja_two_u1h2 (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x")) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_43_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (((maja_r (AY) (BY) (AZ)) * (maja_r (AY) (BY) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (Zmod (((mont_p ((maja_h3 (AX) (BX) (AZ)))) + (mont_p ((maja_two_u1h2 (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_r2 (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_x_adjust (AX) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_43_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_43_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_43_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_44_non_alias_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (((maja_r (AY) (BY) (AZ)) * (maja_r (AY) (BY) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (Zmod (((mont_p ((maja_h3 (AX) (BX) (AZ)))) + (mont_p ((maja_two_u1h2 (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x")) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_44_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (((maja_r (AY) (BY) (AZ)) * (maja_r (AY) (BY) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (Zmod (((mont_p ((maja_h3 (AX) (BX) (AZ)))) + (mont_p ((maja_two_u1h2 (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_r2 (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_x_adjust (AX) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_44_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_44_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_44_non_alias_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_45_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH33 : (afpoint_represents BX BY Q_r_eq_a )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_r_eq_a <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_r_eq_a <> ECInfinity)) (PreH38 : (r_pre = a_pre)) (PreH39 : (retval = 0)) (PreH40 : (retval_2 = 0)) (PreH41 : (retval_3 = 0)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (Zmod (((mont_p ((maja_r2 (AY) (BY) (AZ)))) - (mont_p ((maja_x_adjust (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_x_adjust (AX) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
|--
  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_46_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_non_alias )) (PreH33 : (afpoint_represents BX BY Q_non_alias )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_non_alias <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (Zmod (((mont_p ((maja_r2 (AY) (BY) (AZ)))) - (mont_p ((maja_x_adjust (AX) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_x_adjust (AX) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_47_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "T" ) ) (Zmod (((mont_p ((maja_u1h2 (AX) (BX) (AZ)))) - (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (maja_r (AY) (BY) (AZ))) ” 
  &&  “ ((maja_r (AY) (BY) (AZ)) < SM2_P_Z) ” 
  &&  “ (0 <= (maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY))) ” 
  &&  “ ((maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_47_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH32 : (afpoint_represents BX BY Q_r_eq_a )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_r_eq_a <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_r_eq_a <> ECInfinity)) (PreH37 : (r_pre = a_pre)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "T" ) ) (Zmod (((mont_p ((maja_u1h2 (AX) (BX) (AZ)))) - (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (maja_r (AY) (BY) (AZ))) ” 
  &&  “ ((maja_r (AY) (BY) (AZ)) < SM2_P_Z) ” 
  &&  “ (0 <= (maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY))) ” 
  &&  “ ((maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)) < SM2_P_Z) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_47_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_47_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_47_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_48_non_alias_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "T" ) ) (Zmod (((mont_p ((maja_u1h2 (AX) (BX) (AZ)))) - (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (maja_r (AY) (BY) (AZ))) ” 
  &&  “ ((maja_r (AY) (BY) (AZ)) < SM2_P_Z) ” 
  &&  “ (0 <= (maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY))) ” 
  &&  “ ((maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_48_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "T" ) ) (Zmod (((mont_p ((maja_u1h2 (AX) (BX) (AZ)))) - (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (maja_r (AY) (BY) (AZ))) ” 
  &&  “ ((maja_r (AY) (BY) (AZ)) < SM2_P_Z) ” 
  &&  “ (0 <= (maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY))) ” 
  &&  “ ((maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)) < SM2_P_Z) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_48_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_48_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_48_non_alias_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_49_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH33 : (afpoint_represents BX BY Q_r_eq_a )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_r_eq_a <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_r_eq_a <> ECInfinity)) (PreH38 : (r_pre = a_pre)) (PreH39 : (retval = 0)) (PreH40 : (retval_2 = 0)) (PreH41 : (retval_3 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((maja_r (AY) (BY) (AZ)) * (maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h3 (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h3 (AX) (BX) (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_49_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH33 : (afpoint_represents BX BY Q_r_eq_a )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_r_eq_a <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_r_eq_a <> ECInfinity)) (PreH38 : (r_pre = a_pre)) (PreH39 : (retval = 0)) (PreH40 : (retval_2 = 0)) (PreH41 : (retval_3 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((maja_r (AY) (BY) (AZ)) * (maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h3 (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h3 (AX) (BX) (AZ)) < SM2_P_Z) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((maja_r (AY) (BY) (AZ)) * (maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)) ))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_49_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_49_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_49_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_50_non_alias_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_non_alias )) (PreH33 : (afpoint_represents BX BY Q_non_alias )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_non_alias <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((maja_r (AY) (BY) (AZ)) * (maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= AY) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h3 (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h3 (AX) (BX) (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_50_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_non_alias )) (PreH33 : (afpoint_represents BX BY Q_non_alias )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_non_alias <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((maja_r (AY) (BY) (AZ)) * (maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= AY) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h3 (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h3 (AX) (BX) (AZ)) < SM2_P_Z) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((maja_r (AY) (BY) (AZ)) * (maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)) ))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_50_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_50_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_50_non_alias_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_51_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y"))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH33 : (afpoint_represents BX BY Q_r_eq_a )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_r_eq_a <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_r_eq_a <> ECInfinity)) (PreH38 : (r_pre = a_pre)) (PreH39 : (retval = 0)) (PreH40 : (retval_2 = 0)) (PreH41 : (retval_3 = 0)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p ((AY * (maja_h3 (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((maja_r (AY) (BY) (AZ)) * (maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)) ))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "y") = &((r_pre)  # "JPoint" ->ₛ "y")) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_51_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y"))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH33 : (afpoint_represents BX BY Q_r_eq_a )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_r_eq_a <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_r_eq_a <> ECInfinity)) (PreH38 : (r_pre = a_pre)) (PreH39 : (retval = 0)) (PreH40 : (retval_2 = 0)) (PreH41 : (retval_3 = 0)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p ((AY * (maja_h3 (AX) (BX) (AZ)) ))) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((maja_r (AY) (BY) (AZ)) * (maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)) ))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "y") = &((r_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_51_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_51_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_51_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_52_non_alias_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p ((AY * (maja_h3 (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((maja_r (AY) (BY) (AZ)) * (maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)) ))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "y") = &((r_pre)  # "JPoint" ->ₛ "y")) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_52_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH3 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH4 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH5 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) (PreH16 : ((mont_p (BY)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (BY)))) (PreH18 : ((mont_p (BX)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BX)))) (PreH20 : (AZ <> 0)) (PreH21 : (AZ < SM2_P_Z)) (PreH22 : (0 <= AZ)) (PreH23 : (AY < SM2_P_Z)) (PreH24 : (0 <= AY)) (PreH25 : (AX < SM2_P_Z)) (PreH26 : (0 <= AX)) (PreH27 : (BY < SM2_P_Z)) (PreH28 : (0 <= BY)) (PreH29 : (BX < SM2_P_Z)) (PreH30 : (0 <= BX)) (PreH31 : (jpoint_represents AX AY AZ P_non_alias )) (PreH32 : (afpoint_represents BX BY Q_non_alias )) (PreH33 : (retval_2 = 0)) (PreH34 : (Q_non_alias <> ECInfinity)) (PreH35 : (retval = 0)) (PreH36 : (P_non_alias <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) (PreH39 : (retval_3 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p ((AY * (maja_h3 (AX) (BX) (AZ)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((maja_r (AY) (BY) (AZ)) * (maja_e_minus_rx (AX) (AY) (AZ) (BX) (BY)) ))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "y") = &((r_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_52_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_52_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_52_non_alias_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_53_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((r_pre)  # "JPoint" ->ₛ "y"))) (PreH2 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y"))) (PreH3 : (retval_3 = 0)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH34 : (afpoint_represents BX BY Q_r_eq_a )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_r_eq_a <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_r_eq_a <> ECInfinity)) (PreH39 : (r_pre = a_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 = 0)) ,
  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "z") = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h (AX) (BX) (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_53_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((r_pre)  # "JPoint" ->ₛ "y"))) (PreH2 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y"))) (PreH3 : (retval_3 = 0)) (PreH4 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH5 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH6 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH7 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH8 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : ((mont_p (BY)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (BY)))) (PreH20 : ((mont_p (BX)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (BX)))) (PreH22 : (AZ <> 0)) (PreH23 : (AZ < SM2_P_Z)) (PreH24 : (0 <= AZ)) (PreH25 : (AY < SM2_P_Z)) (PreH26 : (0 <= AY)) (PreH27 : (AX < SM2_P_Z)) (PreH28 : (0 <= AX)) (PreH29 : (BY < SM2_P_Z)) (PreH30 : (0 <= BY)) (PreH31 : (BX < SM2_P_Z)) (PreH32 : (0 <= BX)) (PreH33 : (jpoint_represents AX AY AZ P_r_eq_a )) (PreH34 : (afpoint_represents BX BY Q_r_eq_a )) (PreH35 : (retval_2 = 0)) (PreH36 : (Q_r_eq_a <> ECInfinity)) (PreH37 : (retval = 0)) (PreH38 : (P_r_eq_a <> ECInfinity)) (PreH39 : (r_pre = a_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) (PreH42 : (retval_3 = 0)) ,
  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "z") = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h (AX) (BX) (AZ)) < SM2_P_Z) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "y") = &((a_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_r_eq_a ) ” 
  &&  “ (afpoint_represents BX BY Q_r_eq_a ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_r_eq_a <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_r_eq_a <> ECInfinity) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_53_r_eq_a := montg_add_jpoint_and_apoint_partial_solve_wit_53_r_eq_a_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_53_r_eq_a_aux.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_54_non_alias_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((r_pre)  # "JPoint" ->ₛ "y"))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_non_alias )) (PreH33 : (afpoint_represents BX BY Q_non_alias )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_non_alias <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "by" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "bx" ) )) # Ptr  |-> &((b_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= AZ) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h (AX) (BX) (AZ)) < SM2_P_Z) ”
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_54_non_alias_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (retval_2: Z) (AX: Z) (AY: Z) (AZ: Z) (BX: Z) (BY: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_3: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((r_pre)  # "JPoint" ->ₛ "y"))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0)) (PreH4 : ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z)) (PreH5 : (0 <= (mont_p ((maja_r (AY) (BY) (AZ)))))) (PreH6 : ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z)) (PreH7 : (0 <= (mont_p ((maja_h (AX) (BX) (AZ)))))) (PreH8 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : ((mont_p (BY)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (BY)))) (PreH19 : ((mont_p (BX)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (BX)))) (PreH21 : (AZ <> 0)) (PreH22 : (AZ < SM2_P_Z)) (PreH23 : (0 <= AZ)) (PreH24 : (AY < SM2_P_Z)) (PreH25 : (0 <= AY)) (PreH26 : (AX < SM2_P_Z)) (PreH27 : (0 <= AX)) (PreH28 : (BY < SM2_P_Z)) (PreH29 : (0 <= BY)) (PreH30 : (BX < SM2_P_Z)) (PreH31 : (0 <= BX)) (PreH32 : (jpoint_represents AX AY AZ P_non_alias )) (PreH33 : (afpoint_represents BX BY Q_non_alias )) (PreH34 : (retval_2 = 0)) (PreH35 : (Q_non_alias <> ECInfinity)) (PreH36 : (retval = 0)) (PreH37 : (P_non_alias <> ECInfinity)) (PreH38 : (retval = 0)) (PreH39 : (retval_2 = 0)) (PreH40 : (retval_3 = 0)) ,
  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (0 <= AZ) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= (maja_h (AX) (BX) (AZ))) ” 
  &&  “ ((maja_h (AX) (BX) (AZ)) < SM2_P_Z) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) <> 0) ” 
  &&  “ ((mont_p ((maja_r (AY) (BY) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_r (AY) (BY) (AZ))))) ” 
  &&  “ ((mont_p ((maja_h (AX) (BX) (AZ)))) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p ((maja_h (AX) (BX) (AZ))))) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (BY)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BY))) ” 
  &&  “ ((mont_p (BX)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (BX))) ” 
  &&  “ (AZ <> 0) ” 
  &&  “ (AZ < SM2_P_Z) ” 
  &&  “ (0 <= AZ) ” 
  &&  “ (AY < SM2_P_Z) ” 
  &&  “ (0 <= AY) ” 
  &&  “ (AX < SM2_P_Z) ” 
  &&  “ (0 <= AX) ” 
  &&  “ (BY < SM2_P_Z) ” 
  &&  “ (0 <= BY) ” 
  &&  “ (BX < SM2_P_Z) ” 
  &&  “ (0 <= BX) ” 
  &&  “ (jpoint_represents AX AY AZ P_non_alias ) ” 
  &&  “ (afpoint_represents BX BY Q_non_alias ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Q_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (AZ)) )
  **  (store_fp ( &( "C" ) ) (mont_p ((maja_h (AX) (BX) (AZ)))) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) (mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (Zmod (((mont_p ((maja_r_times_delta (AX) (AY) (AZ) (BX) (BY)))) - (mont_p ((maja_y1h3 (AX) (AY) (BX) (AZ)))) )) (SM2_P_Z)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (AY)) )
  **  (store_fp ( &( "Ccub" ) ) (mont_p ((maja_h3 (AX) (BX) (AZ)))) )
  **  (store_fp ( &( "D" ) ) (mont_p ((maja_r (AY) (BY) (AZ)))) )
  **  (store_fp ( &( "E" ) ) (mont_p ((maja_u1h2 (AX) (BX) (AZ)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((maja_rx (AX) (AY) (AZ) (BX) (BY)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (AX)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_fp ( &( "B" ) ) (mont_p ((maja_s2 (BY) (AZ)))) )
  **  (store_fp ( &( "A" ) ) (mont_p ((maja_u2 (BX) (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "y") (mont_p (BY)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((maja_z2 (AZ)))) )
  **  (store_fp &((b_pre)  # "AFPoint" ->ₛ "x") (mont_p (BX)) )
  **  (store_montg_one )
.

Definition montg_add_jpoint_and_apoint_partial_solve_wit_54_non_alias := montg_add_jpoint_and_apoint_partial_solve_wit_54_non_alias_pure -> montg_add_jpoint_and_apoint_partial_solve_wit_54_non_alias_aux.

Definition montg_add_jpoint_and_apoint_which_implies_wit_1 := 
(
  (store_bn_zero )
|--
  (store_u256_limbs ( &( "BN_ZERO" ) ) 0 )
) \/
(
  (store_bn_zero )
|--
  EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Module Type VC_Correct.

Include montg_add_jpoint_and_apoint_precompute_Strategy_Correct.
Include montg_add_jpoint_and_apoint_x_Strategy_Correct.
Include montg_add_jpoint_and_apoint_y_Strategy_Correct.
Include sm2_representation_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_point_overwrite_Strategy_Correct.
Include ecc_point_facts_Strategy_Correct.
Include montg_add_jpoint_and_apoint_compare_Strategy_Correct.
Include montg_add_jpoint_and_apoint_result_Strategy_Correct.
Include montg_add_jpoint_and_apoint_cleanup_Strategy_Correct.

Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_1_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_2_non_alias : montg_add_jpoint_and_apoint_safety_wit_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_3_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_3_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_4_non_alias : montg_add_jpoint_and_apoint_safety_wit_4_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_5_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_5_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_6_non_alias : montg_add_jpoint_and_apoint_safety_wit_6_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_7_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_7_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_8_non_alias : montg_add_jpoint_and_apoint_safety_wit_8_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_9_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_9_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_10_non_alias : montg_add_jpoint_and_apoint_safety_wit_10_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_11_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_11_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_12_non_alias : montg_add_jpoint_and_apoint_safety_wit_12_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_13_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_13_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_14_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_14_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_15_non_alias : montg_add_jpoint_and_apoint_safety_wit_15_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_16_non_alias : montg_add_jpoint_and_apoint_safety_wit_16_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_17_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_17_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_18_non_alias : montg_add_jpoint_and_apoint_safety_wit_18_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_19_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_19_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_20_non_alias : montg_add_jpoint_and_apoint_safety_wit_20_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_21_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_21_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_22_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_22_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_23_non_alias : montg_add_jpoint_and_apoint_safety_wit_23_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_24_non_alias : montg_add_jpoint_and_apoint_safety_wit_24_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_25_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_25_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_26_non_alias : montg_add_jpoint_and_apoint_safety_wit_26_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_27_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_27_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_28_non_alias : montg_add_jpoint_and_apoint_safety_wit_28_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_29_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_29_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_30_non_alias : montg_add_jpoint_and_apoint_safety_wit_30_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_31_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_31_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_32_non_alias : montg_add_jpoint_and_apoint_safety_wit_32_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_33_r_eq_a : montg_add_jpoint_and_apoint_safety_wit_33_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_safety_wit_34_non_alias : montg_add_jpoint_and_apoint_safety_wit_34_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_1_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_1_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_1_2_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_1_2_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_1_3_non_alias : montg_add_jpoint_and_apoint_entail_wit_1_3_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_1_4_non_alias : montg_add_jpoint_and_apoint_entail_wit_1_4_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_2_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_2_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_2_2_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_2_2_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_2_3_non_alias : montg_add_jpoint_and_apoint_entail_wit_2_3_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_2_4_non_alias : montg_add_jpoint_and_apoint_entail_wit_2_4_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_3_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_3_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_3_2_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_3_2_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_3_3_non_alias : montg_add_jpoint_and_apoint_entail_wit_3_3_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_3_4_non_alias : montg_add_jpoint_and_apoint_entail_wit_3_4_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_4_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_4_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_4_2_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_4_2_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_4_3_non_alias : montg_add_jpoint_and_apoint_entail_wit_4_3_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_4_4_non_alias : montg_add_jpoint_and_apoint_entail_wit_4_4_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_5_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_5_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_5_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_5_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_6_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_6_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_6_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_6_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_7_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_7_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_7_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_7_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_8_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_8_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_8_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_8_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_9_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_9_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_9_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_9_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_10_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_10_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_10_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_10_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_11_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_11_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_11_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_11_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_12_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_12_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_12_2_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_12_2_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_12_3_non_alias : montg_add_jpoint_and_apoint_entail_wit_12_3_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_12_4_non_alias : montg_add_jpoint_and_apoint_entail_wit_12_4_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_13_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_13_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_13_2_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_13_2_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_13_3_non_alias : montg_add_jpoint_and_apoint_entail_wit_13_3_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_13_4_non_alias : montg_add_jpoint_and_apoint_entail_wit_13_4_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_14_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_14_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_14_2_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_14_2_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_14_3_non_alias : montg_add_jpoint_and_apoint_entail_wit_14_3_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_14_4_non_alias : montg_add_jpoint_and_apoint_entail_wit_14_4_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_15_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_15_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_15_2_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_15_2_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_15_3_non_alias : montg_add_jpoint_and_apoint_entail_wit_15_3_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_15_4_non_alias : montg_add_jpoint_and_apoint_entail_wit_15_4_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_16_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_16_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_16_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_16_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_17_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_17_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_17_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_17_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_18_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_18_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_18_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_18_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_19_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_19_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_19_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_19_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_20_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_20_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_20_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_20_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_21_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_21_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_21_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_21_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_22_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_22_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_22_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_22_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_23_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_23_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_23_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_23_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_24_1_r_eq_a : montg_add_jpoint_and_apoint_entail_wit_24_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_entail_wit_24_2_non_alias : montg_add_jpoint_and_apoint_entail_wit_24_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_return_wit_1_r_eq_a : montg_add_jpoint_and_apoint_return_wit_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_return_wit_2_non_alias : montg_add_jpoint_and_apoint_return_wit_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_return_wit_3_r_eq_a : montg_add_jpoint_and_apoint_return_wit_3_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_return_wit_4_non_alias : montg_add_jpoint_and_apoint_return_wit_4_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_return_wit_5_r_eq_a : montg_add_jpoint_and_apoint_return_wit_5_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_return_wit_6_non_alias : montg_add_jpoint_and_apoint_return_wit_6_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_return_wit_7_r_eq_a : montg_add_jpoint_and_apoint_return_wit_7_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_return_wit_8_non_alias : montg_add_jpoint_and_apoint_return_wit_8_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_return_wit_9_r_eq_a : montg_add_jpoint_and_apoint_return_wit_9_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_return_wit_10_non_alias : montg_add_jpoint_and_apoint_return_wit_10_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_1_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_2_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_2_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_3_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_3_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_4_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_4_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_5_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_5_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_6_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_6_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_7_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_7_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_7_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_7_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_8_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_8_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_9_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_9_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_9_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_9_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_10_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_10_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_10_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_10_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_11_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_11_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_11_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_11_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_12_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_12_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_12_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_12_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_13_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_13_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_13_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_13_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_14_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_14_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_14_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_14_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_15_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_15_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_15_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_15_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_16_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_16_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_16_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_16_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_17_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_17_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_18_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_18_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_19_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_19_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_20_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_20_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_21_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_21_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_22_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_22_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_23_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_23_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_24_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_24_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_25_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_25_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_26_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_26_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_27_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_27_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_27_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_27_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_28_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_28_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_28_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_28_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_29_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_29_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_30_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_30_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_31_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_31_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_31_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_31_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_32_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_32_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_32_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_32_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_33_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_33_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_33_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_33_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_34_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_34_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_34_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_34_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_35_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_35_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_35_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_35_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_36_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_36_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_36_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_36_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_37_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_37_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_38_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_38_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_39_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_39_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_39_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_39_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_40_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_40_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_40_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_40_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_41_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_41_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_41_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_41_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_42_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_42_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_42_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_42_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_43_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_43_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_43_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_43_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_44_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_44_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_44_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_44_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_45_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_45_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_46_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_46_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_47_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_47_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_47_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_47_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_48_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_48_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_48_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_48_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_49_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_49_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_49_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_49_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_50_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_50_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_50_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_50_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_51_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_51_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_51_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_51_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_52_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_52_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_52_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_52_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_53_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_53_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_53_r_eq_a : montg_add_jpoint_and_apoint_partial_solve_wit_53_r_eq_a.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_54_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_54_non_alias_pure.
Axiom proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_54_non_alias : montg_add_jpoint_and_apoint_partial_solve_wit_54_non_alias.
Axiom proof_of_montg_add_jpoint_and_apoint_which_implies_wit_1 : montg_add_jpoint_and_apoint_which_implies_wit_1.

End VC_Correct.
