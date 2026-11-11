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
Require Import SimpleC.EE.Applications_human.sm2.lib.sm2_no_three_torsion.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_overwrite_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_overwrite_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import wnaf3_precomp_points_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import wnaf3_precomp_points_strategy_proof.

(*----- Function montg_pre_compute_naf_w3 -----*)

Definition montg_pre_compute_naf_w3_safety_wit_1 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UndefStructPredJPoint ( &( "dr" ) ) )
  **  (UndefStructPredJPoint ( &( "r" ) ) )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_pre_compute_naf_w3_safety_wit_2 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UndefStructPredJPoint ( &( "dr" ) ) )
  **  (UndefStructPredJPoint ( &( "r" ) ) )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_pre_compute_naf_w3_safety_wit_3 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UndefStructPredJPoint ( &( "dr" ) ) )
  **  (UndefStructPredJPoint ( &( "r" ) ) )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_pre_compute_naf_w3_safety_wit_4 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (BasePoint_non_alias <> ECInfinity)) ,
  (UndefStructPredu32 &(( &( "r" ) )->ₛ "z") )
  **  (UndefStructPredu32 &(( &( "r" ) )->ₛ "y") )
  **  (UndefStructPredu32 &(( &( "r" ) )->ₛ "x") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "z") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "y") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "x") )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_sm2_p )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_rhop )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_pre_compute_naf_w3_safety_wit_5 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (retval = 1)) (PreH3 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_jpoint ( &( "r" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_pre_compute_naf_w3_safety_wit_6 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (retval = 1)) (PreH3 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_jpoint ( &( "r" ) ) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition montg_pre_compute_naf_w3_safety_wit_7 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((sm2_point_mul (3) (BasePoint_non_alias)) <> ECInfinity)) (PreH2 : (retval_3 = 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (retval = 1)) (PreH5 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_jpoint ( &( "r" ) ) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (3 * sizeof( "AFPoint" ))) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition montg_pre_compute_naf_w3_safety_wit_8 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((sm2_point_mul (3) (BasePoint_non_alias)) <> ECInfinity)) (PreH2 : (retval_3 = 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (retval = 1)) (PreH5 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_jpoint ( &( "r" ) ) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (3 * sizeof( "AFPoint" ))) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition montg_pre_compute_naf_w3_entail_wit_1 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (UndefStructPredJPoint ( &( "dr" ) ) )
  **  (UndefStructPredJPoint ( &( "r" ) ) )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (wnaf3_precomp_undef PT_pre NT_pre )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UndefStructPredJPoint ( &( "dr" ) ) )
  **  (UndefStructPredJPoint ( &( "r" ) ) )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_pre_compute_naf_w3_entail_wit_2 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_sm2_p )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_rhop )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UndefStructPredJPoint ( &( "dr" ) ) )
  **  (UndefStructPredJPoint ( &( "r" ) ) )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (retval = 1) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (UndefStructPredu32 &(( &( "r" ) )->ₛ "z") )
  **  (UndefStructPredu32 &(( &( "r" ) )->ₛ "y") )
  **  (UndefStructPredu32 &(( &( "r" ) )->ₛ "x") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "z") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "y") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "x") )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_sm2_p )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_rhop )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_pre_compute_naf_w3_entail_wit_3 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (retval = 1)) (PreH3 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "r" ) ) BasePoint_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "z") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "y") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "x") )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_sm2_p )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_rhop )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
|--
  “ (retval_2 = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "r" ) ) BasePoint_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "z") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "y") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "x") )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_sm2_p )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_rhop )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
.

Definition montg_pre_compute_naf_w3_entail_wit_4 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((sm2_point_mul (3) (BasePoint_non_alias)) <> ECInfinity)) (PreH2 : (retval_3 = 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (retval = 1)) (PreH5 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_afpoint (PT_pre + (3 * sizeof( "AFPoint" ))) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_mont_afpoint (NT_pre + (3 * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul (3) (BasePoint_non_alias)))) )
  **  (store_sm2_p )
  **  (store_mont_jpoint ( &( "r" ) ) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
|--
  “ ((sm2_point_mul (3) (BasePoint_non_alias)) <> ECInfinity) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_wnaf3_precomp PT_pre NT_pre BasePoint_non_alias )
  **  (store_sm2_p )
  **  (store_mont_jpoint ( &( "r" ) ) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
.

Definition montg_pre_compute_naf_w3_return_wit_1 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((sm2_point_mul (3) (BasePoint_non_alias)) <> ECInfinity)) (PreH2 : (retval_3 = 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (retval = 1)) (PreH5 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_wnaf3_precomp PT_pre NT_pre BasePoint_non_alias )
  **  (store_sm2_p )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_rhop )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
|--
  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_mont_wnaf3_precomp PT_pre NT_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_pre_compute_naf_w3_partial_solve_wit_1 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UndefStructPredJPoint ( &( "dr" ) ) )
  **  (UndefStructPredJPoint ( &( "r" ) ) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (UInt64Array.undef_full &(((PT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UndefStructPredJPoint ( &( "dr" ) ) )
  **  (UndefStructPredJPoint ( &( "r" ) ) )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_pre_compute_naf_w3_partial_solve_wit_2_pure := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UndefStructPredJPoint ( &( "dr" ) ) )
  **  (UndefStructPredJPoint ( &( "r" ) ) )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (BasePoint_non_alias <> ECInfinity) ”
.

Definition montg_pre_compute_naf_w3_partial_solve_wit_2_aux := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UndefStructPredJPoint ( &( "dr" ) ) )
  **  (UndefStructPredJPoint ( &( "r" ) ) )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (BasePoint_non_alias <> ECInfinity) ” 
  &&  “ (retval = 1) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (1 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_rhop )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UndefStructPredJPoint ( &( "dr" ) ) )
  **  (UndefStructPredJPoint ( &( "r" ) ) )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_pre_compute_naf_w3_partial_solve_wit_2 := montg_pre_compute_naf_w3_partial_solve_wit_2_pure -> montg_pre_compute_naf_w3_partial_solve_wit_2_aux.

Definition montg_pre_compute_naf_w3_partial_solve_wit_3 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (BasePoint_non_alias <> ECInfinity)) ,
  (UndefStructPredu32 &(( &( "r" ) )->ₛ "z") )
  **  (UndefStructPredu32 &(( &( "r" ) )->ₛ "y") )
  **  (UndefStructPredu32 &(( &( "r" ) )->ₛ "x") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "z") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "y") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "x") )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_sm2_p )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_rhop )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (retval = 1) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (UInt64Array.undef_full &(( &( "r" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "r" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "r" ) )->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "z") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "y") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "x") )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_sm2_p )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_rhop )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
.

Definition montg_pre_compute_naf_w3_partial_solve_wit_4 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (retval = 1)) (PreH3 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "r" ) ) BasePoint_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "z") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "y") )
  **  (UndefStructPredu32 &(( &( "dr" ) )->ₛ "x") )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_sm2_p )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_rhop )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
|--
  “ (retval_2 = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_jpoint ( &( "r" ) ) BasePoint_non_alias )
  **  (UInt64Array.undef_full &(( &( "dr" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "dr" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "dr" ) )->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
.

Definition montg_pre_compute_naf_w3_partial_solve_wit_5 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (retval = 1)) (PreH3 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_jpoint ( &( "r" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
|--
  “ (retval_2 = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (UInt64Array.undef_full &(( &( "r" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "r" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "r" ) )->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
.

Definition montg_pre_compute_naf_w3_partial_solve_wit_6 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (retval = 1)) (PreH3 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "r" ) ) (sm2_point_add ((sm2_point_double (BasePoint_non_alias))) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
|--
  “ (retval_2 = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_jpoint ( &( "r" ) ) (sm2_point_add ((sm2_point_double (BasePoint_non_alias))) (BasePoint_non_alias)) )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
.

Definition montg_pre_compute_naf_w3_partial_solve_wit_7 := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (retval = 1)) (PreH3 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_jpoint ( &( "r" ) ) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
|--
  “ (retval_2 = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_jpoint ( &( "r" ) ) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((PT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
.

Definition montg_pre_compute_naf_w3_partial_solve_wit_8_pure := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (retval_2 = 1)) (PreH3 : (retval = 1)) (PreH4 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_jpoint ( &( "r" ) ) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (3 * sizeof( "AFPoint" ))) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
|--
  “ (BasePoint_non_alias <> ECInfinity) ”
.

Definition montg_pre_compute_naf_w3_partial_solve_wit_8_aux := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (retval_2 = 1)) (PreH3 : (retval = 1)) (PreH4 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_jpoint ( &( "r" ) ) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (3 * sizeof( "AFPoint" ))) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
|--
  “ (BasePoint_non_alias <> ECInfinity) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_jpoint ( &( "r" ) ) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (3 * sizeof( "AFPoint" ))) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
.

Definition montg_pre_compute_naf_w3_partial_solve_wit_8 := montg_pre_compute_naf_w3_partial_solve_wit_8_pure -> montg_pre_compute_naf_w3_partial_solve_wit_8_aux.

Definition montg_pre_compute_naf_w3_partial_solve_wit_9_pure := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((sm2_point_mul (3) (BasePoint_non_alias)) <> ECInfinity)) (PreH2 : (retval_3 = 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (retval = 1)) (PreH5 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_jpoint ( &( "r" ) ) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (3 * sizeof( "AFPoint" ))) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  ((( &( "apoint" ) )) # Ptr  |-> apoint_pre)
  **  ((( &( "PT" ) )) # Ptr  |-> PT_pre)
  **  ((( &( "NT" ) )) # Ptr  |-> NT_pre)
|--
  “ ((sm2_point_mul (3) (BasePoint_non_alias)) <> ECInfinity) ”
.

Definition montg_pre_compute_naf_w3_partial_solve_wit_9_aux := 
forall (NT_pre: Z) (PT_pre: Z) (apoint_pre: Z) (BasePoint_non_alias: ec_point) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((sm2_point_mul (3) (BasePoint_non_alias)) <> ECInfinity)) (PreH2 : (retval_3 = 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (retval = 1)) (PreH5 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_jpoint ( &( "r" ) ) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (3 * sizeof( "AFPoint" ))) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
|--
  “ ((sm2_point_mul (3) (BasePoint_non_alias)) <> ECInfinity) ” 
  &&  “ ((sm2_point_mul (3) (BasePoint_non_alias)) <> ECInfinity) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_afpoint (PT_pre + (3 * sizeof( "AFPoint" ))) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(((NT_pre + (3 * sizeof( "AFPoint" ))))  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_mont_jpoint ( &( "r" ) ) (sm2_point_mul (3) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "dr" ) ) (sm2_point_double (BasePoint_non_alias)) )
  **  (store_mont_afpoint (PT_pre + (1 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_mont_afpoint (NT_pre + (1 * sizeof( "AFPoint" ))) (sm2_point_negate (BasePoint_non_alias)) )
  **  (store_afpoint apoint_pre BasePoint_non_alias )
  **  (store_sm2_h )
.

Definition montg_pre_compute_naf_w3_partial_solve_wit_9 := montg_pre_compute_naf_w3_partial_solve_wit_9_pure -> montg_pre_compute_naf_w3_partial_solve_wit_9_aux.

Definition montg_pre_compute_naf_w3_which_implies_wit_1 := 
(
forall (BasePoint_non_alias: ec_point) ,
  (store_mont_jpoint ( &( "r" ) ) (sm2_point_add ((sm2_point_double (BasePoint_non_alias))) (BasePoint_non_alias)) )
|--
  (store_mont_jpoint ( &( "r" ) ) (sm2_point_mul (3) (BasePoint_non_alias)) )
) \/
(
forall (BasePoint_non_alias: ec_point) ,
  (store_mont_jpoint ( &( "r" ) ) (sm2_point_add ((sm2_point_double (BasePoint_non_alias))) (BasePoint_non_alias)) )
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
  &&  “ (jpoint_represents x y z (sm2_point_mul (3) (BasePoint_non_alias)) ) ”
  &&  (((&(( &( "r" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "r" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "r" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "r" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "r" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "r" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "r" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "r" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Definition montg_pre_compute_naf_w3_which_implies_wit_2 := 
(
forall (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  TT && emp 
|--
  “ ((sm2_point_mul (3) (BasePoint_non_alias)) <> ECInfinity) ”
  &&  emp
) \/
(
forall (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  TT && emp 
|--
  “ ((sm2_point_mul (3) (BasePoint_non_alias)) <> ECInfinity) ”
  &&  emp
).

Definition montg_pre_compute_naf_w3_which_implies_wit_2_split_goal_1 := 
forall (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  ((sm2_point_mul (3) (BasePoint_non_alias)) <> ECInfinity)
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_point_copy_steps_Strategy_Correct.
Include ecc_point_overwrite_Strategy_Correct.
Include wnaf3_precomp_points_Strategy_Correct.

Axiom proof_of_montg_pre_compute_naf_w3_safety_wit_1 : montg_pre_compute_naf_w3_safety_wit_1.
Axiom proof_of_montg_pre_compute_naf_w3_safety_wit_2 : montg_pre_compute_naf_w3_safety_wit_2.
Axiom proof_of_montg_pre_compute_naf_w3_safety_wit_3 : montg_pre_compute_naf_w3_safety_wit_3.
Axiom proof_of_montg_pre_compute_naf_w3_safety_wit_4 : montg_pre_compute_naf_w3_safety_wit_4.
Axiom proof_of_montg_pre_compute_naf_w3_safety_wit_5 : montg_pre_compute_naf_w3_safety_wit_5.
Axiom proof_of_montg_pre_compute_naf_w3_safety_wit_6 : montg_pre_compute_naf_w3_safety_wit_6.
Axiom proof_of_montg_pre_compute_naf_w3_safety_wit_7 : montg_pre_compute_naf_w3_safety_wit_7.
Axiom proof_of_montg_pre_compute_naf_w3_safety_wit_8 : montg_pre_compute_naf_w3_safety_wit_8.
Axiom proof_of_montg_pre_compute_naf_w3_entail_wit_1 : montg_pre_compute_naf_w3_entail_wit_1.
Axiom proof_of_montg_pre_compute_naf_w3_entail_wit_2 : montg_pre_compute_naf_w3_entail_wit_2.
Axiom proof_of_montg_pre_compute_naf_w3_entail_wit_3 : montg_pre_compute_naf_w3_entail_wit_3.
Axiom proof_of_montg_pre_compute_naf_w3_entail_wit_4 : montg_pre_compute_naf_w3_entail_wit_4.
Axiom proof_of_montg_pre_compute_naf_w3_return_wit_1 : montg_pre_compute_naf_w3_return_wit_1.
Axiom proof_of_montg_pre_compute_naf_w3_partial_solve_wit_1 : montg_pre_compute_naf_w3_partial_solve_wit_1.
Axiom proof_of_montg_pre_compute_naf_w3_partial_solve_wit_2_pure : montg_pre_compute_naf_w3_partial_solve_wit_2_pure.
Axiom proof_of_montg_pre_compute_naf_w3_partial_solve_wit_2 : montg_pre_compute_naf_w3_partial_solve_wit_2.
Axiom proof_of_montg_pre_compute_naf_w3_partial_solve_wit_3 : montg_pre_compute_naf_w3_partial_solve_wit_3.
Axiom proof_of_montg_pre_compute_naf_w3_partial_solve_wit_4 : montg_pre_compute_naf_w3_partial_solve_wit_4.
Axiom proof_of_montg_pre_compute_naf_w3_partial_solve_wit_5 : montg_pre_compute_naf_w3_partial_solve_wit_5.
Axiom proof_of_montg_pre_compute_naf_w3_partial_solve_wit_6 : montg_pre_compute_naf_w3_partial_solve_wit_6.
Axiom proof_of_montg_pre_compute_naf_w3_partial_solve_wit_7 : montg_pre_compute_naf_w3_partial_solve_wit_7.
Axiom proof_of_montg_pre_compute_naf_w3_partial_solve_wit_8_pure : montg_pre_compute_naf_w3_partial_solve_wit_8_pure.
Axiom proof_of_montg_pre_compute_naf_w3_partial_solve_wit_8 : montg_pre_compute_naf_w3_partial_solve_wit_8.
Axiom proof_of_montg_pre_compute_naf_w3_partial_solve_wit_9_pure : montg_pre_compute_naf_w3_partial_solve_wit_9_pure.
Axiom proof_of_montg_pre_compute_naf_w3_partial_solve_wit_9 : montg_pre_compute_naf_w3_partial_solve_wit_9.
Axiom proof_of_montg_pre_compute_naf_w3_which_implies_wit_1 : montg_pre_compute_naf_w3_which_implies_wit_1.
Axiom proof_of_montg_pre_compute_naf_w3_which_implies_wit_2 : montg_pre_compute_naf_w3_which_implies_wit_2.

End VC_Correct.
