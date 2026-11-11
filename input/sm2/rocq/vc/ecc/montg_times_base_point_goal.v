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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import montg_times_base_point_def.
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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_basepoint_mul.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import basepoint_bytes_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import basepoint_bytes_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import basepoint_table_points_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import basepoint_table_points_strategy_proof.

(*----- Function montg_times_base_point -----*)

Definition montg_times_base_point_safety_wit_1 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_2 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) ,
  ((( &( "byteIdx" ) )) # UChar  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_3 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) ,
  ((( &( "pk" ) )) # Ptr  |->_)
  **  ((( &( "byteIdx" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_4 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) ,
  ((( &( "pT" ) )) # Ptr  |->_)
  **  ((( &( "pk" ) )) # Ptr  |-> 0)
  **  ((( &( "byteIdx" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_5 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (PreH1 : (sm2_mont_base_table_correct )) (PreH2 : (0 <= K_non_alias)) (PreH3 : (K_non_alias < SM2_N_Z)) (PreH4 : ((Zlength (byte_list)) = 32)) (PreH5 : (u8_list_bounded byte_list )) (PreH6 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH7 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  ((( &( "pT" ) )) # Ptr  |-> 0)
  **  ((( &( "pk" ) )) # Ptr  |-> 0)
  **  ((( &( "byteIdx" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_6 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (PreH1 : (sm2_mont_base_table_correct )) (PreH2 : (0 <= K_non_alias)) (PreH3 : (K_non_alias < SM2_N_Z)) (PreH4 : ((Zlength (byte_list)) = 32)) (PreH5 : (u8_list_bounded byte_list )) (PreH6 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH7 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  ((( &( "pT" ) )) # Ptr  |-> 0)
  **  ((( &( "pk" ) )) # Ptr  |-> 0)
  **  ((( &( "byteIdx" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_7 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (PreH1 : (sm2_mont_base_table_correct )) (PreH2 : (0 <= K_non_alias)) (PreH3 : (K_non_alias < SM2_N_Z)) (PreH4 : ((Zlength (byte_list)) = 32)) (PreH5 : (u8_list_bounded byte_list )) (PreH6 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH7 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 8 (sublist (0) (8) (byte_list)) )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  ((( &( "pT" ) )) # Ptr  |-> 0)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "byteIdx" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_8 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (PreH1 : (0 <= (Znth 0 (sublist (0) (8) (byte_list)) 0))) (PreH2 : ((Znth 0 (sublist (0) (8) (byte_list)) 0) < 256)) (PreH3 : (sm2_mont_base_table_correct )) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (0) (8) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> 0)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 8 (sublist (0) (8) (byte_list)) )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_9 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (PreH1 : (0 <= (Znth 0 (sublist (0) (8) (byte_list)) 0))) (PreH2 : ((Znth 0 (sublist (0) (8) (byte_list)) 0) < 256)) (PreH3 : (sm2_mont_base_table_correct )) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (0) (8) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> 0)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 8 (sublist (0) (8) (byte_list)) )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_10 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= (Znth 0 (sublist (0) (8) (byte_list)) 0))) (PreH3 : ((Znth 0 (sublist (0) (8) (byte_list)) 0) < 256)) (PreH4 : (sm2_mont_base_table_correct )) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (0) (8) (byte_list)) 0)) (0) (0))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (0) (8) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (0 * ((sizeof( "AFPoint" ) * 256) * 8))) + (0 * (sizeof( "AFPoint" ) * 256))) + ((Znth 0 (sublist (0) (8) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_times_base_point_safety_wit_11 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH2 : (1 <= i)) (PreH3 : (i <= 8)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH10 : (sm2_mont_base_table_correct )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full pk 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition montg_times_base_point_safety_wit_12 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PT: Z) (PreH1 : (0 <= (Znth i (sublist (0) (8) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (0) (8) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (0) (8) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  (UCharArray.full pk 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_13 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (( &( "K0" ) ) = ( &( "K0" ) ))) (PreH2 : (0 <= (Znth i (sublist (0) (8) (byte_list)) 0))) (PreH3 : ((Znth i (sublist (0) (8) (byte_list)) 0) < 256)) (PreH4 : (i < 8)) (PreH5 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth i (sublist (0) (8) (byte_list)) 0)) (0) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (0) (8) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (0 * ((sizeof( "AFPoint" ) * 256) * 8))) + (i * (sizeof( "AFPoint" ) * 256))) + ((Znth i (sublist (0) (8) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  (UCharArray.full pk 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition montg_times_base_point_safety_wit_14 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_15 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_times_base_point_safety_wit_16 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_17 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PT: Z) (pk: Z) (PreH1 : (0 <= (Znth 0 (sublist (8) (16) (byte_list)) 0))) (PreH2 : ((Znth 0 (sublist (8) (16) (byte_list)) 0) < 256)) (PreH3 : (i >= 8)) (PreH4 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (8) (16) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_times_base_point_safety_wit_18 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PT: Z) (pk: Z) (PreH1 : (0 <= (Znth 0 (sublist (8) (16) (byte_list)) 0))) (PreH2 : ((Znth 0 (sublist (8) (16) (byte_list)) 0) < 256)) (PreH3 : (i >= 8)) (PreH4 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (8) (16) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_19 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= (Znth 0 (sublist (8) (16) (byte_list)) 0))) (PreH3 : ((Znth 0 (sublist (8) (16) (byte_list)) 0) < 256)) (PreH4 : (i >= 8)) (PreH5 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (8) (16) (byte_list)) 0)) (1) (0))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (8) (16) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (1 * ((sizeof( "AFPoint" ) * 256) * 8))) + (0 * (sizeof( "AFPoint" ) * 256))) + ((Znth 0 (sublist (8) (16) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_times_base_point_safety_wit_20 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH2 : (1 <= i)) (PreH3 : (i <= 8)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH10 : (sm2_mont_base_table_correct )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full pk 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition montg_times_base_point_safety_wit_21 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PT: Z) (PreH1 : (0 <= (Znth i (sublist (8) (16) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (8) (16) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (8) (16) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  (UCharArray.full pk 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_times_base_point_safety_wit_22 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (( &( "K1" ) ) = ( &( "K1" ) ))) (PreH2 : (0 <= (Znth i (sublist (8) (16) (byte_list)) 0))) (PreH3 : ((Znth i (sublist (8) (16) (byte_list)) 0) < 256)) (PreH4 : (i < 8)) (PreH5 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth i (sublist (8) (16) (byte_list)) 0)) (1) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (8) (16) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (1 * ((sizeof( "AFPoint" ) * 256) * 8))) + (i * (sizeof( "AFPoint" ) * 256))) + ((Znth i (sublist (8) (16) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  (UCharArray.full pk 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition montg_times_base_point_safety_wit_23 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_24 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition montg_times_base_point_safety_wit_25 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_26 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PT: Z) (pk: Z) (PreH1 : (0 <= (Znth 0 (sublist (16) (24) (byte_list)) 0))) (PreH2 : ((Znth 0 (sublist (16) (24) (byte_list)) 0) < 256)) (PreH3 : (i >= 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (16) (24) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition montg_times_base_point_safety_wit_27 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PT: Z) (pk: Z) (PreH1 : (0 <= (Znth 0 (sublist (16) (24) (byte_list)) 0))) (PreH2 : ((Znth 0 (sublist (16) (24) (byte_list)) 0) < 256)) (PreH3 : (i >= 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (16) (24) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_28 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= (Znth 0 (sublist (16) (24) (byte_list)) 0))) (PreH3 : ((Znth 0 (sublist (16) (24) (byte_list)) 0) < 256)) (PreH4 : (i >= 8)) (PreH5 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (16) (24) (byte_list)) 0)) (2) (0))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (16) (24) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (2 * ((sizeof( "AFPoint" ) * 256) * 8))) + (0 * (sizeof( "AFPoint" ) * 256))) + ((Znth 0 (sublist (16) (24) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_times_base_point_safety_wit_29 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH2 : (1 <= i)) (PreH3 : (i <= 8)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH10 : (sm2_mont_base_table_correct )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full pk 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition montg_times_base_point_safety_wit_30 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PT: Z) (PreH1 : (0 <= (Znth i (sublist (16) (24) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (16) (24) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (16) (24) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  (UCharArray.full pk 8 (sublist (16) (24) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition montg_times_base_point_safety_wit_31 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (( &( "K2" ) ) = ( &( "K2" ) ))) (PreH2 : (0 <= (Znth i (sublist (16) (24) (byte_list)) 0))) (PreH3 : ((Znth i (sublist (16) (24) (byte_list)) 0) < 256)) (PreH4 : (i < 8)) (PreH5 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth i (sublist (16) (24) (byte_list)) 0)) (2) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (16) (24) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (2 * ((sizeof( "AFPoint" ) * 256) * 8))) + (i * (sizeof( "AFPoint" ) * 256))) + ((Znth i (sublist (16) (24) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  (UCharArray.full pk 8 (sublist (16) (24) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition montg_times_base_point_safety_wit_32 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_33 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition montg_times_base_point_safety_wit_34 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_35 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PT: Z) (pk: Z) (PreH1 : (0 <= (Znth 0 (sublist (24) (32) (byte_list)) 0))) (PreH2 : ((Znth 0 (sublist (24) (32) (byte_list)) 0) < 256)) (PreH3 : (i >= 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (24) (32) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition montg_times_base_point_safety_wit_36 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PT: Z) (pk: Z) (PreH1 : (0 <= (Znth 0 (sublist (24) (32) (byte_list)) 0))) (PreH2 : ((Znth 0 (sublist (24) (32) (byte_list)) 0) < 256)) (PreH3 : (i >= 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (24) (32) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_base_point_safety_wit_37 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= (Znth 0 (sublist (24) (32) (byte_list)) 0))) (PreH3 : ((Znth 0 (sublist (24) (32) (byte_list)) 0) < 256)) (PreH4 : (i >= 8)) (PreH5 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (24) (32) (byte_list)) 0)) (3) (0))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (24) (32) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (3 * ((sizeof( "AFPoint" ) * 256) * 8))) + (0 * (sizeof( "AFPoint" ) * 256))) + ((Znth 0 (sublist (24) (32) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_times_base_point_safety_wit_38 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH2 : (1 <= i)) (PreH3 : (i <= 8)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH10 : (sm2_mont_base_table_correct )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full pk 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition montg_times_base_point_safety_wit_39 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PT: Z) (PreH1 : (0 <= (Znth i (sublist (24) (32) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (24) (32) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (24) (32) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  (UCharArray.full pk 8 (sublist (24) (32) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition montg_times_base_point_safety_wit_40 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (( &( "K3" ) ) = ( &( "K3" ) ))) (PreH2 : (0 <= (Znth i (sublist (24) (32) (byte_list)) 0))) (PreH3 : ((Znth i (sublist (24) (32) (byte_list)) 0) < 256)) (PreH4 : (i < 8)) (PreH5 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth i (sublist (24) (32) (byte_list)) 0)) (3) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (24) (32) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (3 * ((sizeof( "AFPoint" ) * 256) * 8))) + (i * (sizeof( "AFPoint" ) * 256))) + ((Znth i (sublist (24) (32) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  (UCharArray.full pk 8 (sublist (24) (32) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition montg_times_base_point_entail_wit_1 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (PreH1 : (0 <= K_non_alias)) (PreH2 : (K_non_alias < SM2_N_Z)) (PreH3 : ((Zlength (byte_list)) = 32)) (PreH4 : (u8_list_bounded byte_list )) (PreH5 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH6 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  ((( &( "pT" ) )) # Ptr  |-> 0)
  **  ((( &( "pk" ) )) # Ptr  |-> 0)
  **  ((( &( "byteIdx" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ”
  &&  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  ((( &( "pT" ) )) # Ptr  |-> 0)
  **  ((( &( "pk" ) )) # Ptr  |-> 0)
  **  ((( &( "byteIdx" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_entail_wit_2 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (PreH1 : (sm2_mont_base_table_correct )) (PreH2 : (0 <= K_non_alias)) (PreH3 : (K_non_alias < SM2_N_Z)) (PreH4 : ((Zlength (byte_list)) = 32)) (PreH5 : (u8_list_bounded byte_list )) (PreH6 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH7 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  ((( &( "pT" ) )) # Ptr  |-> 0)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "byteIdx" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (sm2_mont_base_table_correct ) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ”
  &&  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 8 (sublist (0) (8) (byte_list)) )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  ((( &( "pT" ) )) # Ptr  |-> 0)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "byteIdx" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_entail_wit_3 := 
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= (Znth 0 (sublist (0) (8) (byte_list)) 0))) (PreH3 : ((Znth 0 (sublist (0) (8) (byte_list)) 0) < 256)) (PreH4 : (sm2_mont_base_table_correct )) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (0) (8) (byte_list)) 0)) (0) (0))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = &((k_pre)  # "u32" ->ₛ "v")) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (1))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
) \/
(
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= (Znth 0 (sublist (0) (8) (byte_list)) 0))) (PreH3 : ((Znth 0 (sublist (0) (8) (byte_list)) 0) < 256)) (PreH4 : (sm2_mont_base_table_correct )) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (0) (8) (byte_list)) 0)) (0) (0))) (SM2_G_POINT)) )
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
  &&  “ (jpoint_represents x y z (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (1))) (SM2_G_POINT)) ) ” 
  &&  “ ((&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = &((k_pre)  # "u32" ->ₛ "v")) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
).

Definition montg_times_base_point_entail_wit_4 := 
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (( &( "K0" ) ) = ( &( "K0" ) ))) (PreH2 : (0 <= (Znth i (sublist (0) (8) (byte_list)) 0))) (PreH3 : ((Znth i (sublist (0) (8) (byte_list)) 0) < 256)) (PreH4 : (i < 8)) (PreH5 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth i (sublist (0) (8) (byte_list)) 0)) (0) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UCharArray.full pk 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (pk = &((k_pre)  # "u32" ->ₛ "v")) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full pk 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) ((i + 1 )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
) \/
(
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth i (sublist (0) (8) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (0) (8) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth i (sublist (0) (8) (byte_list)) 0)) (0) (i))) (SM2_G_POINT)))) )
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
  &&  “ (jpoint_represents x y z (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) ((i + 1 )))) (SM2_G_POINT)) ) ” 
  &&  “ (pk = &((k_pre)  # "u32" ->ₛ "v")) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
).

Definition montg_times_base_point_entail_wit_5 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full pk 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = &((k_pre)  # "u32" ->ₛ "v")) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_entail_wit_6 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = &((k_pre)  # "u32" ->ₛ "v")) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_entail_wit_7 := 
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= (Znth 0 (sublist (8) (16) (byte_list)) 0))) (PreH3 : ((Znth 0 (sublist (8) (16) (byte_list)) 0) < 256)) (PreH4 : (i >= 8)) (PreH5 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (8) (16) (byte_list)) 0)) (1) (0))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (1))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
) \/
(
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= (Znth 0 (sublist (8) (16) (byte_list)) 0))) (PreH3 : ((Znth 0 (sublist (8) (16) (byte_list)) 0) < 256)) (PreH4 : (i >= 8)) (PreH5 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (8) (16) (byte_list)) 0)) (1) (0))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (z_2: Z)  (y_2: Z)  (x_2: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (z: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p (x_2)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ ((mont_p (x_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (x_2))) ” 
  &&  “ ((mont_p (y_2)) = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ ((mont_p (y_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (y_2))) ” 
  &&  “ ((mont_p (z_2)) = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ ((mont_p (z_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (z_2))) ” 
  &&  “ (z_2 < SM2_P_Z) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (1))) (SM2_G_POINT)) ) ” 
  &&  “ ((mont_p (x)) = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
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
  &&  “ (jpoint_represents x y z (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (((&(( &( "K1" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "K1" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "K1" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "K1" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "K1" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "K1" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "K1" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "K1" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "K1" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "K1" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "K1" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "K1" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
).

Definition montg_times_base_point_entail_wit_8 := 
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (( &( "K1" ) ) = ( &( "K1" ) ))) (PreH2 : (0 <= (Znth i (sublist (8) (16) (byte_list)) 0))) (PreH3 : ((Znth i (sublist (8) (16) (byte_list)) 0) < 256)) (PreH4 : (i < 8)) (PreH5 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth i (sublist (8) (16) (byte_list)) 0)) (1) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UCharArray.full pk 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full pk 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) ((i + 1 )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
) \/
(
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth i (sublist (8) (16) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (8) (16) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth i (sublist (8) (16) (byte_list)) 0)) (1) (i))) (SM2_G_POINT)))) )
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
  &&  “ (jpoint_represents x y z (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) ((i + 1 )))) (SM2_G_POINT)) ) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (((&(( &( "K1" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "K1" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "K1" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "K1" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "K1" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "K1" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "K1" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "K1" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "K1" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "K1" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "K1" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "K1" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
).

Definition montg_times_base_point_entail_wit_9 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full pk 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_entail_wit_10 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_entail_wit_11 := 
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= (Znth 0 (sublist (16) (24) (byte_list)) 0))) (PreH3 : ((Znth 0 (sublist (16) (24) (byte_list)) 0) < 256)) (PreH4 : (i >= 8)) (PreH5 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (16) (24) (byte_list)) 0)) (2) (0))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (1))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
) \/
(
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= (Znth 0 (sublist (16) (24) (byte_list)) 0))) (PreH3 : ((Znth 0 (sublist (16) (24) (byte_list)) 0) < 256)) (PreH4 : (i >= 8)) (PreH5 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (16) (24) (byte_list)) 0)) (2) (0))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (z_2: Z)  (y_2: Z)  (x_2: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (z: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p (x_2)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ ((mont_p (x_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (x_2))) ” 
  &&  “ ((mont_p (y_2)) = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ ((mont_p (y_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (y_2))) ” 
  &&  “ ((mont_p (z_2)) = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ ((mont_p (z_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (z_2))) ” 
  &&  “ (z_2 < SM2_P_Z) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (1))) (SM2_G_POINT)) ) ” 
  &&  “ ((mont_p (x)) = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
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
  &&  “ (jpoint_represents x y z (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (((&(( &( "K2" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "K2" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "K2" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "K2" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "K2" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "K2" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "K2" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "K2" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "K2" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "K2" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "K2" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "K2" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "K1" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "K1" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "K1" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "K1" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "K1" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "K1" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "K1" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "K1" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "K1" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "K1" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "K1" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "K1" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
).

Definition montg_times_base_point_entail_wit_12 := 
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (( &( "K2" ) ) = ( &( "K2" ) ))) (PreH2 : (0 <= (Znth i (sublist (16) (24) (byte_list)) 0))) (PreH3 : ((Znth i (sublist (16) (24) (byte_list)) 0) < 256)) (PreH4 : (i < 8)) (PreH5 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth i (sublist (16) (24) (byte_list)) 0)) (2) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UCharArray.full pk 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full pk 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) ((i + 1 )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
) \/
(
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth i (sublist (16) (24) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (16) (24) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth i (sublist (16) (24) (byte_list)) 0)) (2) (i))) (SM2_G_POINT)))) )
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
  &&  “ (jpoint_represents x y z (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) ((i + 1 )))) (SM2_G_POINT)) ) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (((&(( &( "K2" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "K2" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "K2" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "K2" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "K2" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "K2" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "K2" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "K2" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "K2" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "K2" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "K2" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "K2" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
).

Definition montg_times_base_point_entail_wit_13 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full pk 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_entail_wit_14 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_entail_wit_15 := 
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= (Znth 0 (sublist (24) (32) (byte_list)) 0))) (PreH3 : ((Znth 0 (sublist (24) (32) (byte_list)) 0) < 256)) (PreH4 : (i >= 8)) (PreH5 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (24) (32) (byte_list)) 0)) (3) (0))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (1))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
) \/
(
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (0 <= (Znth 0 (sublist (24) (32) (byte_list)) 0))) (PreH3 : ((Znth 0 (sublist (24) (32) (byte_list)) 0) < 256)) (PreH4 : (i >= 8)) (PreH5 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (24) (32) (byte_list)) 0)) (3) (0))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (z_2: Z)  (y_2: Z)  (x_2: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (z: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p (x_2)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ ((mont_p (x_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (x_2))) ” 
  &&  “ ((mont_p (y_2)) = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ ((mont_p (y_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (y_2))) ” 
  &&  “ ((mont_p (z_2)) = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ ((mont_p (z_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (z_2))) ” 
  &&  “ (z_2 < SM2_P_Z) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (1))) (SM2_G_POINT)) ) ” 
  &&  “ ((mont_p (x)) = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
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
  &&  “ (jpoint_represents x y z (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (((&(( &( "K3" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "K3" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "K3" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "K3" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "K3" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "K3" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "K3" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "K3" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "K3" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "K3" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "K3" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "K3" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "K2" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "K2" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "K2" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "K2" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "K2" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "K2" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "K2" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "K2" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "K2" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "K2" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "K2" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "K2" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
).

Definition montg_times_base_point_entail_wit_16 := 
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (( &( "K3" ) ) = ( &( "K3" ) ))) (PreH2 : (0 <= (Znth i (sublist (24) (32) (byte_list)) 0))) (PreH3 : ((Znth i (sublist (24) (32) (byte_list)) 0) < 256)) (PreH4 : (i < 8)) (PreH5 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH6 : (1 <= i)) (PreH7 : (i <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth i (sublist (24) (32) (byte_list)) 0)) (3) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UCharArray.full pk 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full pk 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) ((i + 1 )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
) \/
(
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth i (sublist (24) (32) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (24) (32) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth i (sublist (24) (32) (byte_list)) 0)) (3) (i))) (SM2_G_POINT)))) )
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
  &&  “ (jpoint_represents x y z (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) ((i + 1 )))) (SM2_G_POINT)) ) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (((&(( &( "K3" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "K3" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "K3" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "K3" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "K3" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "K3" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "K3" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "K3" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "K3" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "K3" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "K3" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "K3" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
).

Definition montg_times_base_point_entail_wit_17 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full pk 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_entail_wit_18 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (store_mont_jpoint result_pre (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (store_mont_jpoint result_pre (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
.

Definition montg_times_base_point_entail_wit_19 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (store_mont_jpoint result_pre (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (store_mont_jpoint result_pre (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
.

Definition montg_times_base_point_return_wit_1 := 
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (store_sm2_mont_base_point_table )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint result_pre (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
|--
  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint result_pre (sm2_point_mul (K_non_alias) (SM2_G_POINT)) )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
) \/
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (store_sm2_mont_base_point_table )
  **  (store_mont_jpoint result_pre (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
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
  &&  “ (jpoint_represents x y z (sm2_point_mul (K_non_alias) (SM2_G_POINT)) ) ”
  &&  (((&((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
).

Definition montg_times_base_point_partial_solve_wit_1 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) ,
  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  (store_fn k_pre K_non_alias )
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_2 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (PreH1 : (0 <= K_non_alias)) (PreH2 : (K_non_alias < SM2_N_Z)) (PreH3 : ((Zlength (byte_list)) = 32)) (PreH4 : (u8_list_bounded byte_list )) (PreH5 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH6 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ”
  &&  (store_sm2_mont_base_point_table )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_3 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (PreH1 : (sm2_mont_base_table_correct )) (PreH2 : (0 <= K_non_alias)) (PreH3 : (K_non_alias < SM2_N_Z)) (PreH4 : ((Zlength (byte_list)) = 32)) (PreH5 : (u8_list_bounded byte_list )) (PreH6 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH7 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 8 (sublist (0) (8) (byte_list)) )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (sm2_mont_base_table_correct ) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ”
  &&  ((((&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth 0 (sublist (0) (8) (byte_list)) 0))
  **  (UCharArray.missing_i (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 0 0 8 (sublist (0) (8) (byte_list)) )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_4_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (PreH1 : (sm2_mont_base_table_correct )) (PreH2 : (0 <= K_non_alias)) (PreH3 : (K_non_alias < SM2_N_Z)) (PreH4 : ((Zlength (byte_list)) = 32)) (PreH5 : (u8_list_bounded byte_list )) (PreH6 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH7 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 8 (sublist (0) (8) (byte_list)) )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  ((( &( "pT" ) )) # Ptr  |-> 0)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (0) (8) (byte_list)) 0))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((Znth 0 (sublist (0) (8) (byte_list)) 0) = (Znth 0 (sublist (0) (8) (byte_list)) 0)) ”
.

Definition montg_times_base_point_partial_solve_wit_4_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (PreH1 : (sm2_mont_base_table_correct )) (PreH2 : (0 <= K_non_alias)) (PreH3 : (K_non_alias < SM2_N_Z)) (PreH4 : ((Zlength (byte_list)) = 32)) (PreH5 : (u8_list_bounded byte_list )) (PreH6 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH7 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 8 (sublist (0) (8) (byte_list)) )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((Znth 0 (sublist (0) (8) (byte_list)) 0) = (Znth 0 (sublist (0) (8) (byte_list)) 0)) ” 
  &&  “ (sm2_mont_base_table_correct ) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ”
  &&  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 8 (sublist (0) (8) (byte_list)) )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_4 := montg_times_base_point_partial_solve_wit_4_pure -> montg_times_base_point_partial_solve_wit_4_aux.

Definition montg_times_base_point_partial_solve_wit_5 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (PreH1 : (0 <= (Znth 0 (sublist (0) (8) (byte_list)) 0))) (PreH2 : ((Znth 0 (sublist (0) (8) (byte_list)) 0) < 256)) (PreH3 : (sm2_mont_base_table_correct )) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 8 (sublist (0) (8) (byte_list)) )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UndefStructPredJPoint ( &( "K0" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (record_afpoint_well_formed (sm2_mont_base_table_record_at (0) (0) ((Znth 0 (sublist (0) (8) (byte_list)) 0))) ) ” 
  &&  “ (0 <= (Znth 0 (sublist (0) (8) (byte_list)) 0)) ” 
  &&  “ ((Znth 0 (sublist (0) (8) (byte_list)) 0) < 256) ” 
  &&  “ (sm2_mont_base_table_correct ) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ”
  &&  (store_mont_afpoint (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (0 * ((sizeof( "AFPoint" ) * 256) * 8))) + (0 * (sizeof( "AFPoint" ) * 256))) + ((Znth 0 (sublist (0) (8) (byte_list)) 0) * sizeof( "AFPoint" ))) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (0) (8) (byte_list)) 0)) (0) (0))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K0" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K0" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K0" ) )->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (StructAFPointArray.missing_i ( &( "g_montg_AFTable_for_base_point_mul" ) ) ((((0 * 8 ) * 256 ) + (0 * 256 ) ) + (Znth 0 (sublist (0) (8) (byte_list)) 0) ) 0 SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UndefStructPredJPoint ( &( "K3" ) ) )
  **  (UndefStructPredJPoint ( &( "K2" ) ) )
  **  (UndefStructPredJPoint ( &( "K1" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_times_base_point_partial_solve_wit_6 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i < 8)) (PreH2 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full pk 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i < 8) ” 
  &&  “ (pk = &((k_pre)  # "u32" ->ₛ "v")) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (((pk + (i * sizeof(UCHAR)))) # UChar  |-> (Znth i (sublist (0) (8) (byte_list)) 0))
  **  (UCharArray.missing_i pk i 0 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_7_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PT: Z) (PreH1 : (i < 8)) (PreH2 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full pk 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (0) (8) (byte_list)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Znth i (sublist (0) (8) (byte_list)) 0) = (Znth i (sublist (0) (8) (byte_list)) 0)) ”
.

Definition montg_times_base_point_partial_solve_wit_7_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i < 8)) (PreH2 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full pk 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Znth i (sublist (0) (8) (byte_list)) 0) = (Znth i (sublist (0) (8) (byte_list)) 0)) ” 
  &&  “ (i < 8) ” 
  &&  “ (pk = &((k_pre)  # "u32" ->ₛ "v")) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full pk 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_7 := montg_times_base_point_partial_solve_wit_7_pure -> montg_times_base_point_partial_solve_wit_7_aux.

Definition montg_times_base_point_partial_solve_wit_8_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth i (sublist (0) (8) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (0) (8) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (0) (8) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (0 * ((sizeof( "AFPoint" ) * 256) * 8))) + (i * (sizeof( "AFPoint" ) * 256))) + ((Znth i (sublist (0) (8) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  (UCharArray.full pk 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "K0" ) ) = ( &( "K0" ) )) ”
.

Definition montg_times_base_point_partial_solve_wit_8_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth i (sublist (0) (8) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (0) (8) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full pk 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "K0" ) ) = ( &( "K0" ) )) ” 
  &&  “ (record_afpoint_well_formed (sm2_mont_base_table_record_at (0) (i) ((Znth i (sublist (0) (8) (byte_list)) 0))) ) ” 
  &&  “ (0 <= (Znth i (sublist (0) (8) (byte_list)) 0)) ” 
  &&  “ ((Znth i (sublist (0) (8) (byte_list)) 0) < 256) ” 
  &&  “ (i < 8) ” 
  &&  “ (pk = &((k_pre)  # "u32" ->ₛ "v")) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (store_mont_afpoint (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (0 * ((sizeof( "AFPoint" ) * 256) * 8))) + (i * (sizeof( "AFPoint" ) * 256))) + ((Znth i (sublist (0) (8) (byte_list)) 0) * sizeof( "AFPoint" ))) (sm2_point_mul ((sm2_table_term ((Znth i (sublist (0) (8) (byte_list)) 0)) (0) (i))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (StructAFPointArray.missing_i ( &( "g_montg_AFTable_for_base_point_mul" ) ) ((((0 * 8 ) * 256 ) + (i * 256 ) ) + (Znth i (sublist (0) (8) (byte_list)) 0) ) 0 SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full pk 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_base_point_partial_solve_wit_8 := montg_times_base_point_partial_solve_wit_8_pure -> montg_times_base_point_partial_solve_wit_8_aux.

Definition montg_times_base_point_partial_solve_wit_9 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = &((k_pre)  # "u32" ->ₛ "v")) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  ((((&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth 0 (sublist (8) (16) (byte_list)) 0))
  **  (UCharArray.missing_i (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 0 0 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_10_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (8) (16) (byte_list)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((Znth 0 (sublist (8) (16) (byte_list)) 0) = (Znth 0 (sublist (8) (16) (byte_list)) 0)) ”
.

Definition montg_times_base_point_partial_solve_wit_10_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((Znth 0 (sublist (8) (16) (byte_list)) 0) = (Znth 0 (sublist (8) (16) (byte_list)) 0)) ” 
  &&  “ (i >= 8) ” 
  &&  “ (pk = &((k_pre)  # "u32" ->ₛ "v")) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_10 := montg_times_base_point_partial_solve_wit_10_pure -> montg_times_base_point_partial_solve_wit_10_aux.

Definition montg_times_base_point_partial_solve_wit_11 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth 0 (sublist (8) (16) (byte_list)) 0))) (PreH2 : ((Znth 0 (sublist (8) (16) (byte_list)) 0) < 256)) (PreH3 : (i >= 8)) (PreH4 : (pk = &((k_pre)  # "u32" ->ₛ "v"))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (record_afpoint_well_formed (sm2_mont_base_table_record_at (1) (0) ((Znth 0 (sublist (8) (16) (byte_list)) 0))) ) ” 
  &&  “ (0 <= (Znth 0 (sublist (8) (16) (byte_list)) 0)) ” 
  &&  “ ((Znth 0 (sublist (8) (16) (byte_list)) 0) < 256) ” 
  &&  “ (i >= 8) ” 
  &&  “ (pk = &((k_pre)  # "u32" ->ₛ "v")) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (store_mont_afpoint (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (1 * ((sizeof( "AFPoint" ) * 256) * 8))) + (0 * (sizeof( "AFPoint" ) * 256))) + ((Znth 0 (sublist (8) (16) (byte_list)) 0) * sizeof( "AFPoint" ))) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (8) (16) (byte_list)) 0)) (1) (0))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (StructAFPointArray.missing_i ( &( "g_montg_AFTable_for_base_point_mul" ) ) ((((1 * 8 ) * 256 ) + (0 * 256 ) ) + (Znth 0 (sublist (8) (16) (byte_list)) 0) ) 0 SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_times_base_point_partial_solve_wit_12 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i < 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full pk 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i < 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (((pk + (i * sizeof(UCHAR)))) # UChar  |-> (Znth i (sublist (8) (16) (byte_list)) 0))
  **  (UCharArray.missing_i pk i 0 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_13_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PT: Z) (PreH1 : (i < 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full pk 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (8) (16) (byte_list)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Znth i (sublist (8) (16) (byte_list)) 0) = (Znth i (sublist (8) (16) (byte_list)) 0)) ”
.

Definition montg_times_base_point_partial_solve_wit_13_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i < 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full pk 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Znth i (sublist (8) (16) (byte_list)) 0) = (Znth i (sublist (8) (16) (byte_list)) 0)) ” 
  &&  “ (i < 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full pk 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_13 := montg_times_base_point_partial_solve_wit_13_pure -> montg_times_base_point_partial_solve_wit_13_aux.

Definition montg_times_base_point_partial_solve_wit_14_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth i (sublist (8) (16) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (8) (16) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (8) (16) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (1 * ((sizeof( "AFPoint" ) * 256) * 8))) + (i * (sizeof( "AFPoint" ) * 256))) + ((Znth i (sublist (8) (16) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  (UCharArray.full pk 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "K1" ) ) = ( &( "K1" ) )) ”
.

Definition montg_times_base_point_partial_solve_wit_14_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth i (sublist (8) (16) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (8) (16) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full pk 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "K1" ) ) = ( &( "K1" ) )) ” 
  &&  “ (record_afpoint_well_formed (sm2_mont_base_table_record_at (1) (i) ((Znth i (sublist (8) (16) (byte_list)) 0))) ) ” 
  &&  “ (0 <= (Znth i (sublist (8) (16) (byte_list)) 0)) ” 
  &&  “ ((Znth i (sublist (8) (16) (byte_list)) 0) < 256) ” 
  &&  “ (i < 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (store_mont_afpoint (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (1 * ((sizeof( "AFPoint" ) * 256) * 8))) + (i * (sizeof( "AFPoint" ) * 256))) + ((Znth i (sublist (8) (16) (byte_list)) 0) * sizeof( "AFPoint" ))) (sm2_point_mul ((sm2_table_term ((Znth i (sublist (8) (16) (byte_list)) 0)) (1) (i))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (StructAFPointArray.missing_i ( &( "g_montg_AFTable_for_base_point_mul" ) ) ((((1 * 8 ) * 256 ) + (i * 256 ) ) + (Znth i (sublist (8) (16) (byte_list)) 0) ) 0 SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full pk 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_base_point_partial_solve_wit_14 := montg_times_base_point_partial_solve_wit_14_pure -> montg_times_base_point_partial_solve_wit_14_aux.

Definition montg_times_base_point_partial_solve_wit_15 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  ((((&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth 0 (sublist (16) (24) (byte_list)) 0))
  **  (UCharArray.missing_i (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 0 0 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_16_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (16) (24) (byte_list)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((Znth 0 (sublist (16) (24) (byte_list)) 0) = (Znth 0 (sublist (16) (24) (byte_list)) 0)) ”
.

Definition montg_times_base_point_partial_solve_wit_16_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((Znth 0 (sublist (16) (24) (byte_list)) 0) = (Znth 0 (sublist (16) (24) (byte_list)) 0)) ” 
  &&  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_16 := montg_times_base_point_partial_solve_wit_16_pure -> montg_times_base_point_partial_solve_wit_16_aux.

Definition montg_times_base_point_partial_solve_wit_17 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth 0 (sublist (16) (24) (byte_list)) 0))) (PreH2 : ((Znth 0 (sublist (16) (24) (byte_list)) 0) < 256)) (PreH3 : (i >= 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (record_afpoint_well_formed (sm2_mont_base_table_record_at (2) (0) ((Znth 0 (sublist (16) (24) (byte_list)) 0))) ) ” 
  &&  “ (0 <= (Znth 0 (sublist (16) (24) (byte_list)) 0)) ” 
  &&  “ ((Znth 0 (sublist (16) (24) (byte_list)) 0) < 256) ” 
  &&  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (store_mont_afpoint (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (2 * ((sizeof( "AFPoint" ) * 256) * 8))) + (0 * (sizeof( "AFPoint" ) * 256))) + ((Znth 0 (sublist (16) (24) (byte_list)) 0) * sizeof( "AFPoint" ))) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (16) (24) (byte_list)) 0)) (2) (0))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K2" ) )->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (StructAFPointArray.missing_i ( &( "g_montg_AFTable_for_base_point_mul" ) ) ((((2 * 8 ) * 256 ) + (0 * 256 ) ) + (Znth 0 (sublist (16) (24) (byte_list)) 0) ) 0 SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_times_base_point_partial_solve_wit_18 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i < 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full pk 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i < 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (((pk + (i * sizeof(UCHAR)))) # UChar  |-> (Znth i (sublist (16) (24) (byte_list)) 0))
  **  (UCharArray.missing_i pk i 0 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_19_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PT: Z) (PreH1 : (i < 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full pk 8 (sublist (16) (24) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (16) (24) (byte_list)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Znth i (sublist (16) (24) (byte_list)) 0) = (Znth i (sublist (16) (24) (byte_list)) 0)) ”
.

Definition montg_times_base_point_partial_solve_wit_19_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i < 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full pk 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Znth i (sublist (16) (24) (byte_list)) 0) = (Znth i (sublist (16) (24) (byte_list)) 0)) ” 
  &&  “ (i < 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full pk 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_19 := montg_times_base_point_partial_solve_wit_19_pure -> montg_times_base_point_partial_solve_wit_19_aux.

Definition montg_times_base_point_partial_solve_wit_20_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth i (sublist (16) (24) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (16) (24) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (16) (24) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (2 * ((sizeof( "AFPoint" ) * 256) * 8))) + (i * (sizeof( "AFPoint" ) * 256))) + ((Znth i (sublist (16) (24) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  (UCharArray.full pk 8 (sublist (16) (24) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "K2" ) ) = ( &( "K2" ) )) ”
.

Definition montg_times_base_point_partial_solve_wit_20_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth i (sublist (16) (24) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (16) (24) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full pk 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "K2" ) ) = ( &( "K2" ) )) ” 
  &&  “ (record_afpoint_well_formed (sm2_mont_base_table_record_at (2) (i) ((Znth i (sublist (16) (24) (byte_list)) 0))) ) ” 
  &&  “ (0 <= (Znth i (sublist (16) (24) (byte_list)) 0)) ” 
  &&  “ ((Znth i (sublist (16) (24) (byte_list)) 0) < 256) ” 
  &&  “ (i < 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (store_mont_afpoint (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (2 * ((sizeof( "AFPoint" ) * 256) * 8))) + (i * (sizeof( "AFPoint" ) * 256))) + ((Znth i (sublist (16) (24) (byte_list)) 0) * sizeof( "AFPoint" ))) (sm2_point_mul ((sm2_table_term ((Znth i (sublist (16) (24) (byte_list)) 0)) (2) (i))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (StructAFPointArray.missing_i ( &( "g_montg_AFTable_for_base_point_mul" ) ) ((((2 * 8 ) * 256 ) + (i * 256 ) ) + (Znth i (sublist (16) (24) (byte_list)) 0) ) 0 SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full pk 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_base_point_partial_solve_wit_20 := montg_times_base_point_partial_solve_wit_20_pure -> montg_times_base_point_partial_solve_wit_20_aux.

Definition montg_times_base_point_partial_solve_wit_21 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  ((((&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth 0 (sublist (24) (32) (byte_list)) 0))
  **  (UCharArray.missing_i (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 0 0 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_22_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth 0 (sublist (24) (32) (byte_list)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((Znth 0 (sublist (24) (32) (byte_list)) 0) = (Znth 0 (sublist (24) (32) (byte_list)) 0)) ”
.

Definition montg_times_base_point_partial_solve_wit_22_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((Znth 0 (sublist (24) (32) (byte_list)) 0) = (Znth 0 (sublist (24) (32) (byte_list)) 0)) ” 
  &&  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_22 := montg_times_base_point_partial_solve_wit_22_pure -> montg_times_base_point_partial_solve_wit_22_aux.

Definition montg_times_base_point_partial_solve_wit_23 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth 0 (sublist (24) (32) (byte_list)) 0))) (PreH2 : ((Znth 0 (sublist (24) (32) (byte_list)) 0) < 256)) (PreH3 : (i >= 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (record_afpoint_well_formed (sm2_mont_base_table_record_at (3) (0) ((Znth 0 (sublist (24) (32) (byte_list)) 0))) ) ” 
  &&  “ (0 <= (Znth 0 (sublist (24) (32) (byte_list)) 0)) ” 
  &&  “ ((Znth 0 (sublist (24) (32) (byte_list)) 0) < 256) ” 
  &&  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (store_mont_afpoint (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (3 * ((sizeof( "AFPoint" ) * 256) * 8))) + (0 * (sizeof( "AFPoint" ) * 256))) + ((Znth 0 (sublist (24) (32) (byte_list)) 0) * sizeof( "AFPoint" ))) (sm2_point_mul ((sm2_table_term ((Znth 0 (sublist (24) (32) (byte_list)) 0)) (3) (0))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "K3" ) )->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (StructAFPointArray.missing_i ( &( "g_montg_AFTable_for_base_point_mul" ) ) ((((3 * 8 ) * 256 ) + (0 * 256 ) ) + (Znth 0 (sublist (24) (32) (byte_list)) 0) ) 0 SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_times_base_point_partial_solve_wit_24 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i < 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (UCharArray.full pk 8 (sublist (24) (32) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i < 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (((pk + (i * sizeof(UCHAR)))) # UChar  |-> (Znth i (sublist (24) (32) (byte_list)) 0))
  **  (UCharArray.missing_i pk i 0 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_25_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PT: Z) (PreH1 : (i < 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full pk 8 (sublist (24) (32) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (24) (32) (byte_list)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Znth i (sublist (24) (32) (byte_list)) 0) = (Znth i (sublist (24) (32) (byte_list)) 0)) ”
.

Definition montg_times_base_point_partial_solve_wit_25_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i < 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full pk 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Znth i (sublist (24) (32) (byte_list)) 0) = (Znth i (sublist (24) (32) (byte_list)) 0)) ” 
  &&  “ (i < 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (UCharArray.full pk 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_25 := montg_times_base_point_partial_solve_wit_25_pure -> montg_times_base_point_partial_solve_wit_25_aux.

Definition montg_times_base_point_partial_solve_wit_26_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth i (sublist (24) (32) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (24) (32) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byteIdx" ) )) # UChar  |-> (Znth i (sublist (24) (32) (byte_list)) 0))
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (3 * ((sizeof( "AFPoint" ) * 256) * 8))) + (i * (sizeof( "AFPoint" ) * 256))) + ((Znth i (sublist (24) (32) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  (UCharArray.full pk 8 (sublist (24) (32) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "K3" ) ) = ( &( "K3" ) )) ”
.

Definition montg_times_base_point_partial_solve_wit_26_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (0 <= (Znth i (sublist (24) (32) (byte_list)) 0))) (PreH2 : ((Znth i (sublist (24) (32) (byte_list)) 0) < 256)) (PreH3 : (i < 8)) (PreH4 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH5 : (1 <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full pk 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "K3" ) ) = ( &( "K3" ) )) ” 
  &&  “ (record_afpoint_well_formed (sm2_mont_base_table_record_at (3) (i) ((Znth i (sublist (24) (32) (byte_list)) 0))) ) ” 
  &&  “ (0 <= (Znth i (sublist (24) (32) (byte_list)) 0)) ” 
  &&  “ ((Znth i (sublist (24) (32) (byte_list)) 0) < 256) ” 
  &&  “ (i < 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (store_mont_afpoint (((( &( "g_montg_AFTable_for_base_point_mul" ) ) + (3 * ((sizeof( "AFPoint" ) * 256) * 8))) + (i * (sizeof( "AFPoint" ) * 256))) + ((Znth i (sublist (24) (32) (byte_list)) 0) * sizeof( "AFPoint" ))) (sm2_point_mul ((sm2_table_term ((Znth i (sublist (24) (32) (byte_list)) 0)) (3) (i))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (StructAFPointArray.missing_i ( &( "g_montg_AFTable_for_base_point_mul" ) ) ((((3 * 8 ) * 256 ) + (i * 256 ) ) + (Znth i (sublist (24) (32) (byte_list)) 0) ) 0 SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (UCharArray.full pk 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_base_point_partial_solve_wit_26 := montg_times_base_point_partial_solve_wit_26_pure -> montg_times_base_point_partial_solve_wit_26_aux.

Definition montg_times_base_point_partial_solve_wit_27_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "K0" ) ) = ( &( "K0" ) )) ”
.

Definition montg_times_base_point_partial_solve_wit_27_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "K0" ) ) = ( &( "K0" ) )) ” 
  &&  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_27 := montg_times_base_point_partial_solve_wit_27_pure -> montg_times_base_point_partial_solve_wit_27_aux.

Definition montg_times_base_point_partial_solve_wit_28 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (( &( "K0" ) ) = ( &( "K0" ) ))) (PreH2 : (i >= 8)) (PreH3 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH4 : (1 <= i)) (PreH5 : (i <= 8)) (PreH6 : (0 <= K_non_alias)) (PreH7 : (K_non_alias < SM2_N_Z)) (PreH8 : ((Zlength (byte_list)) = 32)) (PreH9 : (u8_list_bounded byte_list )) (PreH10 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH11 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH12 : (sm2_mont_base_table_correct )) ,
  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)))) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)))) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_29_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (16))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
|--
  “ (( &( "K0" ) ) = ( &( "K0" ) )) ”
.

Definition montg_times_base_point_partial_solve_wit_29_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (16))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
|--
  “ (( &( "K0" ) ) = ( &( "K0" ) )) ” 
  &&  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (16))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_29 := montg_times_base_point_partial_solve_wit_29_pure -> montg_times_base_point_partial_solve_wit_29_aux.

Definition montg_times_base_point_partial_solve_wit_30 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (( &( "K0" ) ) = ( &( "K0" ) ))) (PreH2 : (i >= 8)) (PreH3 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH4 : (1 <= i)) (PreH5 : (i <= 8)) (PreH6 : (0 <= K_non_alias)) (PreH7 : (K_non_alias < SM2_N_Z)) (PreH8 : ((Zlength (byte_list)) = 32)) (PreH9 : (u8_list_bounded byte_list )) (PreH10 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH11 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH12 : (sm2_mont_base_table_correct )) ,
  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (16))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)))) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (16))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)))) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_31 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
|--
  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) 8 (sublist (24) (32) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 8 (sublist (0) (8) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) 8 (sublist (8) (16) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) 8 (sublist (16) (24) (byte_list)) )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_32_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (B: Z) (PT: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (store_mont_jpoint result_pre (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pk" ) )) # Ptr  |-> pk)
  **  ((( &( "pT" ) )) # Ptr  |-> PT)
  **  ((( &( "byteIdx" ) )) # UChar  |-> B)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
|--
  “ (sm2_mont_base_table_correct ) ”
.

Definition montg_times_base_point_partial_solve_wit_32_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (pk: Z) (PreH1 : (i >= 8)) (PreH2 : (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64))))) (PreH3 : (1 <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_mont_base_table_correct )) ,
  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (store_mont_jpoint result_pre (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_montg_one )
|--
  “ (sm2_mont_base_table_correct ) ” 
  &&  “ (i >= 8) ” 
  &&  “ (pk = (&((k_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_mont_base_table_correct ) ”
  &&  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K3" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)) )
  **  (store_mont_jpoint result_pre (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (3) (i))) (SM2_G_POINT)))) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "K2" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "K1" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)) )
  **  (store_montg_one )
.

Definition montg_times_base_point_partial_solve_wit_32 := montg_times_base_point_partial_solve_wit_32_pure -> montg_times_base_point_partial_solve_wit_32_aux.

Definition montg_times_base_point_which_implies_wit_1 := 
(
forall (K_non_alias: Z) (k: Z) ,
  (store_fn k K_non_alias )
|--
  EX (byte_list: (@list Z)) ,
  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k)  # "u32" ->ₛ "v") ) ”
  &&  (UCharArray.full &((k)  # "u32" ->ₛ "v") 32 byte_list )
) \/
(
forall (K_non_alias: Z) (k: Z) ,
  (store_fn k K_non_alias )
|--
  EX (byte_list: (@list Z)) ,
  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k)  # "u32" ->ₛ "v") ) ”
  &&  (UCharArray.full &((k)  # "u32" ->ₛ "v") 32 byte_list )
).

Definition montg_times_base_point_which_implies_wit_2 := 
(
  (store_sm2_mont_base_point_table )
|--
  “ (sm2_mont_base_table_correct ) ”
  &&  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
) \/
(
  (store_sm2_mont_base_point_table )
|--
  “ (sm2_mont_base_table_correct ) ”
  &&  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
).

Definition montg_times_base_point_which_implies_wit_2_split_goal_1 := 
  (store_sm2_mont_base_point_table )
|--
  “ (sm2_mont_base_table_correct ) ”
.

Definition montg_times_base_point_which_implies_wit_2_split_goal_spatial := 
  (store_sm2_mont_base_point_table )
|--
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
.

Definition montg_times_base_point_which_implies_wit_3 := 
(
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (0) (8) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (0 <= byteIdx) ” 
  &&  “ (byteIdx < 256) ”
  &&  emp
) \/
(
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (0) (8) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (byteIdx < 256) ” 
  &&  “ (0 <= byteIdx) ”
  &&  emp
).

Definition montg_times_base_point_which_implies_wit_3_split_goal_1 := 
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (0) (8) (byte_list)) 0))) ,
  (byteIdx < 256)
.

Definition montg_times_base_point_which_implies_wit_3_split_goal_2 := 
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (0) (8) (byte_list)) 0))) ,
  (0 <= byteIdx)
.

Definition montg_times_base_point_which_implies_wit_4 := 
(
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (0) (8) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (0 <= byteIdx) ” 
  &&  “ (byteIdx < 256) ”
  &&  emp
) \/
(
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (0) (8) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (byteIdx < 256) ” 
  &&  “ (0 <= byteIdx) ”
  &&  emp
).

Definition montg_times_base_point_which_implies_wit_4_split_goal_1 := 
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (0) (8) (byte_list)) 0))) ,
  (byteIdx < 256)
.

Definition montg_times_base_point_which_implies_wit_4_split_goal_2 := 
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (0) (8) (byte_list)) 0))) ,
  (0 <= byteIdx)
.

Definition montg_times_base_point_which_implies_wit_5 := 
(
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (8) (16) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (0 <= byteIdx) ” 
  &&  “ (byteIdx < 256) ”
  &&  emp
) \/
(
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (8) (16) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (byteIdx < 256) ” 
  &&  “ (0 <= byteIdx) ”
  &&  emp
).

Definition montg_times_base_point_which_implies_wit_5_split_goal_1 := 
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (8) (16) (byte_list)) 0))) ,
  (byteIdx < 256)
.

Definition montg_times_base_point_which_implies_wit_5_split_goal_2 := 
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (8) (16) (byte_list)) 0))) ,
  (0 <= byteIdx)
.

Definition montg_times_base_point_which_implies_wit_6 := 
(
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (8) (16) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (0 <= byteIdx) ” 
  &&  “ (byteIdx < 256) ”
  &&  emp
) \/
(
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (8) (16) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (byteIdx < 256) ” 
  &&  “ (0 <= byteIdx) ”
  &&  emp
).

Definition montg_times_base_point_which_implies_wit_6_split_goal_1 := 
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (8) (16) (byte_list)) 0))) ,
  (byteIdx < 256)
.

Definition montg_times_base_point_which_implies_wit_6_split_goal_2 := 
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (8) (16) (byte_list)) 0))) ,
  (0 <= byteIdx)
.

Definition montg_times_base_point_which_implies_wit_7 := 
(
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (16) (24) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (0 <= byteIdx) ” 
  &&  “ (byteIdx < 256) ”
  &&  emp
) \/
(
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (16) (24) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (byteIdx < 256) ” 
  &&  “ (0 <= byteIdx) ”
  &&  emp
).

Definition montg_times_base_point_which_implies_wit_7_split_goal_1 := 
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (16) (24) (byte_list)) 0))) ,
  (byteIdx < 256)
.

Definition montg_times_base_point_which_implies_wit_7_split_goal_2 := 
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (16) (24) (byte_list)) 0))) ,
  (0 <= byteIdx)
.

Definition montg_times_base_point_which_implies_wit_8 := 
(
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (16) (24) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (0 <= byteIdx) ” 
  &&  “ (byteIdx < 256) ”
  &&  emp
) \/
(
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (16) (24) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (byteIdx < 256) ” 
  &&  “ (0 <= byteIdx) ”
  &&  emp
).

Definition montg_times_base_point_which_implies_wit_8_split_goal_1 := 
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (16) (24) (byte_list)) 0))) ,
  (byteIdx < 256)
.

Definition montg_times_base_point_which_implies_wit_8_split_goal_2 := 
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (16) (24) (byte_list)) 0))) ,
  (0 <= byteIdx)
.

Definition montg_times_base_point_which_implies_wit_9 := 
(
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (24) (32) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (0 <= byteIdx) ” 
  &&  “ (byteIdx < 256) ”
  &&  emp
) \/
(
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (24) (32) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (byteIdx < 256) ” 
  &&  “ (0 <= byteIdx) ”
  &&  emp
).

Definition montg_times_base_point_which_implies_wit_9_split_goal_1 := 
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (24) (32) (byte_list)) 0))) ,
  (byteIdx < 256)
.

Definition montg_times_base_point_which_implies_wit_9_split_goal_2 := 
forall (byte_list: (@list Z)) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (byteIdx = (Znth 0 (sublist (24) (32) (byte_list)) 0))) ,
  (0 <= byteIdx)
.

Definition montg_times_base_point_which_implies_wit_10 := 
(
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (24) (32) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (0 <= byteIdx) ” 
  &&  “ (byteIdx < 256) ”
  &&  emp
) \/
(
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (24) (32) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (byteIdx < 256) ” 
  &&  “ (0 <= byteIdx) ”
  &&  emp
).

Definition montg_times_base_point_which_implies_wit_10_split_goal_1 := 
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (24) (32) (byte_list)) 0))) ,
  (byteIdx < 256)
.

Definition montg_times_base_point_which_implies_wit_10_split_goal_2 := 
forall (byte_list: (@list Z)) (i: Z) (byteIdx: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (1 <= i)) (PreH4 : (i < 8)) (PreH5 : (byteIdx = (Znth i (sublist (24) (32) (byte_list)) 0))) ,
  (0 <= byteIdx)
.

Definition montg_times_base_point_which_implies_wit_11 := 
(
forall (K_non_alias: Z) ,
  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)))) )
|--
  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (16))) (SM2_G_POINT)) )
) \/
(
forall (K_non_alias: Z) ,
  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (0) (8))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (1) (8))) (SM2_G_POINT)))) )
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
  &&  “ (jpoint_represents x y z (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (16))) (SM2_G_POINT)) ) ”
  &&  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Definition montg_times_base_point_which_implies_wit_12 := 
(
forall (K_non_alias: Z) ,
  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (16))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)))) )
|--
  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT)) )
) \/
(
forall (K_non_alias: Z) ,
  (store_mont_jpoint ( &( "K0" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (16))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (2) (8))) (SM2_G_POINT)))) )
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
  &&  “ (jpoint_represents x y z (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) (24))) (SM2_G_POINT)) ) ”
  &&  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "K0" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "K0" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "K0" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Definition montg_times_base_point_which_implies_wit_13 := 
(
forall (PreH1 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
|--
  (store_sm2_mont_base_point_table )
) \/
(
forall (PreH1 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
|--
  (store_sm2_mont_base_point_table )
).

Definition montg_times_base_point_which_implies_wit_13_split_goal_spatial := 
forall (PreH1 : (sm2_mont_base_table_correct )) ,
  (StructAFPointArray.full ( &( "g_montg_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_MONT_BASE_TABLE_DATA)) )
|--
  (store_sm2_mont_base_point_table )
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include basepoint_bytes_Strategy_Correct.
Include basepoint_table_points_Strategy_Correct.

Axiom proof_of_montg_times_base_point_safety_wit_1 : montg_times_base_point_safety_wit_1.
Axiom proof_of_montg_times_base_point_safety_wit_2 : montg_times_base_point_safety_wit_2.
Axiom proof_of_montg_times_base_point_safety_wit_3 : montg_times_base_point_safety_wit_3.
Axiom proof_of_montg_times_base_point_safety_wit_4 : montg_times_base_point_safety_wit_4.
Axiom proof_of_montg_times_base_point_safety_wit_5 : montg_times_base_point_safety_wit_5.
Axiom proof_of_montg_times_base_point_safety_wit_6 : montg_times_base_point_safety_wit_6.
Axiom proof_of_montg_times_base_point_safety_wit_7 : montg_times_base_point_safety_wit_7.
Axiom proof_of_montg_times_base_point_safety_wit_8 : montg_times_base_point_safety_wit_8.
Axiom proof_of_montg_times_base_point_safety_wit_9 : montg_times_base_point_safety_wit_9.
Axiom proof_of_montg_times_base_point_safety_wit_10 : montg_times_base_point_safety_wit_10.
Axiom proof_of_montg_times_base_point_safety_wit_11 : montg_times_base_point_safety_wit_11.
Axiom proof_of_montg_times_base_point_safety_wit_12 : montg_times_base_point_safety_wit_12.
Axiom proof_of_montg_times_base_point_safety_wit_13 : montg_times_base_point_safety_wit_13.
Axiom proof_of_montg_times_base_point_safety_wit_14 : montg_times_base_point_safety_wit_14.
Axiom proof_of_montg_times_base_point_safety_wit_15 : montg_times_base_point_safety_wit_15.
Axiom proof_of_montg_times_base_point_safety_wit_16 : montg_times_base_point_safety_wit_16.
Axiom proof_of_montg_times_base_point_safety_wit_17 : montg_times_base_point_safety_wit_17.
Axiom proof_of_montg_times_base_point_safety_wit_18 : montg_times_base_point_safety_wit_18.
Axiom proof_of_montg_times_base_point_safety_wit_19 : montg_times_base_point_safety_wit_19.
Axiom proof_of_montg_times_base_point_safety_wit_20 : montg_times_base_point_safety_wit_20.
Axiom proof_of_montg_times_base_point_safety_wit_21 : montg_times_base_point_safety_wit_21.
Axiom proof_of_montg_times_base_point_safety_wit_22 : montg_times_base_point_safety_wit_22.
Axiom proof_of_montg_times_base_point_safety_wit_23 : montg_times_base_point_safety_wit_23.
Axiom proof_of_montg_times_base_point_safety_wit_24 : montg_times_base_point_safety_wit_24.
Axiom proof_of_montg_times_base_point_safety_wit_25 : montg_times_base_point_safety_wit_25.
Axiom proof_of_montg_times_base_point_safety_wit_26 : montg_times_base_point_safety_wit_26.
Axiom proof_of_montg_times_base_point_safety_wit_27 : montg_times_base_point_safety_wit_27.
Axiom proof_of_montg_times_base_point_safety_wit_28 : montg_times_base_point_safety_wit_28.
Axiom proof_of_montg_times_base_point_safety_wit_29 : montg_times_base_point_safety_wit_29.
Axiom proof_of_montg_times_base_point_safety_wit_30 : montg_times_base_point_safety_wit_30.
Axiom proof_of_montg_times_base_point_safety_wit_31 : montg_times_base_point_safety_wit_31.
Axiom proof_of_montg_times_base_point_safety_wit_32 : montg_times_base_point_safety_wit_32.
Axiom proof_of_montg_times_base_point_safety_wit_33 : montg_times_base_point_safety_wit_33.
Axiom proof_of_montg_times_base_point_safety_wit_34 : montg_times_base_point_safety_wit_34.
Axiom proof_of_montg_times_base_point_safety_wit_35 : montg_times_base_point_safety_wit_35.
Axiom proof_of_montg_times_base_point_safety_wit_36 : montg_times_base_point_safety_wit_36.
Axiom proof_of_montg_times_base_point_safety_wit_37 : montg_times_base_point_safety_wit_37.
Axiom proof_of_montg_times_base_point_safety_wit_38 : montg_times_base_point_safety_wit_38.
Axiom proof_of_montg_times_base_point_safety_wit_39 : montg_times_base_point_safety_wit_39.
Axiom proof_of_montg_times_base_point_safety_wit_40 : montg_times_base_point_safety_wit_40.
Axiom proof_of_montg_times_base_point_entail_wit_1 : montg_times_base_point_entail_wit_1.
Axiom proof_of_montg_times_base_point_entail_wit_2 : montg_times_base_point_entail_wit_2.
Axiom proof_of_montg_times_base_point_entail_wit_3 : montg_times_base_point_entail_wit_3.
Axiom proof_of_montg_times_base_point_entail_wit_4 : montg_times_base_point_entail_wit_4.
Axiom proof_of_montg_times_base_point_entail_wit_5 : montg_times_base_point_entail_wit_5.
Axiom proof_of_montg_times_base_point_entail_wit_6 : montg_times_base_point_entail_wit_6.
Axiom proof_of_montg_times_base_point_entail_wit_7 : montg_times_base_point_entail_wit_7.
Axiom proof_of_montg_times_base_point_entail_wit_8 : montg_times_base_point_entail_wit_8.
Axiom proof_of_montg_times_base_point_entail_wit_9 : montg_times_base_point_entail_wit_9.
Axiom proof_of_montg_times_base_point_entail_wit_10 : montg_times_base_point_entail_wit_10.
Axiom proof_of_montg_times_base_point_entail_wit_11 : montg_times_base_point_entail_wit_11.
Axiom proof_of_montg_times_base_point_entail_wit_12 : montg_times_base_point_entail_wit_12.
Axiom proof_of_montg_times_base_point_entail_wit_13 : montg_times_base_point_entail_wit_13.
Axiom proof_of_montg_times_base_point_entail_wit_14 : montg_times_base_point_entail_wit_14.
Axiom proof_of_montg_times_base_point_entail_wit_15 : montg_times_base_point_entail_wit_15.
Axiom proof_of_montg_times_base_point_entail_wit_16 : montg_times_base_point_entail_wit_16.
Axiom proof_of_montg_times_base_point_entail_wit_17 : montg_times_base_point_entail_wit_17.
Axiom proof_of_montg_times_base_point_entail_wit_18 : montg_times_base_point_entail_wit_18.
Axiom proof_of_montg_times_base_point_entail_wit_19 : montg_times_base_point_entail_wit_19.
Axiom proof_of_montg_times_base_point_return_wit_1 : montg_times_base_point_return_wit_1.
Axiom proof_of_montg_times_base_point_partial_solve_wit_1 : montg_times_base_point_partial_solve_wit_1.
Axiom proof_of_montg_times_base_point_partial_solve_wit_2 : montg_times_base_point_partial_solve_wit_2.
Axiom proof_of_montg_times_base_point_partial_solve_wit_3 : montg_times_base_point_partial_solve_wit_3.
Axiom proof_of_montg_times_base_point_partial_solve_wit_4_pure : montg_times_base_point_partial_solve_wit_4_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_4 : montg_times_base_point_partial_solve_wit_4.
Axiom proof_of_montg_times_base_point_partial_solve_wit_5 : montg_times_base_point_partial_solve_wit_5.
Axiom proof_of_montg_times_base_point_partial_solve_wit_6 : montg_times_base_point_partial_solve_wit_6.
Axiom proof_of_montg_times_base_point_partial_solve_wit_7_pure : montg_times_base_point_partial_solve_wit_7_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_7 : montg_times_base_point_partial_solve_wit_7.
Axiom proof_of_montg_times_base_point_partial_solve_wit_8_pure : montg_times_base_point_partial_solve_wit_8_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_8 : montg_times_base_point_partial_solve_wit_8.
Axiom proof_of_montg_times_base_point_partial_solve_wit_9 : montg_times_base_point_partial_solve_wit_9.
Axiom proof_of_montg_times_base_point_partial_solve_wit_10_pure : montg_times_base_point_partial_solve_wit_10_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_10 : montg_times_base_point_partial_solve_wit_10.
Axiom proof_of_montg_times_base_point_partial_solve_wit_11 : montg_times_base_point_partial_solve_wit_11.
Axiom proof_of_montg_times_base_point_partial_solve_wit_12 : montg_times_base_point_partial_solve_wit_12.
Axiom proof_of_montg_times_base_point_partial_solve_wit_13_pure : montg_times_base_point_partial_solve_wit_13_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_13 : montg_times_base_point_partial_solve_wit_13.
Axiom proof_of_montg_times_base_point_partial_solve_wit_14_pure : montg_times_base_point_partial_solve_wit_14_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_14 : montg_times_base_point_partial_solve_wit_14.
Axiom proof_of_montg_times_base_point_partial_solve_wit_15 : montg_times_base_point_partial_solve_wit_15.
Axiom proof_of_montg_times_base_point_partial_solve_wit_16_pure : montg_times_base_point_partial_solve_wit_16_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_16 : montg_times_base_point_partial_solve_wit_16.
Axiom proof_of_montg_times_base_point_partial_solve_wit_17 : montg_times_base_point_partial_solve_wit_17.
Axiom proof_of_montg_times_base_point_partial_solve_wit_18 : montg_times_base_point_partial_solve_wit_18.
Axiom proof_of_montg_times_base_point_partial_solve_wit_19_pure : montg_times_base_point_partial_solve_wit_19_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_19 : montg_times_base_point_partial_solve_wit_19.
Axiom proof_of_montg_times_base_point_partial_solve_wit_20_pure : montg_times_base_point_partial_solve_wit_20_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_20 : montg_times_base_point_partial_solve_wit_20.
Axiom proof_of_montg_times_base_point_partial_solve_wit_21 : montg_times_base_point_partial_solve_wit_21.
Axiom proof_of_montg_times_base_point_partial_solve_wit_22_pure : montg_times_base_point_partial_solve_wit_22_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_22 : montg_times_base_point_partial_solve_wit_22.
Axiom proof_of_montg_times_base_point_partial_solve_wit_23 : montg_times_base_point_partial_solve_wit_23.
Axiom proof_of_montg_times_base_point_partial_solve_wit_24 : montg_times_base_point_partial_solve_wit_24.
Axiom proof_of_montg_times_base_point_partial_solve_wit_25_pure : montg_times_base_point_partial_solve_wit_25_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_25 : montg_times_base_point_partial_solve_wit_25.
Axiom proof_of_montg_times_base_point_partial_solve_wit_26_pure : montg_times_base_point_partial_solve_wit_26_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_26 : montg_times_base_point_partial_solve_wit_26.
Axiom proof_of_montg_times_base_point_partial_solve_wit_27_pure : montg_times_base_point_partial_solve_wit_27_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_27 : montg_times_base_point_partial_solve_wit_27.
Axiom proof_of_montg_times_base_point_partial_solve_wit_28 : montg_times_base_point_partial_solve_wit_28.
Axiom proof_of_montg_times_base_point_partial_solve_wit_29_pure : montg_times_base_point_partial_solve_wit_29_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_29 : montg_times_base_point_partial_solve_wit_29.
Axiom proof_of_montg_times_base_point_partial_solve_wit_30 : montg_times_base_point_partial_solve_wit_30.
Axiom proof_of_montg_times_base_point_partial_solve_wit_31 : montg_times_base_point_partial_solve_wit_31.
Axiom proof_of_montg_times_base_point_partial_solve_wit_32_pure : montg_times_base_point_partial_solve_wit_32_pure.
Axiom proof_of_montg_times_base_point_partial_solve_wit_32 : montg_times_base_point_partial_solve_wit_32.
Axiom proof_of_montg_times_base_point_which_implies_wit_1 : montg_times_base_point_which_implies_wit_1.
Axiom proof_of_montg_times_base_point_which_implies_wit_2 : montg_times_base_point_which_implies_wit_2.
Axiom proof_of_montg_times_base_point_which_implies_wit_3 : montg_times_base_point_which_implies_wit_3.
Axiom proof_of_montg_times_base_point_which_implies_wit_4 : montg_times_base_point_which_implies_wit_4.
Axiom proof_of_montg_times_base_point_which_implies_wit_5 : montg_times_base_point_which_implies_wit_5.
Axiom proof_of_montg_times_base_point_which_implies_wit_6 : montg_times_base_point_which_implies_wit_6.
Axiom proof_of_montg_times_base_point_which_implies_wit_7 : montg_times_base_point_which_implies_wit_7.
Axiom proof_of_montg_times_base_point_which_implies_wit_8 : montg_times_base_point_which_implies_wit_8.
Axiom proof_of_montg_times_base_point_which_implies_wit_9 : montg_times_base_point_which_implies_wit_9.
Axiom proof_of_montg_times_base_point_which_implies_wit_10 : montg_times_base_point_which_implies_wit_10.
Axiom proof_of_montg_times_base_point_which_implies_wit_11 : montg_times_base_point_which_implies_wit_11.
Axiom proof_of_montg_times_base_point_which_implies_wit_12 : montg_times_base_point_which_implies_wit_12.
Axiom proof_of_montg_times_base_point_which_implies_wit_13 : montg_times_base_point_which_implies_wit_13.

End VC_Correct.
