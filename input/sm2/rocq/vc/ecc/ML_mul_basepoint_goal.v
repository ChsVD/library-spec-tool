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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import ML_mul_basepoint_def.
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

(*----- Function ML_mul_basepoint -----*)

Definition ML_mul_basepoint_safety_wit_1 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ML_mul_basepoint_safety_wit_2 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ML_mul_basepoint_safety_wit_3 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = 0)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (0 < SM2_P_Z)) (PreH5 : (0 <= 0)) (PreH6 : ((u64_list_value (ys)) = 1)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (1 < SM2_P_Z)) (PreH10 : (0 <= 1)) (PreH11 : ((u64_list_value (xs)) = 1)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (1 < SM2_P_Z)) (PreH15 : (0 <= 1)) ,
  ((( &( "pByte" ) )) # Ptr  |->_)
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ML_mul_basepoint_safety_wit_4 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = 0)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (0 < SM2_P_Z)) (PreH5 : (0 <= 0)) (PreH6 : ((u64_list_value (ys)) = 1)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (1 < SM2_P_Z)) (PreH10 : (0 <= 1)) (PreH11 : ((u64_list_value (xs)) = 1)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (1 < SM2_P_Z)) (PreH15 : (0 <= 1)) ,
  ((( &( "pTable" ) )) # Ptr  |->_)
  **  ((( &( "byte" ) )) # UChar  |->_)
  **  ((( &( "pByte" ) )) # Ptr  |-> 0)
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ML_mul_basepoint_safety_wit_5 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (byte_list: (@list Z)) (PreH1 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) (PreH2 : (0 <= K_non_alias)) (PreH3 : (K_non_alias < SM2_N_Z)) (PreH4 : ((Zlength (byte_list)) = 32)) (PreH5 : (u8_list_bounded byte_list )) (PreH6 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH7 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH8 : ((u64_list_value (zs)) = 0)) (PreH9 : (u64_list_bounded zs )) (PreH10 : ((Zlength (zs)) = 4)) (PreH11 : (0 < SM2_P_Z)) (PreH12 : (0 <= 0)) (PreH13 : ((u64_list_value (ys)) = 1)) (PreH14 : (u64_list_bounded ys )) (PreH15 : ((Zlength (ys)) = 4)) (PreH16 : (1 < SM2_P_Z)) (PreH17 : (0 <= 1)) (PreH18 : ((u64_list_value (xs)) = 1)) (PreH19 : (u64_list_bounded xs )) (PreH20 : ((Zlength (xs)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) ,
  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  ((( &( "pTable" ) )) # Ptr  |-> 0)
  **  ((( &( "byte" ) )) # UChar  |->_)
  **  ((( &( "pByte" ) )) # Ptr  |-> 0)
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ML_mul_basepoint_safety_wit_6 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (TP: ec_point) (i: Z) (J: Z) (PA: Z) (PB: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 4)) (PreH3 : (0 <= K_non_alias)) (PreH4 : (K_non_alias < SM2_N_Z)) (PreH5 : ((Zlength (byte_list)) = 32)) (PreH6 : (u8_list_bounded byte_list )) (PreH7 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH8 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH9 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pByte" ) )) # Ptr  |-> PB)
  **  ((( &( "pTable" ) )) # Ptr  |-> PA)
  **  ((( &( "j" ) )) # Int  |-> J)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition ML_mul_basepoint_safety_wit_7 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (TP: ec_point) (PA: Z) (J: Z) (PreH1 : (i < 4)) (PreH2 : (0 <= i)) (PreH3 : (i <= 4)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH10 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  ((( &( "pTable" ) )) # Ptr  |-> PA)
  **  ((( &( "j" ) )) # Int  |-> J)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ML_mul_basepoint_safety_wit_8 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PA: Z) (J: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  ((( &( "pTable" ) )) # Ptr  |-> PA)
  **  ((( &( "j" ) )) # Int  |-> J)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ML_mul_basepoint_safety_wit_9 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PA: Z) (J: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  ((( &( "pTable" ) )) # Ptr  |-> PA)
  **  ((( &( "j" ) )) # Int  |-> J)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ML_mul_basepoint_safety_wit_10 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PA: Z) (J: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 (replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  ((( &( "pTable" ) )) # Ptr  |-> PA)
  **  ((( &( "j" ) )) # Int  |-> J)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ML_mul_basepoint_safety_wit_11 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PA: Z) (J: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 (replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  ((( &( "pTable" ) )) # Ptr  |-> PA)
  **  ((( &( "j" ) )) # Int  |-> J)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ML_mul_basepoint_safety_wit_12 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PA: Z) (J: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 (replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 (replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  ((( &( "pTable" ) )) # Ptr  |-> PA)
  **  ((( &( "j" ) )) # Int  |-> J)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ML_mul_basepoint_safety_wit_13 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PATable: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 4)) (PreH3 : (0 <= j)) (PreH4 : (j <= 8)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pTable" ) )) # Ptr  |-> PATable)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition ML_mul_basepoint_safety_wit_14 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> (sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT))))) (PreH3 : ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)))) <> ECInfinity))) (PreH4 : (0 <= (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) (PreH5 : ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) < 256)) (PreH6 : (j < 8)) (PreH7 : (0 <= i)) (PreH8 : (i < 4)) (PreH9 : (0 <= j)) (PreH10 : (j <= 8)) (PreH11 : (0 <= K_non_alias)) (PreH12 : (K_non_alias < SM2_N_Z)) (PreH13 : ((Zlength (byte_list)) = 32)) (PreH14 : (u8_list_bounded byte_list )) (PreH15 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH16 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH17 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byte" ) )) # UChar  |-> (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))
  **  ((( &( "pTable" ) )) # Ptr  |-> (((( &( "g_AFTable_for_base_point_mul" ) ) + (i * ((sizeof( "AFPoint" ) * 256) * 8))) + (j * (sizeof( "AFPoint" ) * 256))) + ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_inv2p )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition ML_mul_basepoint_safety_wit_15 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PATable: Z) (PreH1 : (( &( "Tr" ) ) = ( &( "Tr" ) ))) (PreH2 : (j >= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= j)) (PreH6 : (j <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)))) )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pTable" ) )) # Ptr  |-> PATable)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition ML_mul_basepoint_entail_wit_1 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) ,
  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  (store_jpoint_fields ( &( "JPoint_ZERO" ) ) 1 1 0 )
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_entail_wit_2 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) ,
  (store_jpoint_fields ( &( "JPoint_ZERO" ) ) 1 1 0 )
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
|--
  EX (zs: (@list Z))  (ys: (@list Z))  (xs: (@list Z)) ,
  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ”
  &&  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_entail_wit_3 := 
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (byte_list: (@list Z)) (PreH1 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) (PreH2 : (0 <= K_non_alias)) (PreH3 : (K_non_alias < SM2_N_Z)) (PreH4 : ((Zlength (byte_list)) = 32)) (PreH5 : (u8_list_bounded byte_list )) (PreH6 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH7 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH8 : ((u64_list_value (zs)) = 0)) (PreH9 : (u64_list_bounded zs )) (PreH10 : ((Zlength (zs)) = 4)) (PreH11 : (0 < SM2_P_Z)) (PreH12 : (0 <= 0)) (PreH13 : ((u64_list_value (ys)) = 1)) (PreH14 : (u64_list_bounded ys )) (PreH15 : ((Zlength (ys)) = 4)) (PreH16 : (1 < SM2_P_Z)) (PreH17 : (0 <= 1)) (PreH18 : ((u64_list_value (xs)) = 1)) (PreH19 : (u64_list_bounded xs )) (PreH20 : ((Zlength (xs)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) ,
  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
|--
  EX (TP: ec_point) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 4) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * 0 )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
) \/
(
forall (k_pre: Z) (K_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (byte_list: (@list Z)) (PreH1 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) (PreH2 : (0 <= K_non_alias)) (PreH3 : (K_non_alias < SM2_N_Z)) (PreH4 : ((Zlength (byte_list)) = 32)) (PreH5 : (u8_list_bounded byte_list )) (PreH6 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH7 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH8 : ((u64_list_value (zs)) = 0)) (PreH9 : (u64_list_bounded zs )) (PreH10 : ((Zlength (zs)) = 4)) (PreH11 : (0 < SM2_P_Z)) (PreH12 : (0 <= 0)) (PreH13 : ((u64_list_value (ys)) = 1)) (PreH14 : (u64_list_bounded ys )) (PreH15 : ((Zlength (ys)) = 4)) (PreH16 : (1 < SM2_P_Z)) (PreH17 : (0 <= 1)) (PreH18 : ((u64_list_value (xs)) = 1)) (PreH19 : (u64_list_bounded xs )) (PreH20 : ((Zlength (xs)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (TP: ec_point) ,
  “ ((u64_list_value (xs)) < SM2_P_Z) ” 
  &&  “ (0 <= (u64_list_value (xs))) ” 
  &&  “ ((u64_list_value (ys)) < SM2_P_Z) ” 
  &&  “ (0 <= (u64_list_value (ys))) ” 
  &&  “ ((u64_list_value (zs)) < SM2_P_Z) ” 
  &&  “ (0 <= (u64_list_value (zs))) ” 
  &&  “ (jpoint_canonical_infinity_encoding (u64_list_value (xs)) (u64_list_value (ys)) (u64_list_value (zs)) TP ) ” 
  &&  “ (jpoint_represents (u64_list_value (xs)) (u64_list_value (ys)) (u64_list_value (zs)) TP ) ” 
  &&  “ ((u64_list_value (xs)) < SM2_P_Z) ” 
  &&  “ (0 <= (u64_list_value (xs))) ” 
  &&  “ ((u64_list_value (ys)) < SM2_P_Z) ” 
  &&  “ (0 <= (u64_list_value (ys))) ” 
  &&  “ ((u64_list_value (zs)) < SM2_P_Z) ” 
  &&  “ (0 <= (u64_list_value (zs))) ” 
  &&  “ (jpoint_canonical_infinity_encoding (u64_list_value (xs)) (u64_list_value (ys)) (u64_list_value (zs)) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * 0 )))) (SM2_G_POINT)) ) ” 
  &&  “ (jpoint_represents (u64_list_value (xs)) (u64_list_value (ys)) (u64_list_value (zs)) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * 0 )))) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 4) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
).

Definition ML_mul_basepoint_entail_wit_4 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (PA: Z) (J: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 (replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 (replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  ((( &( "pTable" ) )) # Ptr  |-> PA)
  **  ((( &( "j" ) )) # Int  |-> J)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (retval = ( &( "T" ) )) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 4) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 (replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 (replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  ((( &( "pTable" ) )) # Ptr  |-> PA)
  **  ((( &( "j" ) )) # Int  |-> J)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
.

Definition ML_mul_basepoint_entail_wit_5 := 
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 (replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 (replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (0))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
) \/
(
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  TT && emp 
|--
  “ (jpoint_represents (u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) (u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) (u64_list_value ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (0))) (SM2_G_POINT)) ) ” 
  &&  “ (jpoint_canonical_infinity_encoding (u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) (u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) (u64_list_value ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (0))) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= (u64_list_value ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z)))))))))))) ” 
  &&  “ ((u64_list_value ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) < SM2_P_Z) ” 
  &&  “ (0 <= (u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z)))))))))))))) ” 
  &&  “ ((u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) < SM2_P_Z) ” 
  &&  “ (0 <= (u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z)))))))))))))) ” 
  &&  “ ((u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) < SM2_P_Z) ”
  &&  emp
).

Definition ML_mul_basepoint_entail_wit_5_split_goal_1 := 
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (jpoint_represents (u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) (u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) (u64_list_value ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (0))) (SM2_G_POINT)) )
.

Definition ML_mul_basepoint_entail_wit_5_split_goal_2 := 
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (jpoint_canonical_infinity_encoding (u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) (u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) (u64_list_value ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (0))) (SM2_G_POINT)) )
.

Definition ML_mul_basepoint_entail_wit_5_split_goal_3 := 
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (0 <= (u64_list_value ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))
.

Definition ML_mul_basepoint_entail_wit_5_split_goal_4 := 
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  ((u64_list_value ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) < SM2_P_Z)
.

Definition ML_mul_basepoint_entail_wit_5_split_goal_5 := 
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (0 <= (u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))))
.

Definition ML_mul_basepoint_entail_wit_5_split_goal_6 := 
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  ((u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) < SM2_P_Z)
.

Definition ML_mul_basepoint_entail_wit_5_split_goal_7 := 
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (0 <= (u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))))
.

Definition ML_mul_basepoint_entail_wit_5_split_goal_8 := 
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  ((u64_list_value ((replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) < SM2_P_Z)
.

Definition ML_mul_basepoint_entail_wit_6 := 
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> (sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT))))) (PreH3 : ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)))) <> ECInfinity))) (PreH4 : (0 <= (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) (PreH5 : ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) < 256)) (PreH6 : (j < 8)) (PreH7 : (0 <= i)) (PreH8 : (i < 4)) (PreH9 : (0 <= j)) (PreH10 : (j <= 8)) (PreH11 : (0 <= K_non_alias)) (PreH12 : (K_non_alias < SM2_N_Z)) (PreH13 : ((Zlength (byte_list)) = 32)) (PreH14 : (u8_list_bounded byte_list )) (PreH15 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH16 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH17 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  ((( &( "byte" ) )) # UChar  |-> (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_inv2p )
|--
  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) ((j + 1 )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
) \/
(
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PreH1 : ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> (sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT))))) (PreH2 : ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)))) <> ECInfinity))) (PreH3 : (0 <= (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) (PreH4 : ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) < 256)) (PreH5 : (j < 8)) (PreH6 : (0 <= i)) (PreH7 : (i < 4)) (PreH8 : (0 <= j)) (PreH9 : (j <= 8)) (PreH10 : (0 <= K_non_alias)) (PreH11 : (K_non_alias < SM2_N_Z)) (PreH12 : ((Zlength (byte_list)) = 32)) (PreH13 : (u8_list_bounded byte_list )) (PreH14 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH15 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH16 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (jpoint_canonical_infinity_encoding (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) (u256_of_limbs (x0) (x1) (x2) (x3)) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) ((j + 1 )))) (SM2_G_POINT)) ) ” 
  &&  “ (jpoint_represents (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) (u256_of_limbs (x0) (x1) (x2) (x3)) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) ((j + 1 )))) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (((&(( &( "T" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "T" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "T" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "T" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "T" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "T" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "T" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "T" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "T" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "T" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "T" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "T" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition ML_mul_basepoint_entail_wit_7 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PATable: Z) (PreH1 : (j >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i < 4)) (PreH4 : (0 <= j)) (PreH5 : (j <= 8)) (PreH6 : (0 <= K_non_alias)) (PreH7 : (K_non_alias < SM2_N_Z)) (PreH8 : ((Zlength (byte_list)) = 32)) (PreH9 : (u8_list_bounded byte_list )) (PreH10 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH11 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH12 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pTable" ) )) # Ptr  |-> PATable)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (j >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pTable" ) )) # Ptr  |-> PATable)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
.

Definition ML_mul_basepoint_entail_wit_8 := 
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PreH1 : (( &( "Tr" ) ) = ( &( "Tr" ) ))) (PreH2 : (j >= 8)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= j)) (PreH6 : (j <= 8)) (PreH7 : (0 <= K_non_alias)) (PreH8 : (K_non_alias < SM2_N_Z)) (PreH9 : ((Zlength (byte_list)) = 32)) (PreH10 : (u8_list_bounded byte_list )) (PreH11 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH12 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH13 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)))) )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
|--
  EX (TP: ec_point) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 4) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * (i + 1 ) )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
) \/
(
forall (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i < 4)) (PreH4 : (0 <= j)) (PreH5 : (j <= 8)) (PreH6 : (0 <= K_non_alias)) (PreH7 : (K_non_alias < SM2_N_Z)) (PreH8 : ((Zlength (byte_list)) = 32)) (PreH9 : (u8_list_bounded byte_list )) (PreH10 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH11 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH12 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_add ((sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (TP: ec_point) ,
  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ ((u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (jpoint_canonical_infinity_encoding (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) TP ) ” 
  &&  “ (jpoint_represents (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) TP ) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (jpoint_canonical_infinity_encoding (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) (u256_of_limbs (x0) (x1) (x2) (x3)) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * (i + 1 ) )))) (SM2_G_POINT)) ) ” 
  &&  “ (jpoint_represents (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) (u256_of_limbs (x0) (x1) (x2) (x3)) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * (i + 1 ) )))) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 4) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (((&(( &( "T" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "T" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "T" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "T" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "T" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "T" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "T" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "T" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "T" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "T" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "T" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "T" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "Tr" ) )->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "Tr" ) )->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "Tr" ) )->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "Tr" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "Tr" ) )->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "Tr" ) )->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "Tr" ) )->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "Tr" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "Tr" ) )->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "Tr" ) )->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "Tr" ) )->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "Tr" ) )->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition ML_mul_basepoint_entail_wit_9 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (TP: ec_point) (i: Z) (J: Z) (PA: Z) (PB: Z) (PreH1 : (i >= 4)) (PreH2 : (0 <= i)) (PreH3 : (i <= 4)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH10 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pByte" ) )) # Ptr  |-> PB)
  **  ((( &( "pTable" ) )) # Ptr  |-> PA)
  **  ((( &( "j" ) )) # Int  |-> J)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (i >= 4) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 4) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (store_fn k_pre K_non_alias )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pByte" ) )) # Ptr  |-> PB)
  **  ((( &( "pTable" ) )) # Ptr  |-> PA)
  **  ((( &( "j" ) )) # Int  |-> J)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
.

Definition ML_mul_basepoint_return_wit_1 := 
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = result_pre)) (PreH2 : (i >= 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (store_jpoint_with_canonical_infinity result_pre (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_sm2_base_point_table )
  **  (store_fn k_pre K_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  (store_fn k_pre K_non_alias )
  **  (store_jpoint_with_canonical_infinity result_pre (sm2_point_mul (K_non_alias) (SM2_G_POINT)) )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
) \/
(
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = result_pre)) (PreH2 : (i >= 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (store_jpoint_with_canonical_infinity result_pre (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (jpoint_canonical_infinity_encoding (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) (u256_of_limbs (x0) (x1) (x2) (x3)) (sm2_point_mul (K_non_alias) (SM2_G_POINT)) ) ” 
  &&  “ (jpoint_represents (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) (u256_of_limbs (x0) (x1) (x2) (x3)) (sm2_point_mul (K_non_alias) (SM2_G_POINT)) ) ”
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
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition ML_mul_basepoint_partial_solve_wit_1 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = 0)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (0 < SM2_P_Z)) (PreH5 : (0 <= 0)) (PreH6 : ((u64_list_value (ys)) = 1)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (1 < SM2_P_Z)) (PreH10 : (0 <= 1)) (PreH11 : ((u64_list_value (xs)) = 1)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (1 < SM2_P_Z)) (PreH15 : (0 <= 1)) ,
  (UndefStructPredJPoint ( &( "Tr" ) ) )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
|--
  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ”
  &&  (UInt64Array.undef_full &(( &( "Tr" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.undef_full &(( &( "Tr" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.undef_full &(( &( "Tr" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_partial_solve_wit_2 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = 0)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (0 < SM2_P_Z)) (PreH5 : (0 <= 0)) (PreH6 : ((u64_list_value (ys)) = 1)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (1 < SM2_P_Z)) (PreH10 : (0 <= 1)) (PreH11 : ((u64_list_value (xs)) = 1)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (1 < SM2_P_Z)) (PreH15 : (0 <= 1)) ,
  (UndefStructPredJPoint ( &( "T" ) ) )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
|--
  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ”
  &&  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_partial_solve_wit_3 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = 0)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (0 < SM2_P_Z)) (PreH5 : (0 <= 0)) (PreH6 : ((u64_list_value (ys)) = 1)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (1 < SM2_P_Z)) (PreH10 : (0 <= 1)) (PreH11 : ((u64_list_value (xs)) = 1)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (1 < SM2_P_Z)) (PreH15 : (0 <= 1)) ,
  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
|--
  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ”
  &&  (store_fn k_pre K_non_alias )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_partial_solve_wit_4 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (byte_list: (@list Z)) (PreH1 : (0 <= K_non_alias)) (PreH2 : (K_non_alias < SM2_N_Z)) (PreH3 : ((Zlength (byte_list)) = 32)) (PreH4 : (u8_list_bounded byte_list )) (PreH5 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH6 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH7 : ((u64_list_value (zs)) = 0)) (PreH8 : (u64_list_bounded zs )) (PreH9 : ((Zlength (zs)) = 4)) (PreH10 : (0 < SM2_P_Z)) (PreH11 : (0 <= 0)) (PreH12 : ((u64_list_value (ys)) = 1)) (PreH13 : (u64_list_bounded ys )) (PreH14 : ((Zlength (ys)) = 4)) (PreH15 : (1 < SM2_P_Z)) (PreH16 : (0 <= 1)) (PreH17 : ((u64_list_value (xs)) = 1)) (PreH18 : (u64_list_bounded xs )) (PreH19 : ((Zlength (xs)) = 4)) (PreH20 : (1 < SM2_P_Z)) (PreH21 : (0 <= 1)) ,
  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
|--
  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ”
  &&  (store_sm2_base_point_table )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "Tr" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_partial_solve_wit_5_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (TP: ec_point) (PA: Z) (J: Z) (PreH1 : (i < 4)) (PreH2 : (0 <= i)) (PreH3 : (i <= 4)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH10 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  ((( &( "pTable" ) )) # Ptr  |-> PA)
  **  ((( &( "j" ) )) # Int  |-> J)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (0 = 0) ” 
  &&  “ (sizeof( "JPoint" ) = sizeof( "JPoint" )) ”
.

Definition ML_mul_basepoint_partial_solve_wit_5_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (TP: ec_point) (PreH1 : (i < 4)) (PreH2 : (0 <= i)) (PreH3 : (i <= 4)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH10 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (0 = 0) ” 
  &&  “ (sizeof( "JPoint" ) = sizeof( "JPoint" )) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 4) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_partial_solve_wit_5 := ML_mul_basepoint_partial_solve_wit_5_pure -> ML_mul_basepoint_partial_solve_wit_5_aux.

Definition ML_mul_basepoint_partial_solve_wit_6 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (store_jpoint_fields ( &( "T" ) ) 0 0 0 )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (retval = ( &( "T" ) )) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 4) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (store_jpoint_fields ( &( "T" ) ) 0 0 0 )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_partial_solve_wit_7 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (retval = ( &( "T" ) )) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 4) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (((&(( &( "T" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.missing_i &(( &( "T" ) )->ₛ "x" .ₛ "v") 0 0 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_partial_solve_wit_8 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = ( &( "T" ) ))) (PreH2 : (i < 4)) (PreH3 : (0 <= i)) (PreH4 : (i <= 4)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (K_non_alias < SM2_N_Z)) (PreH7 : ((Zlength (byte_list)) = 32)) (PreH8 : (u8_list_bounded byte_list )) (PreH9 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH10 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH11 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 (replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (retval = ( &( "T" ) )) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 4) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (((&(( &( "T" ) )->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.missing_i &(( &( "T" ) )->ₛ "y" .ₛ "v") 0 0 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 (replace_Znth (0) (1) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_partial_solve_wit_9 := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 8)) (PreH2 : (0 <= i)) (PreH3 : (i < 4)) (PreH4 : (0 <= j)) (PreH5 : (j <= 8)) (PreH6 : (0 <= K_non_alias)) (PreH7 : (K_non_alias < SM2_N_Z)) (PreH8 : ((Zlength (byte_list)) = 32)) (PreH9 : (u8_list_bounded byte_list )) (PreH10 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH11 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH12 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (j < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  ((((&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) + (j * sizeof(UCHAR)))) # UChar  |-> (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))
  **  (UCharArray.missing_i (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) j 0 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_partial_solve_wit_10_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PATable: Z) (PreH1 : (j < 8)) (PreH2 : (0 <= i)) (PreH3 : (i < 4)) (PreH4 : (0 <= j)) (PreH5 : (j <= 8)) (PreH6 : (0 <= K_non_alias)) (PreH7 : (K_non_alias < SM2_N_Z)) (PreH8 : ((Zlength (byte_list)) = 32)) (PreH9 : (u8_list_bounded byte_list )) (PreH10 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH11 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH12 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pTable" ) )) # Ptr  |-> PATable)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |-> (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 8) ” 
  &&  “ ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) = (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) ”
.

Definition ML_mul_basepoint_partial_solve_wit_10_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 8)) (PreH2 : (0 <= i)) (PreH3 : (i < 4)) (PreH4 : (0 <= j)) (PreH5 : (j <= 8)) (PreH6 : (0 <= K_non_alias)) (PreH7 : (K_non_alias < SM2_N_Z)) (PreH8 : ((Zlength (byte_list)) = 32)) (PreH9 : (u8_list_bounded byte_list )) (PreH10 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH11 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH12 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 8) ” 
  &&  “ ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) = (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) ” 
  &&  “ (j < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_partial_solve_wit_10 := ML_mul_basepoint_partial_solve_wit_10_pure -> ML_mul_basepoint_partial_solve_wit_10_aux.

Definition ML_mul_basepoint_partial_solve_wit_11_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PreH1 : (0 <= (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) (PreH2 : ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) < 256)) (PreH3 : (j < 8)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= j)) (PreH7 : (j <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "byte" ) )) # UChar  |-> (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  ((( &( "pTable" ) )) # Ptr  |-> (((( &( "g_AFTable_for_base_point_mul" ) ) + (i * ((sizeof( "AFPoint" ) * 256) * 8))) + (j * (sizeof( "AFPoint" ) * 256))) + ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 8) ” 
  &&  “ ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) = (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) ”
.

Definition ML_mul_basepoint_partial_solve_wit_11_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PreH1 : (0 <= (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) (PreH2 : ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) < 256)) (PreH3 : (j < 8)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= j)) (PreH7 : (j <= 8)) (PreH8 : (0 <= K_non_alias)) (PreH9 : (K_non_alias < SM2_N_Z)) (PreH10 : ((Zlength (byte_list)) = 32)) (PreH11 : (u8_list_bounded byte_list )) (PreH12 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH13 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH14 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 8) ” 
  &&  “ ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) = (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) ” 
  &&  “ (record_afpoint_well_formed (sm2_base_table_record_at (i) (j) ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) ) ” 
  &&  “ (0 <= (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) ” 
  &&  “ ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) < 256) ” 
  &&  “ (j < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (store_afpoint (((( &( "g_AFTable_for_base_point_mul" ) ) + (i * ((sizeof( "AFPoint" ) * 256) * 8))) + (j * (sizeof( "AFPoint" ) * 256))) + ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) * sizeof( "AFPoint" ))) (sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) )
  **  (StructAFPointArray.missing_i ( &( "g_AFTable_for_base_point_mul" ) ) ((((i * 8 ) * 256 ) + (j * 256 ) ) + (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) ) 0 SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_partial_solve_wit_11 := ML_mul_basepoint_partial_solve_wit_11_pure -> ML_mul_basepoint_partial_solve_wit_11_aux.

Definition ML_mul_basepoint_partial_solve_wit_12_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PreH1 : ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> (sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT))))) (PreH2 : ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)))) <> ECInfinity))) (PreH3 : (0 <= (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) (PreH4 : ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) < 256)) (PreH5 : (j < 8)) (PreH6 : (0 <= i)) (PreH7 : (i < 4)) (PreH8 : (0 <= j)) (PreH9 : (j <= 8)) (PreH10 : (0 <= K_non_alias)) (PreH11 : (K_non_alias < SM2_N_Z)) (PreH12 : ((Zlength (byte_list)) = 32)) (PreH13 : (u8_list_bounded byte_list )) (PreH14 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH15 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH16 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "byte" ) )) # UChar  |-> (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  ((( &( "pTable" ) )) # Ptr  |-> (((( &( "g_AFTable_for_base_point_mul" ) ) + (i * ((sizeof( "AFPoint" ) * 256) * 8))) + (j * (sizeof( "AFPoint" ) * 256))) + ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) * sizeof( "AFPoint" ))))
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> (sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)))) ” 
  &&  “ ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)))) <> ECInfinity)) ”
.

Definition ML_mul_basepoint_partial_solve_wit_12_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PreH1 : ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> (sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT))))) (PreH2 : ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)))) <> ECInfinity))) (PreH3 : (0 <= (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) (PreH4 : ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) < 256)) (PreH5 : (j < 8)) (PreH6 : (0 <= i)) (PreH7 : (i < 4)) (PreH8 : (0 <= j)) (PreH9 : (j <= 8)) (PreH10 : (0 <= K_non_alias)) (PreH11 : (K_non_alias < SM2_N_Z)) (PreH12 : ((Zlength (byte_list)) = 32)) (PreH13 : (u8_list_bounded byte_list )) (PreH14 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH15 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH16 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> (sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)))) ” 
  &&  “ ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)))) <> ECInfinity)) ” 
  &&  “ (record_afpoint_well_formed (sm2_base_table_record_at (i) (j) ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) ) ” 
  &&  “ ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> (sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)))) ” 
  &&  “ ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)))) <> ECInfinity)) ” 
  &&  “ (0 <= (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) ” 
  &&  “ ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) < 256) ” 
  &&  “ (j < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (store_afpoint (((( &( "g_AFTable_for_base_point_mul" ) ) + (i * ((sizeof( "AFPoint" ) * 256) * 8))) + (j * (sizeof( "AFPoint" ) * 256))) + ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) * sizeof( "AFPoint" ))) (sm2_point_mul ((sm2_table_term ((Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0)) (i) (j))) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (StructAFPointArray.missing_i ( &( "g_AFTable_for_base_point_mul" ) ) ((((i * 8 ) * 256 ) + (j * 256 ) ) + (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0) ) 0 SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))) 8 (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") (8 * i ) (sublist (0) ((8 * i )) (byte_list)) )
  **  (UCharArray.full (&((k_pre)  # "u32" ->ₛ "v") + ((i + 1 ) * sizeof(UINT64))) (32 - ((8 * i ) + 8 ) ) (sublist (((8 * i ) + 8 )) (32) (byte_list)) )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_partial_solve_wit_12 := ML_mul_basepoint_partial_solve_wit_12_pure -> ML_mul_basepoint_partial_solve_wit_12_aux.

Definition ML_mul_basepoint_partial_solve_wit_13_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PATable: Z) (PreH1 : (j >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i < 4)) (PreH4 : (0 <= j)) (PreH5 : (j <= 8)) (PreH6 : (0 <= K_non_alias)) (PreH7 : (K_non_alias < SM2_N_Z)) (PreH8 : ((Zlength (byte_list)) = 32)) (PreH9 : (u8_list_bounded byte_list )) (PreH10 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH11 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH12 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pTable" ) )) # Ptr  |-> PATable)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pByte" ) )) # Ptr  |-> (&((k_pre)  # "u32" ->ₛ "v") + (i * sizeof(UINT64))))
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (( &( "Tr" ) ) = ( &( "Tr" ) )) ”
.

Definition ML_mul_basepoint_partial_solve_wit_13_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i < 4)) (PreH4 : (0 <= j)) (PreH5 : (j <= 8)) (PreH6 : (0 <= K_non_alias)) (PreH7 : (K_non_alias < SM2_N_Z)) (PreH8 : ((Zlength (byte_list)) = 32)) (PreH9 : (u8_list_bounded byte_list )) (PreH10 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH11 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH12 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (( &( "Tr" ) ) = ( &( "Tr" ) )) ” 
  &&  “ (j >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= 8) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UCharArray.full &((k_pre)  # "u32" ->ₛ "v") 32 byte_list )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
.

Definition ML_mul_basepoint_partial_solve_wit_13 := ML_mul_basepoint_partial_solve_wit_13_pure -> ML_mul_basepoint_partial_solve_wit_13_aux.

Definition ML_mul_basepoint_partial_solve_wit_14_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (TP: ec_point) (i: Z) (J: Z) (PA: Z) (PB: Z) (PreH1 : (i >= 4)) (PreH2 : (0 <= i)) (PreH3 : (i <= 4)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH10 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (store_fn k_pre K_non_alias )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pByte" ) )) # Ptr  |-> PB)
  **  ((( &( "pTable" ) )) # Ptr  |-> PA)
  **  ((( &( "j" ) )) # Int  |-> J)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
.

Definition ML_mul_basepoint_partial_solve_wit_14_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (TP: ec_point) (i: Z) (PreH1 : (i >= 4)) (PreH2 : (0 <= i)) (PreH3 : (i <= 4)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH10 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (store_fn k_pre K_non_alias )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ” 
  &&  “ (i >= 4) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 4) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
  **  (store_fn k_pre K_non_alias )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_partial_solve_wit_14 := ML_mul_basepoint_partial_solve_wit_14_pure -> ML_mul_basepoint_partial_solve_wit_14_aux.

Definition ML_mul_basepoint_partial_solve_wit_15_pure := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (TP: ec_point) (i: Z) (J: Z) (PA: Z) (PB: Z) (PreH1 : (i >= 4)) (PreH2 : (0 <= i)) (PreH3 : (i <= 4)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH10 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (store_sm2_base_point_table )
  **  (store_fn k_pre K_non_alias )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "pByte" ) )) # Ptr  |-> PB)
  **  ((( &( "pTable" ) )) # Ptr  |-> PA)
  **  ((( &( "j" ) )) # Int  |-> J)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  ((( &( "byte" ) )) # UChar  |->_)
|--
  “ (sizeof( "JPoint" ) = sizeof( "JPoint" )) ”
.

Definition ML_mul_basepoint_partial_solve_wit_15_aux := 
forall (result_pre: Z) (k_pre: Z) (K_non_alias: Z) (byte_list: (@list Z)) (TP: ec_point) (i: Z) (PreH1 : (i >= 4)) (PreH2 : (0 <= i)) (PreH3 : (i <= 4)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (K_non_alias < SM2_N_Z)) (PreH6 : ((Zlength (byte_list)) = 32)) (PreH7 : (u8_list_bounded byte_list )) (PreH8 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH9 : (aligned_4 &((k_pre)  # "u32" ->ₛ "v") )) (PreH10 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (store_sm2_base_point_table )
  **  (store_fn k_pre K_non_alias )
  **  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  “ (sizeof( "JPoint" ) = sizeof( "JPoint" )) ” 
  &&  “ (i >= 4) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 4) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (K_non_alias < SM2_N_Z) ” 
  &&  “ ((Zlength (byte_list)) = 32) ” 
  &&  “ (u8_list_bounded byte_list ) ” 
  &&  “ ((u8_list_value (byte_list)) = K_non_alias) ” 
  &&  “ (aligned_4 &((k_pre)  # "u32" ->ₛ "v") ) ” 
  &&  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (store_jpoint_with_canonical_infinity ( &( "Tr" ) ) (sm2_point_mul ((sm2_scalar_prefix (K_non_alias) ((8 * i )))) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_fn k_pre K_non_alias )
  **  (store_jpoint_with_canonical_infinity ( &( "T" ) ) TP )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
.

Definition ML_mul_basepoint_partial_solve_wit_15 := ML_mul_basepoint_partial_solve_wit_15_pure -> ML_mul_basepoint_partial_solve_wit_15_aux.

Definition ML_mul_basepoint_which_implies_wit_1 := 
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

Definition ML_mul_basepoint_which_implies_wit_2 := 
(
  (store_sm2_base_point_table )
|--
  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
) \/
(
  (store_sm2_base_point_table )
|--
  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
  &&  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
).

Definition ML_mul_basepoint_which_implies_wit_2_split_goal_1 := 
  (store_sm2_base_point_table )
|--
  “ (sm2_base_table_correct SM2_BASE_TABLE_DATA ) ”
.

Definition ML_mul_basepoint_which_implies_wit_2_split_goal_spatial := 
  (store_sm2_base_point_table )
|--
  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
.

Definition ML_mul_basepoint_which_implies_wit_3 := 
(
  (store_jpoint_fields ( &( "T" ) ) 0 0 0 )
|--
  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
) \/
(
  (store_jpoint_fields ( &( "T" ) ) 0 0 0 )
|--
  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
).

Definition ML_mul_basepoint_which_implies_wit_3_split_goal_spatial := 
  (store_jpoint_fields ( &( "T" ) ) 0 0 0 )
|--
  (UInt64Array.full &(( &( "T" ) )->ₛ "x" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "y" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "T" ) )->ₛ "z" .ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
.

Definition ML_mul_basepoint_which_implies_wit_4 := 
(
forall (byte_list: (@list Z)) (i: Z) (j: Z) (byte: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= j)) (PreH6 : (j < 8)) (PreH7 : (byte = (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (0 <= byte) ” 
  &&  “ (byte < 256) ”
  &&  emp
) \/
(
forall (byte_list: (@list Z)) (i: Z) (j: Z) (byte: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= j)) (PreH6 : (j < 8)) (PreH7 : (byte = (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) ,
  TT && emp 
|--
  “ (byte < 256) ” 
  &&  “ (0 <= byte) ”
  &&  emp
).

Definition ML_mul_basepoint_which_implies_wit_4_split_goal_1 := 
forall (byte_list: (@list Z)) (i: Z) (j: Z) (byte: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= j)) (PreH6 : (j < 8)) (PreH7 : (byte = (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) ,
  (byte < 256)
.

Definition ML_mul_basepoint_which_implies_wit_4_split_goal_2 := 
forall (byte_list: (@list Z)) (i: Z) (j: Z) (byte: Z) (PreH1 : ((Zlength (byte_list)) = 32)) (PreH2 : (u8_list_bounded byte_list )) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= j)) (PreH6 : (j < 8)) (PreH7 : (byte = (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) ,
  (0 <= byte)
.

Definition ML_mul_basepoint_which_implies_wit_5 := 
(
forall (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (j: Z) (byte: Z) (pTable: Z) (PreH1 : (0 <= K_non_alias)) (PreH2 : (K_non_alias < SM2_N_Z)) (PreH3 : ((Zlength (byte_list)) = 32)) (PreH4 : (u8_list_bounded byte_list )) (PreH5 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH6 : (0 <= i)) (PreH7 : (i < 4)) (PreH8 : (0 <= j)) (PreH9 : (j < 8)) (PreH10 : (byte = (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) ,
  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (store_afpoint pTable (sm2_point_mul ((sm2_table_term (byte) (i) (j))) (SM2_G_POINT)) )
|--
  “ ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term (byte) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> (sm2_point_mul ((sm2_table_term (byte) (i) (j))) (SM2_G_POINT)))) ” 
  &&  “ ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term (byte) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term (byte) (i) (j))) (SM2_G_POINT)))) <> ECInfinity)) ”
  &&  (store_jpoint_with_canonical_infinity ( &( "T" ) ) (sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) )
  **  (store_afpoint pTable (sm2_point_mul ((sm2_table_term (byte) (i) (j))) (SM2_G_POINT)) )
) \/
(
forall (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (j: Z) (byte: Z) (PreH1 : (0 <= K_non_alias)) (PreH2 : (K_non_alias < SM2_N_Z)) (PreH3 : ((Zlength (byte_list)) = 32)) (PreH4 : (u8_list_bounded byte_list )) (PreH5 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH6 : (0 <= i)) (PreH7 : (i < 4)) (PreH8 : (0 <= j)) (PreH9 : (j < 8)) (PreH10 : (byte = (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) ,
  TT && emp 
|--
  “ ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term (byte) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term (byte) (i) (j))) (SM2_G_POINT)))) <> ECInfinity)) ” 
  &&  “ ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term (byte) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> (sm2_point_mul ((sm2_table_term (byte) (i) (j))) (SM2_G_POINT)))) ”
  &&  emp
).

Definition ML_mul_basepoint_which_implies_wit_5_split_goal_1 := 
forall (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (j: Z) (byte: Z) (PreH1 : (0 <= K_non_alias)) (PreH2 : (K_non_alias < SM2_N_Z)) (PreH3 : ((Zlength (byte_list)) = 32)) (PreH4 : (u8_list_bounded byte_list )) (PreH5 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH6 : (0 <= i)) (PreH7 : (i < 4)) (PreH8 : (0 <= j)) (PreH9 : (j < 8)) (PreH10 : (byte = (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) ,
  ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term (byte) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_add ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT))) ((sm2_point_mul ((sm2_table_term (byte) (i) (j))) (SM2_G_POINT)))) <> ECInfinity))
.

Definition ML_mul_basepoint_which_implies_wit_5_split_goal_2 := 
forall (K_non_alias: Z) (byte_list: (@list Z)) (i: Z) (j: Z) (byte: Z) (PreH1 : (0 <= K_non_alias)) (PreH2 : (K_non_alias < SM2_N_Z)) (PreH3 : ((Zlength (byte_list)) = 32)) (PreH4 : (u8_list_bounded byte_list )) (PreH5 : ((u8_list_value (byte_list)) = K_non_alias)) (PreH6 : (0 <= i)) (PreH7 : (i < 4)) (PreH8 : (0 <= j)) (PreH9 : (j < 8)) (PreH10 : (byte = (Znth j (sublist ((8 * i )) (((8 * i ) + 8 )) (byte_list)) 0))) ,
  ((((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> ECInfinity) /\ ((sm2_point_mul ((sm2_table_term (byte) (i) (j))) (SM2_G_POINT)) <> ECInfinity)) -> ((sm2_point_mul ((sm2_scalar_chunk (K_non_alias) (i) (j))) (SM2_G_POINT)) <> (sm2_point_mul ((sm2_table_term (byte) (i) (j))) (SM2_G_POINT))))
.

Definition ML_mul_basepoint_which_implies_wit_6 := 
(
forall (PreH1 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
|--
  (store_sm2_base_point_table )
) \/
(
forall (PreH1 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
|--
  (store_sm2_base_point_table )
).

Definition ML_mul_basepoint_which_implies_wit_6_split_goal_spatial := 
forall (PreH1 : (sm2_base_table_correct SM2_BASE_TABLE_DATA )) ,
  (StructAFPointArray.full ( &( "g_AFTable_for_base_point_mul" ) ) SM2_TABLE_RECORDS (sm2_table_flatten (SM2_BASE_TABLE_DATA)) )
|--
  (store_sm2_base_point_table )
.

Definition add_JPoint_and_AFPoint_derive_canonical_finite_guard_r_eq_point1_by_canonical_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_canonical_finite_guard_r_eq_point1: ec_point) (P1_canonical_finite_guard_r_eq_point1: ec_point) ,
  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_canonical_finite_guard_r_eq_point1 <> ECInfinity) /\ (P2_canonical_finite_guard_r_eq_point1 <> ECInfinity)) -> (P1_canonical_finite_guard_r_eq_point1 <> P2_canonical_finite_guard_r_eq_point1)) ” 
  &&  “ (((P1_canonical_finite_guard_r_eq_point1 <> ECInfinity) /\ (P2_canonical_finite_guard_r_eq_point1 <> ECInfinity)) -> ((sm2_point_add (P1_canonical_finite_guard_r_eq_point1) (P2_canonical_finite_guard_r_eq_point1)) <> ECInfinity)) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_canonical_finite_guard_r_eq_point1 )
  **  (store_afpoint point2_pre P2_canonical_finite_guard_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
EX (P1_canonical_r_eq_point1: ec_point) (P2_canonical_r_eq_point1: ec_point) ,
  ((“ (result_pre = point1_pre) ” 
  &&  “ (((P1_canonical_r_eq_point1 <> ECInfinity) /\ (P2_canonical_r_eq_point1 <> ECInfinity)) -> (P1_canonical_r_eq_point1 <> P2_canonical_r_eq_point1)) ” 
  &&  “ (P1_canonical_r_eq_point1 = ECInfinity) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_canonical_r_eq_point1 )
  **  (store_afpoint point2_pre P2_canonical_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (“ (result_pre = point1_pre) ” 
  &&  “ (((P1_canonical_r_eq_point1 <> ECInfinity) /\ (P2_canonical_r_eq_point1 <> ECInfinity)) -> (P1_canonical_r_eq_point1 <> P2_canonical_r_eq_point1)) ” 
  &&  “ (P2_canonical_r_eq_point1 = ECInfinity) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_canonical_r_eq_point1 )
  **  (store_afpoint point2_pre P2_canonical_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (“ (result_pre = point1_pre) ” 
  &&  “ (((P1_canonical_r_eq_point1 <> ECInfinity) /\ (P2_canonical_r_eq_point1 <> ECInfinity)) -> (P1_canonical_r_eq_point1 <> P2_canonical_r_eq_point1)) ” 
  &&  “ ((sm2_point_add (P1_canonical_r_eq_point1) (P2_canonical_r_eq_point1)) <> ECInfinity) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_canonical_r_eq_point1 )
  **  (store_afpoint point2_pre P2_canonical_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )))
  **
  ((“ (result_pre = point1_pre) ”
  &&  (store_jpoint_with_canonical_infinity result_pre (sm2_point_add (P1_canonical_r_eq_point1) (P2_canonical_r_eq_point1)) )
  **  (store_afpoint point2_pre P2_canonical_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  -*
  (“ (result_pre = point1_pre) ”
  &&  (store_jpoint_with_canonical_infinity result_pre (sm2_point_add (P1_canonical_finite_guard_r_eq_point1) (P2_canonical_finite_guard_r_eq_point1)) )
  **  (store_afpoint point2_pre P2_canonical_finite_guard_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include basepoint_bytes_Strategy_Correct.
Include basepoint_table_points_Strategy_Correct.

Axiom proof_of_ML_mul_basepoint_safety_wit_1 : ML_mul_basepoint_safety_wit_1.
Axiom proof_of_ML_mul_basepoint_safety_wit_2 : ML_mul_basepoint_safety_wit_2.
Axiom proof_of_ML_mul_basepoint_safety_wit_3 : ML_mul_basepoint_safety_wit_3.
Axiom proof_of_ML_mul_basepoint_safety_wit_4 : ML_mul_basepoint_safety_wit_4.
Axiom proof_of_ML_mul_basepoint_safety_wit_5 : ML_mul_basepoint_safety_wit_5.
Axiom proof_of_ML_mul_basepoint_safety_wit_6 : ML_mul_basepoint_safety_wit_6.
Axiom proof_of_ML_mul_basepoint_safety_wit_7 : ML_mul_basepoint_safety_wit_7.
Axiom proof_of_ML_mul_basepoint_safety_wit_8 : ML_mul_basepoint_safety_wit_8.
Axiom proof_of_ML_mul_basepoint_safety_wit_9 : ML_mul_basepoint_safety_wit_9.
Axiom proof_of_ML_mul_basepoint_safety_wit_10 : ML_mul_basepoint_safety_wit_10.
Axiom proof_of_ML_mul_basepoint_safety_wit_11 : ML_mul_basepoint_safety_wit_11.
Axiom proof_of_ML_mul_basepoint_safety_wit_12 : ML_mul_basepoint_safety_wit_12.
Axiom proof_of_ML_mul_basepoint_safety_wit_13 : ML_mul_basepoint_safety_wit_13.
Axiom proof_of_ML_mul_basepoint_safety_wit_14 : ML_mul_basepoint_safety_wit_14.
Axiom proof_of_ML_mul_basepoint_safety_wit_15 : ML_mul_basepoint_safety_wit_15.
Axiom proof_of_ML_mul_basepoint_entail_wit_1 : ML_mul_basepoint_entail_wit_1.
Axiom proof_of_ML_mul_basepoint_entail_wit_2 : ML_mul_basepoint_entail_wit_2.
Axiom proof_of_ML_mul_basepoint_entail_wit_3 : ML_mul_basepoint_entail_wit_3.
Axiom proof_of_ML_mul_basepoint_entail_wit_4 : ML_mul_basepoint_entail_wit_4.
Axiom proof_of_ML_mul_basepoint_entail_wit_5 : ML_mul_basepoint_entail_wit_5.
Axiom proof_of_ML_mul_basepoint_entail_wit_6 : ML_mul_basepoint_entail_wit_6.
Axiom proof_of_ML_mul_basepoint_entail_wit_7 : ML_mul_basepoint_entail_wit_7.
Axiom proof_of_ML_mul_basepoint_entail_wit_8 : ML_mul_basepoint_entail_wit_8.
Axiom proof_of_ML_mul_basepoint_entail_wit_9 : ML_mul_basepoint_entail_wit_9.
Axiom proof_of_ML_mul_basepoint_return_wit_1 : ML_mul_basepoint_return_wit_1.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_1 : ML_mul_basepoint_partial_solve_wit_1.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_2 : ML_mul_basepoint_partial_solve_wit_2.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_3 : ML_mul_basepoint_partial_solve_wit_3.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_4 : ML_mul_basepoint_partial_solve_wit_4.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_5_pure : ML_mul_basepoint_partial_solve_wit_5_pure.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_5 : ML_mul_basepoint_partial_solve_wit_5.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_6 : ML_mul_basepoint_partial_solve_wit_6.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_7 : ML_mul_basepoint_partial_solve_wit_7.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_8 : ML_mul_basepoint_partial_solve_wit_8.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_9 : ML_mul_basepoint_partial_solve_wit_9.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_10_pure : ML_mul_basepoint_partial_solve_wit_10_pure.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_10 : ML_mul_basepoint_partial_solve_wit_10.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_11_pure : ML_mul_basepoint_partial_solve_wit_11_pure.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_11 : ML_mul_basepoint_partial_solve_wit_11.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_12_pure : ML_mul_basepoint_partial_solve_wit_12_pure.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_12 : ML_mul_basepoint_partial_solve_wit_12.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_13_pure : ML_mul_basepoint_partial_solve_wit_13_pure.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_13 : ML_mul_basepoint_partial_solve_wit_13.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_14_pure : ML_mul_basepoint_partial_solve_wit_14_pure.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_14 : ML_mul_basepoint_partial_solve_wit_14.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_15_pure : ML_mul_basepoint_partial_solve_wit_15_pure.
Axiom proof_of_ML_mul_basepoint_partial_solve_wit_15 : ML_mul_basepoint_partial_solve_wit_15.
Axiom proof_of_ML_mul_basepoint_which_implies_wit_1 : ML_mul_basepoint_which_implies_wit_1.
Axiom proof_of_ML_mul_basepoint_which_implies_wit_2 : ML_mul_basepoint_which_implies_wit_2.
Axiom proof_of_ML_mul_basepoint_which_implies_wit_3 : ML_mul_basepoint_which_implies_wit_3.
Axiom proof_of_ML_mul_basepoint_which_implies_wit_4 : ML_mul_basepoint_which_implies_wit_4.
Axiom proof_of_ML_mul_basepoint_which_implies_wit_5 : ML_mul_basepoint_which_implies_wit_5.
Axiom proof_of_ML_mul_basepoint_which_implies_wit_6 : ML_mul_basepoint_which_implies_wit_6.
Axiom proof_of_add_JPoint_and_AFPoint_derive_canonical_finite_guard_r_eq_point1_by_canonical_r_eq_point1 : add_JPoint_and_AFPoint_derive_canonical_finite_guard_r_eq_point1_by_canonical_r_eq_point1.

End VC_Correct.
