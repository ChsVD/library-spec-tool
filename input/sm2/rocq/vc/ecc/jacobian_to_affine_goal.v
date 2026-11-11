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
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.

(*----- Function jacobian_to_affine -----*)

Definition jacobian_to_affine_safety_wit_1_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (JZ_non_alias = 0)) (PreH6 : (JZ_non_alias < SM2_P_Z)) (PreH7 : (0 <= JZ_non_alias)) (PreH8 : (JY_non_alias < SM2_P_Z)) (PreH9 : (0 <= JY_non_alias)) (PreH10 : (JX_non_alias < SM2_P_Z)) (PreH11 : (0 <= JX_non_alias)) (PreH12 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition jacobian_to_affine_safety_wit_2_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (JZ_non_alias <> 0)) (PreH6 : (JZ_non_alias < SM2_P_Z)) (PreH7 : (0 <= JZ_non_alias)) (PreH8 : (JY_non_alias < SM2_P_Z)) (PreH9 : (0 <= JY_non_alias)) (PreH10 : (JX_non_alias < SM2_P_Z)) (PreH11 : (0 <= JX_non_alias)) (PreH12 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition jacobian_to_affine_safety_wit_3_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (JZ_non_alias <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (JZ_non_alias = 0)) (PreH10 : (JZ_non_alias < SM2_P_Z)) (PreH11 : (0 <= JZ_non_alias)) (PreH12 : (JY_non_alias < SM2_P_Z)) (PreH13 : (0 <= JY_non_alias)) (PreH14 : (JX_non_alias < SM2_P_Z)) (PreH15 : (0 <= JX_non_alias)) (PreH16 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition jacobian_to_affine_safety_wit_4_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (JX_non_alias = 1)) (PreH5 : (JY_non_alias = 1)) (PreH6 : (JZ_non_alias = 0)) (PreH7 : (retval <> 0)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (retval = 1)) (PreH11 : (JZ_non_alias = 0)) (PreH12 : (JZ_non_alias < SM2_P_Z)) (PreH13 : (0 <= JZ_non_alias)) (PreH14 : (JY_non_alias < SM2_P_Z)) (PreH15 : (0 <= JY_non_alias)) (PreH16 : (JX_non_alias < SM2_P_Z)) (PreH17 : (0 <= JX_non_alias)) (PreH18 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH19 : (retval_2 = 0)) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition jacobian_to_affine_safety_wit_5_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (JY_non_alias <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (JZ_non_alias = 0)) (PreH10 : (JZ_non_alias < SM2_P_Z)) (PreH11 : (0 <= JZ_non_alias)) (PreH12 : (JY_non_alias < SM2_P_Z)) (PreH13 : (0 <= JY_non_alias)) (PreH14 : (JX_non_alias < SM2_P_Z)) (PreH15 : (0 <= JX_non_alias)) (PreH16 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH17 : (retval_2 <> 0)) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition jacobian_to_affine_safety_wit_6_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (JX_non_alias <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (JZ_non_alias = 0)) (PreH10 : (JZ_non_alias < SM2_P_Z)) (PreH11 : (0 <= JZ_non_alias)) (PreH12 : (JY_non_alias < SM2_P_Z)) (PreH13 : (0 <= JY_non_alias)) (PreH14 : (JX_non_alias < SM2_P_Z)) (PreH15 : (0 <= JX_non_alias)) (PreH16 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH17 : (retval_2 <> 0)) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition jacobian_to_affine_safety_wit_7_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (JX_non_alias = 1)) (PreH5 : (JY_non_alias = 1)) (PreH6 : (JZ_non_alias = 0)) (PreH7 : (retval <> 0)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (retval = 1)) (PreH11 : (JZ_non_alias = 0)) (PreH12 : (JZ_non_alias < SM2_P_Z)) (PreH13 : (0 <= JZ_non_alias)) (PreH14 : (JY_non_alias < SM2_P_Z)) (PreH15 : (0 <= JY_non_alias)) (PreH16 : (JX_non_alias < SM2_P_Z)) (PreH17 : (0 <= JX_non_alias)) (PreH18 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH19 : (retval_2 <> 0)) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition jacobian_to_affine_entail_wit_1_1_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= 1)) (PreH3 : (retval_4 = 1)) (PreH4 : (JX_non_alias = 1)) (PreH5 : (JY_non_alias = 1)) (PreH6 : (JZ_non_alias = 0)) (PreH7 : (retval <> 0)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (retval = 1)) (PreH11 : (JZ_non_alias = 0)) (PreH12 : (JZ_non_alias < SM2_P_Z)) (PreH13 : (0 <= JZ_non_alias)) (PreH14 : (JY_non_alias < SM2_P_Z)) (PreH15 : (0 <= JY_non_alias)) (PreH16 : (JX_non_alias < SM2_P_Z)) (PreH17 : (0 <= JX_non_alias)) (PreH18 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH19 : (retval_4 = 0)) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (JY_non_alias <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (JX_non_alias <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition jacobian_to_affine_entail_wit_1_2_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (JY_non_alias <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (JZ_non_alias = 0)) (PreH10 : (JZ_non_alias < SM2_P_Z)) (PreH11 : (0 <= JZ_non_alias)) (PreH12 : (JY_non_alias < SM2_P_Z)) (PreH13 : (0 <= JY_non_alias)) (PreH14 : (JX_non_alias < SM2_P_Z)) (PreH15 : (0 <= JX_non_alias)) (PreH16 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH17 : (retval_2 = 0)) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (JY_non_alias <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (JX_non_alias <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition jacobian_to_affine_entail_wit_1_3_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : (JX_non_alias <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (JZ_non_alias = 0)) (PreH10 : (JZ_non_alias < SM2_P_Z)) (PreH11 : (0 <= JZ_non_alias)) (PreH12 : (JY_non_alias < SM2_P_Z)) (PreH13 : (0 <= JY_non_alias)) (PreH14 : (JX_non_alias < SM2_P_Z)) (PreH15 : (0 <= JX_non_alias)) (PreH16 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH17 : (retval_3 = 0)) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (JY_non_alias <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (JX_non_alias <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition jacobian_to_affine_entail_wit_2_1_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (JX_non_alias = 1)) (PreH5 : (JY_non_alias = 1)) (PreH6 : (JZ_non_alias = 0)) (PreH7 : (retval <> 0)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (retval = 1)) (PreH11 : (JZ_non_alias = 0)) (PreH12 : (JZ_non_alias < SM2_P_Z)) (PreH13 : (0 <= JZ_non_alias)) (PreH14 : (JY_non_alias < SM2_P_Z)) (PreH15 : (0 <= JY_non_alias)) (PreH16 : (JX_non_alias < SM2_P_Z)) (PreH17 : (0 <= JX_non_alias)) (PreH18 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH19 : (retval_2 <> 0)) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (JX_non_alias = 1) ” 
  &&  “ (JY_non_alias = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition jacobian_to_affine_entail_wit_2_2_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : (JY_non_alias <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (JZ_non_alias = 0)) (PreH10 : (JZ_non_alias < SM2_P_Z)) (PreH11 : (0 <= JZ_non_alias)) (PreH12 : (JY_non_alias < SM2_P_Z)) (PreH13 : (0 <= JY_non_alias)) (PreH14 : (JX_non_alias < SM2_P_Z)) (PreH15 : (0 <= JX_non_alias)) (PreH16 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH17 : (retval_3 <> 0)) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (JX_non_alias = 1) ” 
  &&  “ (JY_non_alias = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition jacobian_to_affine_entail_wit_2_3_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : (JX_non_alias <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (JZ_non_alias = 0)) (PreH10 : (JZ_non_alias < SM2_P_Z)) (PreH11 : (0 <= JZ_non_alias)) (PreH12 : (JY_non_alias < SM2_P_Z)) (PreH13 : (0 <= JY_non_alias)) (PreH14 : (JX_non_alias < SM2_P_Z)) (PreH15 : (0 <= JX_non_alias)) (PreH16 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH17 : (retval_3 <> 0)) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (JX_non_alias = 1) ” 
  &&  “ (JY_non_alias = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition jacobian_to_affine_return_wit_1_non_alias := 
(
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (Ainv: Z) (PreH1 : (0 <= Ainv)) (PreH2 : (Ainv < SM2_P_Z)) (PreH3 : ((Zmod ((JZ_non_alias * Ainv )) (SM2_P_Z)) = 1)) (PreH4 : (retval = 0)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (JZ_non_alias <> 0)) (PreH9 : (JZ_non_alias < SM2_P_Z)) (PreH10 : (0 <= JZ_non_alias)) (PreH11 : (JY_non_alias < SM2_P_Z)) (PreH12 : (0 <= JY_non_alias)) (PreH13 : (JX_non_alias < SM2_P_Z)) (PreH14 : (0 <= JX_non_alias)) (PreH15 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  (store_fp &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((result_pre)  # "AFPoint" ->ₛ "y") (Zmod ((JY_non_alias * (Zmod (((Zmod ((Ainv * Ainv )) (SM2_P_Z)) * Ainv )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "AFPoint" ->ₛ "x") (Zmod ((JX_non_alias * (Zmod ((Ainv * Ainv )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
|--
  EX (RX: Z)  (RY: Z) ,
  “ (jpoint_to_afpoint_coordinates JX_non_alias JY_non_alias JZ_non_alias RX RY ) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (store_afpoint_fields result_pre RX RY )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (Ainv: Z) (PreH1 : (0 <= Ainv)) (PreH2 : (Ainv < SM2_P_Z)) (PreH3 : ((Zmod ((JZ_non_alias * Ainv )) (SM2_P_Z)) = 1)) (PreH4 : (retval = 0)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (JZ_non_alias <> 0)) (PreH9 : (JZ_non_alias < SM2_P_Z)) (PreH10 : (0 <= JZ_non_alias)) (PreH11 : (JY_non_alias < SM2_P_Z)) (PreH12 : (0 <= JY_non_alias)) (PreH13 : (JX_non_alias < SM2_P_Z)) (PreH14 : (0 <= JX_non_alias)) (PreH15 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  TT && emp 
|--
  “ (jpoint_to_afpoint_coordinates JX_non_alias JY_non_alias JZ_non_alias (Zmod ((JX_non_alias * (Zmod ((Ainv * Ainv )) (SM2_P_Z)) )) (SM2_P_Z)) (Zmod ((JY_non_alias * (Zmod (((Zmod ((Ainv * Ainv )) (SM2_P_Z)) * Ainv )) (SM2_P_Z)) )) (SM2_P_Z)) ) ”
  &&  emp
).

Definition jacobian_to_affine_return_wit_1_non_alias_split_goal_1 := 
forall (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (Ainv: Z) (PreH1 : (0 <= Ainv)) (PreH2 : (Ainv < SM2_P_Z)) (PreH3 : ((Zmod ((JZ_non_alias * Ainv )) (SM2_P_Z)) = 1)) (PreH4 : (retval = 0)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (JZ_non_alias <> 0)) (PreH9 : (JZ_non_alias < SM2_P_Z)) (PreH10 : (0 <= JZ_non_alias)) (PreH11 : (JY_non_alias < SM2_P_Z)) (PreH12 : (0 <= JY_non_alias)) (PreH13 : (JX_non_alias < SM2_P_Z)) (PreH14 : (0 <= JX_non_alias)) (PreH15 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  (jpoint_to_afpoint_coordinates JX_non_alias JY_non_alias JZ_non_alias (Zmod ((JX_non_alias * (Zmod ((Ainv * Ainv )) (SM2_P_Z)) )) (SM2_P_Z)) (Zmod ((JY_non_alias * (Zmod (((Zmod ((Ainv * Ainv )) (SM2_P_Z)) * Ainv )) (SM2_P_Z)) )) (SM2_P_Z)) )
.

Definition jacobian_to_affine_return_wit_2_non_alias := 
(
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = result_pre)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (JX_non_alias = 1)) (PreH6 : (JY_non_alias = 1)) (PreH7 : (JZ_non_alias = 0)) (PreH8 : (retval <> 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 1)) (PreH12 : (JZ_non_alias = 0)) (PreH13 : (JZ_non_alias < SM2_P_Z)) (PreH14 : (0 <= JZ_non_alias)) (PreH15 : (JY_non_alias < SM2_P_Z)) (PreH16 : (0 <= JY_non_alias)) (PreH17 : (JX_non_alias < SM2_P_Z)) (PreH18 : (0 <= JX_non_alias)) (PreH19 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH20 : (retval_2 <> 0)) ,
  (store_afpoint_fields result_pre 0 0 )
  **  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (RX: Z)  (RY: Z) ,
  “ (jpoint_to_afpoint_coordinates JX_non_alias JY_non_alias JZ_non_alias RX RY ) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (store_afpoint_fields result_pre RX RY )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = result_pre)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (JX_non_alias = 1)) (PreH6 : (JY_non_alias = 1)) (PreH7 : (JZ_non_alias = 0)) (PreH8 : (retval <> 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 1)) (PreH12 : (JZ_non_alias = 0)) (PreH13 : (JZ_non_alias < SM2_P_Z)) (PreH14 : (0 <= JZ_non_alias)) (PreH15 : (JY_non_alias < SM2_P_Z)) (PreH16 : (0 <= JY_non_alias)) (PreH17 : (JX_non_alias < SM2_P_Z)) (PreH18 : (0 <= JX_non_alias)) (PreH19 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH20 : (retval_2 <> 0)) ,
  TT && emp 
|--
  “ (jpoint_to_afpoint_coordinates 1 1 0 0 0 ) ”
  &&  emp
).

Definition jacobian_to_affine_return_wit_2_non_alias_split_goal_1 := 
forall (result_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = result_pre)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (JX_non_alias = 1)) (PreH6 : (JY_non_alias = 1)) (PreH7 : (JZ_non_alias = 0)) (PreH8 : (retval <> 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 1)) (PreH12 : (JZ_non_alias = 0)) (PreH13 : (JZ_non_alias < SM2_P_Z)) (PreH14 : (0 <= JZ_non_alias)) (PreH15 : (JY_non_alias < SM2_P_Z)) (PreH16 : (0 <= JY_non_alias)) (PreH17 : (JX_non_alias < SM2_P_Z)) (PreH18 : (0 <= JX_non_alias)) (PreH19 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH20 : (retval_2 <> 0)) ,
  (jpoint_to_afpoint_coordinates 1 1 0 0 0 )
.

Definition jacobian_to_affine_return_wit_3_non_alias := 
(
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (JY_non_alias <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (JZ_non_alias = 0)) (PreH10 : (JZ_non_alias < SM2_P_Z)) (PreH11 : (0 <= JZ_non_alias)) (PreH12 : (JY_non_alias < SM2_P_Z)) (PreH13 : (0 <= JY_non_alias)) (PreH14 : (JX_non_alias < SM2_P_Z)) (PreH15 : (0 <= JX_non_alias)) (PreH16 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH17 : (retval_2 = 0)) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (RX: Z)  (RY: Z) ,
  “ (jpoint_to_afpoint_coordinates JX_non_alias JY_non_alias JZ_non_alias RX RY ) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (store_afpoint_fields result_pre RX RY )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (JY_non_alias <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (JZ_non_alias = 0)) (PreH10 : (JZ_non_alias < SM2_P_Z)) (PreH11 : (0 <= JZ_non_alias)) (PreH12 : (JY_non_alias < SM2_P_Z)) (PreH13 : (0 <= JY_non_alias)) (PreH14 : (JX_non_alias < SM2_P_Z)) (PreH15 : (0 <= JX_non_alias)) (PreH16 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH17 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (x3_2 < U64_MOD) ” 
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
  &&  “ (jpoint_to_afpoint_coordinates JX_non_alias JY_non_alias JZ_non_alias (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) (u256_of_limbs (x0) (x1) (x2) (x3)) ) ”
  &&  (((&((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition jacobian_to_affine_return_wit_4_non_alias := 
(
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (JX_non_alias <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (JZ_non_alias = 0)) (PreH10 : (JZ_non_alias < SM2_P_Z)) (PreH11 : (0 <= JZ_non_alias)) (PreH12 : (JY_non_alias < SM2_P_Z)) (PreH13 : (0 <= JY_non_alias)) (PreH14 : (JX_non_alias < SM2_P_Z)) (PreH15 : (0 <= JX_non_alias)) (PreH16 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH17 : (retval_2 = 0)) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (RX: Z)  (RY: Z) ,
  “ (jpoint_to_afpoint_coordinates JX_non_alias JY_non_alias JZ_non_alias RX RY ) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (store_afpoint_fields result_pre RX RY )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (JX_non_alias <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (JZ_non_alias = 0)) (PreH10 : (JZ_non_alias < SM2_P_Z)) (PreH11 : (0 <= JZ_non_alias)) (PreH12 : (JY_non_alias < SM2_P_Z)) (PreH13 : (0 <= JY_non_alias)) (PreH14 : (JX_non_alias < SM2_P_Z)) (PreH15 : (0 <= JX_non_alias)) (PreH16 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH17 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (x3_2 < U64_MOD) ” 
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
  &&  “ (jpoint_to_afpoint_coordinates JX_non_alias JY_non_alias JZ_non_alias (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) (u256_of_limbs (x0) (x1) (x2) (x3)) ) ”
  &&  (((&((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
).

Definition jacobian_to_affine_partial_solve_wit_1_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (PreH1 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ”
  &&  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition jacobian_to_affine_partial_solve_wit_2_non_alias_pure := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (JZ_non_alias <> 0)) (PreH6 : (JZ_non_alias < SM2_P_Z)) (PreH7 : (0 <= JZ_non_alias)) (PreH8 : (JY_non_alias < SM2_P_Z)) (PreH9 : (0 <= JY_non_alias)) (PreH10 : (JX_non_alias < SM2_P_Z)) (PreH11 : (0 <= JX_non_alias)) (PreH12 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (JZ_non_alias <> 0) ”
.

Definition jacobian_to_affine_partial_solve_wit_2_non_alias_aux := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (JZ_non_alias <> 0)) (PreH6 : (JZ_non_alias < SM2_P_Z)) (PreH7 : (0 <= JZ_non_alias)) (PreH8 : (JY_non_alias < SM2_P_Z)) (PreH9 : (0 <= JY_non_alias)) (PreH10 : (JX_non_alias < SM2_P_Z)) (PreH11 : (0 <= JX_non_alias)) (PreH12 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (JZ_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (JZ_non_alias <> 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ”
  &&  (store_fp &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (UInt64Array.undef_full &(( &( "u" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition jacobian_to_affine_partial_solve_wit_2_non_alias := jacobian_to_affine_partial_solve_wit_2_non_alias_pure -> jacobian_to_affine_partial_solve_wit_2_non_alias_aux.

Definition jacobian_to_affine_partial_solve_wit_3_non_alias_pure := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (Ainv: Z) (PreH1 : (0 <= Ainv)) (PreH2 : (Ainv < SM2_P_Z)) (PreH3 : ((Zmod ((JZ_non_alias * Ainv )) (SM2_P_Z)) = 1)) (PreH4 : (retval = 0)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (JZ_non_alias <> 0)) (PreH9 : (JZ_non_alias < SM2_P_Z)) (PreH10 : (0 <= JZ_non_alias)) (PreH11 : (JY_non_alias < SM2_P_Z)) (PreH12 : (0 <= JY_non_alias)) (PreH13 : (JX_non_alias < SM2_P_Z)) (PreH14 : (0 <= JX_non_alias)) (PreH15 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  (store_fp &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp ( &( "u" ) ) Ainv )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "u" ) ) = ( &( "u" ) )) ”
.

Definition jacobian_to_affine_partial_solve_wit_3_non_alias_aux := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (Ainv: Z) (PreH1 : (0 <= Ainv)) (PreH2 : (Ainv < SM2_P_Z)) (PreH3 : ((Zmod ((JZ_non_alias * Ainv )) (SM2_P_Z)) = 1)) (PreH4 : (retval = 0)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (JZ_non_alias <> 0)) (PreH9 : (JZ_non_alias < SM2_P_Z)) (PreH10 : (0 <= JZ_non_alias)) (PreH11 : (JY_non_alias < SM2_P_Z)) (PreH12 : (0 <= JY_non_alias)) (PreH13 : (JX_non_alias < SM2_P_Z)) (PreH14 : (0 <= JX_non_alias)) (PreH15 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  (store_fp &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp ( &( "u" ) ) Ainv )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "u" ) ) = ( &( "u" ) )) ” 
  &&  “ (0 <= Ainv) ” 
  &&  “ (Ainv < SM2_P_Z) ” 
  &&  “ ((Zmod ((JZ_non_alias * Ainv )) (SM2_P_Z)) = 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (JZ_non_alias <> 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ”
  &&  (store_fp ( &( "u" ) ) Ainv )
  **  (UInt64Array.undef_full &(( &( "u_square" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition jacobian_to_affine_partial_solve_wit_3_non_alias := jacobian_to_affine_partial_solve_wit_3_non_alias_pure -> jacobian_to_affine_partial_solve_wit_3_non_alias_aux.

Definition jacobian_to_affine_partial_solve_wit_4_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (Ainv: Z) (PreH1 : (( &( "u" ) ) = ( &( "u" ) ))) (PreH2 : (0 <= Ainv)) (PreH3 : (Ainv < SM2_P_Z)) (PreH4 : ((Zmod ((JZ_non_alias * Ainv )) (SM2_P_Z)) = 1)) (PreH5 : (retval = 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 0)) (PreH9 : (JZ_non_alias <> 0)) (PreH10 : (JZ_non_alias < SM2_P_Z)) (PreH11 : (0 <= JZ_non_alias)) (PreH12 : (JY_non_alias < SM2_P_Z)) (PreH13 : (0 <= JY_non_alias)) (PreH14 : (JX_non_alias < SM2_P_Z)) (PreH15 : (0 <= JX_non_alias)) (PreH16 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  (store_fp ( &( "u" ) ) Ainv )
  **  (store_fp ( &( "u_square" ) ) (Zmod ((Ainv * Ainv )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= Ainv) ” 
  &&  “ (Ainv < SM2_P_Z) ” 
  &&  “ ((Zmod ((JZ_non_alias * Ainv )) (SM2_P_Z)) = 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (JZ_non_alias <> 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ”
  &&  (store_fp ( &( "u_square" ) ) (Zmod ((Ainv * Ainv )) (SM2_P_Z)) )
  **  (store_fp ( &( "u" ) ) Ainv )
  **  (UInt64Array.undef_full &(( &( "u_cube" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition jacobian_to_affine_partial_solve_wit_5_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (Ainv: Z) (PreH1 : (0 <= Ainv)) (PreH2 : (Ainv < SM2_P_Z)) (PreH3 : ((Zmod ((JZ_non_alias * Ainv )) (SM2_P_Z)) = 1)) (PreH4 : (retval = 0)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (JZ_non_alias <> 0)) (PreH9 : (JZ_non_alias < SM2_P_Z)) (PreH10 : (0 <= JZ_non_alias)) (PreH11 : (JY_non_alias < SM2_P_Z)) (PreH12 : (0 <= JY_non_alias)) (PreH13 : (JX_non_alias < SM2_P_Z)) (PreH14 : (0 <= JX_non_alias)) (PreH15 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  (store_fp ( &( "u_square" ) ) (Zmod ((Ainv * Ainv )) (SM2_P_Z)) )
  **  (store_fp ( &( "u" ) ) Ainv )
  **  (store_fp ( &( "u_cube" ) ) (Zmod (((Zmod ((Ainv * Ainv )) (SM2_P_Z)) * Ainv )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= Ainv) ” 
  &&  “ (Ainv < SM2_P_Z) ” 
  &&  “ ((Zmod ((JZ_non_alias * Ainv )) (SM2_P_Z)) = 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (JZ_non_alias <> 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ”
  &&  (store_fp &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp ( &( "u_square" ) ) (Zmod ((Ainv * Ainv )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "u" ) ) Ainv )
  **  (store_fp ( &( "u_cube" ) ) (Zmod (((Zmod ((Ainv * Ainv )) (SM2_P_Z)) * Ainv )) (SM2_P_Z)) )
  **  (store_fp &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition jacobian_to_affine_partial_solve_wit_6_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (Ainv: Z) (PreH1 : (0 <= Ainv)) (PreH2 : (Ainv < SM2_P_Z)) (PreH3 : ((Zmod ((JZ_non_alias * Ainv )) (SM2_P_Z)) = 1)) (PreH4 : (retval = 0)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (JZ_non_alias <> 0)) (PreH9 : (JZ_non_alias < SM2_P_Z)) (PreH10 : (0 <= JZ_non_alias)) (PreH11 : (JY_non_alias < SM2_P_Z)) (PreH12 : (0 <= JY_non_alias)) (PreH13 : (JX_non_alias < SM2_P_Z)) (PreH14 : (0 <= JX_non_alias)) (PreH15 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  (store_fp &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp ( &( "u_square" ) ) (Zmod ((Ainv * Ainv )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "AFPoint" ->ₛ "x") (Zmod ((JX_non_alias * (Zmod ((Ainv * Ainv )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "u" ) ) Ainv )
  **  (store_fp ( &( "u_cube" ) ) (Zmod (((Zmod ((Ainv * Ainv )) (SM2_P_Z)) * Ainv )) (SM2_P_Z)) )
  **  (store_fp &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= Ainv) ” 
  &&  “ (Ainv < SM2_P_Z) ” 
  &&  “ ((Zmod ((JZ_non_alias * Ainv )) (SM2_P_Z)) = 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (JZ_non_alias <> 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ”
  &&  (store_fp &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp ( &( "u_cube" ) ) (Zmod (((Zmod ((Ainv * Ainv )) (SM2_P_Z)) * Ainv )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp ( &( "u_square" ) ) (Zmod ((Ainv * Ainv )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "AFPoint" ->ₛ "x") (Zmod ((JX_non_alias * (Zmod ((Ainv * Ainv )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "u" ) ) Ainv )
  **  (store_fp &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
.

Definition jacobian_to_affine_partial_solve_wit_7_non_alias := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (JZ_non_alias = 0)) (PreH6 : (JZ_non_alias < SM2_P_Z)) (PreH7 : (0 <= JZ_non_alias)) (PreH8 : (JY_non_alias < SM2_P_Z)) (PreH9 : (0 <= JY_non_alias)) (PreH10 : (JX_non_alias < SM2_P_Z)) (PreH11 : (0 <= JX_non_alias)) (PreH12 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition jacobian_to_affine_partial_solve_wit_8_non_alias_pure := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (JX_non_alias = 1)) (PreH5 : (JY_non_alias = 1)) (PreH6 : (JZ_non_alias = 0)) (PreH7 : (retval <> 0)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (retval = 1)) (PreH11 : (JZ_non_alias = 0)) (PreH12 : (JZ_non_alias < SM2_P_Z)) (PreH13 : (0 <= JZ_non_alias)) (PreH14 : (JY_non_alias < SM2_P_Z)) (PreH15 : (0 <= JY_non_alias)) (PreH16 : (JX_non_alias < SM2_P_Z)) (PreH17 : (0 <= JX_non_alias)) (PreH18 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH19 : (retval_2 <> 0)) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 = 0) ” 
  &&  “ (sizeof( "AFPoint" ) = 64) ”
.

Definition jacobian_to_affine_partial_solve_wit_8_non_alias_aux := 
forall (result_pre: Z) (point_pre: Z) (JZ_non_alias: Z) (JY_non_alias: Z) (JX_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (JX_non_alias = 1)) (PreH5 : (JY_non_alias = 1)) (PreH6 : (JZ_non_alias = 0)) (PreH7 : (retval <> 0)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (retval = 1)) (PreH11 : (JZ_non_alias = 0)) (PreH12 : (JZ_non_alias < SM2_P_Z)) (PreH13 : (0 <= JZ_non_alias)) (PreH14 : (JY_non_alias < SM2_P_Z)) (PreH15 : (0 <= JY_non_alias)) (PreH16 : (JX_non_alias < SM2_P_Z)) (PreH17 : (0 <= JX_non_alias)) (PreH18 : ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias ))) (PreH19 : (retval_2 <> 0)) ,
  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 = 0) ” 
  &&  “ (sizeof( "AFPoint" ) = 64) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (JX_non_alias = 1) ” 
  &&  “ (JY_non_alias = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (JZ_non_alias = 0) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "u_cube" ) ) )
  **  (UndefStructPredu32 ( &( "u_square" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition jacobian_to_affine_partial_solve_wit_8_non_alias := jacobian_to_affine_partial_solve_wit_8_non_alias_pure -> jacobian_to_affine_partial_solve_wit_8_non_alias_aux.

Definition jacobian_to_affine_derive_point_non_alias_by_non_alias := 
forall (result_pre: Z) (point_pre: Z) (P_point_non_alias: ec_point) ,
  (store_jpoint_with_canonical_infinity point_pre P_point_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
EX (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) ,
  (“ ((JZ_non_alias = 0) -> (canonical_jpoint_infinity JX_non_alias JY_non_alias JZ_non_alias )) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  **
  ((EX RX RY,
  “ (jpoint_to_afpoint_coordinates JX_non_alias JY_non_alias JZ_non_alias RX RY ) ”
  &&  (store_jpoint_fields point_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (store_afpoint_fields result_pre RX RY )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  -*
  ((store_jpoint_with_canonical_infinity point_pre P_point_non_alias )
  **  (store_afpoint result_pre P_point_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include ecc_representation_Strategy_Correct.

Axiom proof_of_jacobian_to_affine_safety_wit_1_non_alias : jacobian_to_affine_safety_wit_1_non_alias.
Axiom proof_of_jacobian_to_affine_safety_wit_2_non_alias : jacobian_to_affine_safety_wit_2_non_alias.
Axiom proof_of_jacobian_to_affine_safety_wit_3_non_alias : jacobian_to_affine_safety_wit_3_non_alias.
Axiom proof_of_jacobian_to_affine_safety_wit_4_non_alias : jacobian_to_affine_safety_wit_4_non_alias.
Axiom proof_of_jacobian_to_affine_safety_wit_5_non_alias : jacobian_to_affine_safety_wit_5_non_alias.
Axiom proof_of_jacobian_to_affine_safety_wit_6_non_alias : jacobian_to_affine_safety_wit_6_non_alias.
Axiom proof_of_jacobian_to_affine_safety_wit_7_non_alias : jacobian_to_affine_safety_wit_7_non_alias.
Axiom proof_of_jacobian_to_affine_entail_wit_1_1_non_alias : jacobian_to_affine_entail_wit_1_1_non_alias.
Axiom proof_of_jacobian_to_affine_entail_wit_1_2_non_alias : jacobian_to_affine_entail_wit_1_2_non_alias.
Axiom proof_of_jacobian_to_affine_entail_wit_1_3_non_alias : jacobian_to_affine_entail_wit_1_3_non_alias.
Axiom proof_of_jacobian_to_affine_entail_wit_2_1_non_alias : jacobian_to_affine_entail_wit_2_1_non_alias.
Axiom proof_of_jacobian_to_affine_entail_wit_2_2_non_alias : jacobian_to_affine_entail_wit_2_2_non_alias.
Axiom proof_of_jacobian_to_affine_entail_wit_2_3_non_alias : jacobian_to_affine_entail_wit_2_3_non_alias.
Axiom proof_of_jacobian_to_affine_return_wit_1_non_alias : jacobian_to_affine_return_wit_1_non_alias.
Axiom proof_of_jacobian_to_affine_return_wit_2_non_alias : jacobian_to_affine_return_wit_2_non_alias.
Axiom proof_of_jacobian_to_affine_return_wit_3_non_alias : jacobian_to_affine_return_wit_3_non_alias.
Axiom proof_of_jacobian_to_affine_return_wit_4_non_alias : jacobian_to_affine_return_wit_4_non_alias.
Axiom proof_of_jacobian_to_affine_partial_solve_wit_1_non_alias : jacobian_to_affine_partial_solve_wit_1_non_alias.
Axiom proof_of_jacobian_to_affine_partial_solve_wit_2_non_alias_pure : jacobian_to_affine_partial_solve_wit_2_non_alias_pure.
Axiom proof_of_jacobian_to_affine_partial_solve_wit_2_non_alias : jacobian_to_affine_partial_solve_wit_2_non_alias.
Axiom proof_of_jacobian_to_affine_partial_solve_wit_3_non_alias_pure : jacobian_to_affine_partial_solve_wit_3_non_alias_pure.
Axiom proof_of_jacobian_to_affine_partial_solve_wit_3_non_alias : jacobian_to_affine_partial_solve_wit_3_non_alias.
Axiom proof_of_jacobian_to_affine_partial_solve_wit_4_non_alias : jacobian_to_affine_partial_solve_wit_4_non_alias.
Axiom proof_of_jacobian_to_affine_partial_solve_wit_5_non_alias : jacobian_to_affine_partial_solve_wit_5_non_alias.
Axiom proof_of_jacobian_to_affine_partial_solve_wit_6_non_alias : jacobian_to_affine_partial_solve_wit_6_non_alias.
Axiom proof_of_jacobian_to_affine_partial_solve_wit_7_non_alias : jacobian_to_affine_partial_solve_wit_7_non_alias.
Axiom proof_of_jacobian_to_affine_partial_solve_wit_8_non_alias_pure : jacobian_to_affine_partial_solve_wit_8_non_alias_pure.
Axiom proof_of_jacobian_to_affine_partial_solve_wit_8_non_alias : jacobian_to_affine_partial_solve_wit_8_non_alias.
Axiom proof_of_jacobian_to_affine_derive_point_non_alias_by_non_alias : jacobian_to_affine_derive_point_non_alias_by_non_alias.

End VC_Correct.
