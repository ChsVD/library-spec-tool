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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import mul_mod_p_def.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import u32_alias_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import u32_alias_strategy_proof.

(*----- Function mul_mod_p -----*)

Definition mul_mod_p_safety_wit_1_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_r_eq_y = 1)) (PreH5 : (X_r_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_y)) (PreH7 : (result_pre = y_pre)) (PreH8 : (retval = 0)) ,
  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_2_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_r_eq_x = 1)) (PreH5 : (X_r_eq_x < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_x)) (PreH7 : (result_pre = x_pre)) (PreH8 : (retval = 0)) ,
  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_3_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_x_eq_y = 1)) (PreH5 : (X_x_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_x_eq_y)) (PreH7 : (x_pre = y_pre)) (PreH8 : (retval = 0)) ,
  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_4_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_non_alias = 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval = 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_5_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X_r_eq_y <> 1)) (PreH5 : (X_r_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_y)) (PreH7 : (result_pre = y_pre)) (PreH8 : (retval <> 0)) ,
  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_6_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X_r_eq_x <> 1)) (PreH5 : (X_r_eq_x < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_x)) (PreH7 : (result_pre = x_pre)) (PreH8 : (retval <> 0)) ,
  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_7_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X_x_eq_y <> 1)) (PreH5 : (X_x_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_x_eq_y)) (PreH7 : (x_pre = y_pre)) (PreH8 : (retval <> 0)) ,
  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_8_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X_non_alias <> 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval <> 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_9_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) = 1)) (PreH5 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) (PreH14 : (0 <= retval)) (PreH15 : (retval <= 1)) (PreH16 : (retval = 0)) (PreH17 : (X_x_eq_y <> 1)) (PreH18 : (X_x_eq_y < SM2_P_Z)) (PreH19 : (0 <= X_x_eq_y)) (PreH20 : (x_pre = y_pre)) (PreH21 : (retval = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_10_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1)) (PreH5 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_y < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_y)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_y <> 1)) (PreH29 : (X_r_eq_y < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_y)) (PreH31 : (result_pre = y_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_11_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1)) (PreH5 : (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_x < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_x)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_x <> 1)) (PreH29 : (X_r_eq_x < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_x)) (PreH31 : (result_pre = x_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_12_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1)) (PreH5 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_non_alias < SM2_P_Z)) (PreH24 : (0 <= Y_non_alias)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_non_alias <> 1)) (PreH29 : (X_non_alias < SM2_P_Z)) (PreH30 : (0 <= X_non_alias)) (PreH31 : (retval = 0)) (PreH32 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_13_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_y < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_y)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_y <> 1)) (PreH29 : (X_r_eq_y < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_y)) (PreH31 : (result_pre = y_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_14_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_x < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_x)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_x <> 1)) (PreH29 : (X_r_eq_x < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_x)) (PreH31 : (result_pre = x_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_15_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) <> 1)) (PreH5 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) (PreH14 : (0 <= retval)) (PreH15 : (retval <= 1)) (PreH16 : (retval = 0)) (PreH17 : (X_x_eq_y <> 1)) (PreH18 : (X_x_eq_y < SM2_P_Z)) (PreH19 : (0 <= X_x_eq_y)) (PreH20 : (x_pre = y_pre)) (PreH21 : (retval = 0)) (PreH22 : (retval_2 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_16_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_non_alias < SM2_P_Z)) (PreH24 : (0 <= Y_non_alias)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_non_alias <> 1)) (PreH29 : (X_non_alias < SM2_P_Z)) (PreH30 : (0 <= X_non_alias)) (PreH31 : (retval = 0)) (PreH32 : (retval_2 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition mul_mod_p_safety_wit_17_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_y < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_y)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_y <> 1)) (PreH29 : (X_r_eq_y < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_y)) (PreH31 : (result_pre = y_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_18_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_y < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_y)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_y <> 1)) (PreH29 : (X_r_eq_y < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_y)) (PreH31 : (result_pre = y_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_19_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_y < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_y)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_y <> 1)) (PreH29 : (X_r_eq_y < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_y)) (PreH31 : (result_pre = y_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_20_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_x < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_x)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_x <> 1)) (PreH29 : (X_r_eq_x < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_x)) (PreH31 : (result_pre = x_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_21_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_x < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_x)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_x <> 1)) (PreH29 : (X_r_eq_x < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_x)) (PreH31 : (result_pre = x_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_22_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_x < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_x)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_x <> 1)) (PreH29 : (X_r_eq_x < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_x)) (PreH31 : (result_pre = x_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_23_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) <> 1)) (PreH5 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) (PreH14 : (0 <= retval)) (PreH15 : (retval <= 1)) (PreH16 : (retval = 0)) (PreH17 : (X_x_eq_y <> 1)) (PreH18 : (X_x_eq_y < SM2_P_Z)) (PreH19 : (0 <= X_x_eq_y)) (PreH20 : (x_pre = y_pre)) (PreH21 : (retval = 0)) (PreH22 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_24_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) <> 1)) (PreH5 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) (PreH14 : (0 <= retval)) (PreH15 : (retval <= 1)) (PreH16 : (retval = 0)) (PreH17 : (X_x_eq_y <> 1)) (PreH18 : (X_x_eq_y < SM2_P_Z)) (PreH19 : (0 <= X_x_eq_y)) (PreH20 : (x_pre = y_pre)) (PreH21 : (retval = 0)) (PreH22 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_25_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) <> 1)) (PreH5 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) (PreH14 : (0 <= retval)) (PreH15 : (retval <= 1)) (PreH16 : (retval = 0)) (PreH17 : (X_x_eq_y <> 1)) (PreH18 : (X_x_eq_y < SM2_P_Z)) (PreH19 : (0 <= X_x_eq_y)) (PreH20 : (x_pre = y_pre)) (PreH21 : (retval = 0)) (PreH22 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_26_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_non_alias < SM2_P_Z)) (PreH24 : (0 <= Y_non_alias)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_non_alias <> 1)) (PreH29 : (X_non_alias < SM2_P_Z)) (PreH30 : (0 <= X_non_alias)) (PreH31 : (retval = 0)) (PreH32 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_27_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_non_alias < SM2_P_Z)) (PreH24 : (0 <= Y_non_alias)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_non_alias <> 1)) (PreH29 : (X_non_alias < SM2_P_Z)) (PreH30 : (0 <= X_non_alias)) (PreH31 : (retval = 0)) (PreH32 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_28_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_non_alias < SM2_P_Z)) (PreH24 : (0 <= Y_non_alias)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_non_alias <> 1)) (PreH29 : (X_non_alias < SM2_P_Z)) (PreH30 : (0 <= X_non_alias)) (PreH31 : (retval = 0)) (PreH32 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_29_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= (X_r_eq_y * Y_r_eq_y ))) (PreH2 : ((X_r_eq_y * Y_r_eq_y ) < U512_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH7 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (Y_r_eq_y < SM2_P_Z)) (PreH26 : (0 <= Y_r_eq_y)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 0)) (PreH30 : (X_r_eq_y <> 1)) (PreH31 : (X_r_eq_y < SM2_P_Z)) (PreH32 : (0 <= X_r_eq_y)) (PreH33 : (result_pre = y_pre)) (PreH34 : (retval = 0)) (PreH35 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_y )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_y )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_y * Y_r_eq_y ) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_30_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH2 : ((X_r_eq_x * Y_r_eq_x ) < U512_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH7 : (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (Y_r_eq_x < SM2_P_Z)) (PreH26 : (0 <= Y_r_eq_x)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 0)) (PreH30 : (X_r_eq_x <> 1)) (PreH31 : (X_r_eq_x < SM2_P_Z)) (PreH32 : (0 <= X_r_eq_x)) (PreH33 : (result_pre = x_pre)) (PreH34 : (retval = 0)) (PreH35 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * Y_r_eq_x ) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_31_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_2: Z) (PreH1 : ((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))) (PreH2 : (0 <= (X_x_eq_y * X_x_eq_y ))) (PreH3 : ((X_x_eq_y * X_x_eq_y ) < U512_MOD)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : ((u256_of_limbs (x0) (x1) (x2) (x3)) <> 1)) (PreH8 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 0)) (PreH20 : (X_x_eq_y <> 1)) (PreH21 : (X_x_eq_y < SM2_P_Z)) (PreH22 : (0 <= X_x_eq_y)) (PreH23 : (x_pre = y_pre)) (PreH24 : (retval = 0)) (PreH25 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_x_eq_y )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_x_eq_y * X_x_eq_y ) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_safety_wit_32_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= (X_non_alias * Y_non_alias ))) (PreH2 : ((X_non_alias * Y_non_alias ) < U512_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH7 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (Y_non_alias < SM2_P_Z)) (PreH26 : (0 <= Y_non_alias)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 0)) (PreH30 : (X_non_alias <> 1)) (PreH31 : (X_non_alias < SM2_P_Z)) (PreH32 : (0 <= X_non_alias)) (PreH33 : (retval = 0)) (PreH34 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * Y_non_alias ) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mul_mod_p_entail_wit_1_1_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 1)) (PreH4 : (X_r_eq_y = 1)) (PreH5 : (X_r_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_y)) (PreH7 : (result_pre = y_pre)) (PreH8 : (retval_5 = 0)) ,
  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_1_2_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X_r_eq_y <> 1)) (PreH5 : (X_r_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_y)) (PreH7 : (result_pre = y_pre)) (PreH8 : (retval = 0)) ,
  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_1_3_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 1)) (PreH4 : (X_r_eq_x = 1)) (PreH5 : (X_r_eq_x < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_x)) (PreH7 : (result_pre = x_pre)) (PreH8 : (retval_5 = 0)) ,
  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_1_4_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (X_r_eq_x <> 1)) (PreH5 : (X_r_eq_x < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_x)) (PreH7 : (result_pre = x_pre)) (PreH8 : (retval_2 = 0)) ,
  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_1_5_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 1)) (PreH4 : (X_x_eq_y = 1)) (PreH5 : (X_x_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_x_eq_y)) (PreH7 : (x_pre = y_pre)) (PreH8 : (retval_5 = 0)) ,
  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_1_6_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : (X_x_eq_y <> 1)) (PreH5 : (X_x_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_x_eq_y)) (PreH7 : (x_pre = y_pre)) (PreH8 : (retval_3 = 0)) ,
  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_1_7_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 1)) (PreH4 : (X_non_alias = 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval_5 = 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_1_8_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= 1)) (PreH3 : (retval_4 = 0)) (PreH4 : (X_non_alias <> 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval_4 = 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_2_1_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_r_eq_y = 1)) (PreH5 : (X_r_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_y)) (PreH7 : (result_pre = y_pre)) (PreH8 : (retval <> 0)) ,
  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (X_r_eq_x = 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (X_x_eq_y = 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (X_non_alias = 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_2_2_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 0)) (PreH4 : (X_r_eq_y <> 1)) (PreH5 : (X_r_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_y)) (PreH7 : (result_pre = y_pre)) (PreH8 : (retval_5 <> 0)) ,
  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (X_r_eq_x = 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (X_x_eq_y = 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (X_non_alias = 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_2_3_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (X_r_eq_x = 1)) (PreH5 : (X_r_eq_x < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_x)) (PreH7 : (result_pre = x_pre)) (PreH8 : (retval_2 <> 0)) ,
  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (X_r_eq_x = 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (X_x_eq_y = 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (X_non_alias = 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_2_4_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 0)) (PreH4 : (X_r_eq_x <> 1)) (PreH5 : (X_r_eq_x < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_x)) (PreH7 : (result_pre = x_pre)) (PreH8 : (retval_5 <> 0)) ,
  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (X_r_eq_x = 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (X_x_eq_y = 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (X_non_alias = 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_2_5_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 1)) (PreH4 : (X_x_eq_y = 1)) (PreH5 : (X_x_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_x_eq_y)) (PreH7 : (x_pre = y_pre)) (PreH8 : (retval_3 <> 0)) ,
  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (X_r_eq_x = 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (X_x_eq_y = 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (X_non_alias = 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_2_6_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 0)) (PreH4 : (X_x_eq_y <> 1)) (PreH5 : (X_x_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_x_eq_y)) (PreH7 : (x_pre = y_pre)) (PreH8 : (retval_5 <> 0)) ,
  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (X_r_eq_x = 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (X_x_eq_y = 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (X_non_alias = 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_2_7_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= 1)) (PreH3 : (retval_4 = 1)) (PreH4 : (X_non_alias = 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval_4 <> 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (X_r_eq_x = 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (X_x_eq_y = 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (X_non_alias = 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_2_8_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 0)) (PreH4 : (X_non_alias <> 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval_5 <> 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (X_r_eq_x = 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (X_x_eq_y = 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (X_non_alias = 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_3_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_non_alias = 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval <> 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (X_non_alias = 1) ”
  &&  (store_fp x_pre X_non_alias )
  **  (store_fp y_pre Y_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_entail_wit_4_x_eq_y := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_x_eq_y = 1)) (PreH5 : (X_x_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_x_eq_y)) (PreH7 : (x_pre = y_pre)) (PreH8 : (retval <> 0)) ,
  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (x_pre = y_pre) ” 
  &&  “ (X_x_eq_y = 1) ”
  &&  (store_fp y_pre X_x_eq_y )
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_x_eq_y = 1)) (PreH5 : (X_x_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_x_eq_y)) (PreH7 : (x_pre = y_pre)) (PreH8 : (retval <> 0)) ,
  (store_u256 x_pre X_x_eq_y )
|--
  EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (X_x_eq_y = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Definition mul_mod_p_entail_wit_5_r_eq_x := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_r_eq_x = 1)) (PreH5 : (X_r_eq_x < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_x)) (PreH7 : (result_pre = x_pre)) (PreH8 : (retval <> 0)) ,
  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x = 1) ”
  &&  (store_fp y_pre Y_r_eq_x )
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (x_pre: Z) (X_r_eq_x: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_r_eq_x = 1)) (PreH5 : (X_r_eq_x < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_x)) (PreH7 : (result_pre = x_pre)) (PreH8 : (retval <> 0)) ,
  (store_u256 x_pre X_r_eq_x )
|--
  (UndefStructPredu32 result_pre )
).

Definition mul_mod_p_entail_wit_5_r_eq_x_split_goal_spatial := 
forall (result_pre: Z) (x_pre: Z) (X_r_eq_x: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_r_eq_x = 1)) (PreH5 : (X_r_eq_x < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_x)) (PreH7 : (result_pre = x_pre)) (PreH8 : (retval <> 0)) ,
  (store_u256 x_pre X_r_eq_x )
|--
  (UndefStructPredu32 result_pre )
.

Definition mul_mod_p_entail_wit_6_r_eq_y := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_r_eq_y = 1)) (PreH5 : (X_r_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_y)) (PreH7 : (result_pre = y_pre)) (PreH8 : (retval <> 0)) ,
  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (limbs: (@list Z)) ,
  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = Y_r_eq_y) ”
  &&  (store_fp x_pre X_r_eq_y )
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (y_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_r_eq_y = 1)) (PreH5 : (X_r_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_y)) (PreH7 : (result_pre = y_pre)) (PreH8 : (retval <> 0)) ,
  (store_fp y_pre Y_r_eq_y )
|--
  EX (limbs: (@list Z)) ,
  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = Y_r_eq_y) ”
  &&  (StructPredu32 result_pre (make_record_u32 (limbs)) )
).

Definition mul_mod_p_entail_wit_7_1_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (limbs: (@list Z)) (PreH1 : (result_pre = y_pre)) (PreH2 : (X_r_eq_y = 1)) (PreH3 : (0 <= Y_r_eq_y)) (PreH4 : (Y_r_eq_y < SM2_P_Z)) (PreH5 : ((Zlength (limbs)) = 4)) (PreH6 : (u64_list_bounded limbs )) (PreH7 : ((u64_list_value (limbs)) = Y_r_eq_y)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp x_pre X_r_eq_y )
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = Y_r_eq_y) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x = 1) ”
  &&  (store_u256 y_pre Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (X_x_eq_y = 1) ”
  &&  (store_u256 y_pre X_x_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_7_2_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (PreH1 : (result_pre = x_pre)) (PreH2 : (X_r_eq_x = 1)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp y_pre Y_r_eq_x )
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (limbs: (@list Z)) ,
  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = Y_r_eq_y) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x = 1) ”
  &&  (store_u256 y_pre Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (X_x_eq_y = 1) ”
  &&  (store_u256 y_pre X_x_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_7_3_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (PreH1 : (x_pre = y_pre)) (PreH2 : (X_x_eq_y = 1)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp y_pre X_x_eq_y )
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (limbs: (@list Z)) ,
  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = Y_r_eq_y) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x = 1) ”
  &&  (store_u256 y_pre Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (X_x_eq_y = 1) ”
  &&  (store_u256 y_pre X_x_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_7_4_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (PreH1 : (X_non_alias = 1)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp x_pre X_non_alias )
  **  (store_fp y_pre Y_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (limbs: (@list Z)) ,
  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = Y_r_eq_y) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x = 1) ”
  &&  (store_u256 y_pre Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (X_x_eq_y = 1) ”
  &&  (store_u256 y_pre X_x_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_8_1_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (limbs: (@list Z)) (PreH1 : (X_r_eq_y < SM2_P_Z)) (PreH2 : (0 <= X_r_eq_y)) (PreH3 : (result_pre = y_pre)) (PreH4 : (X_r_eq_y = 1)) (PreH5 : (0 <= Y_r_eq_y)) (PreH6 : (Y_r_eq_y < SM2_P_Z)) (PreH7 : ((Zlength (limbs)) = 4)) (PreH8 : (u64_list_bounded limbs )) (PreH9 : ((u64_list_value (limbs)) = Y_r_eq_y)) ,
  (store_u256 x_pre X_r_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = Y_r_eq_y) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (X_x_eq_y = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (X_x_eq_y = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_8_2_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (PreH1 : (Y_r_eq_x < SM2_P_Z)) (PreH2 : (0 <= Y_r_eq_x)) (PreH3 : (result_pre = x_pre)) (PreH4 : (X_r_eq_x = 1)) ,
  (store_u256 y_pre Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (limbs: (@list Z)) ,
  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = Y_r_eq_y) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (X_x_eq_y = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (X_x_eq_y = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_8_3_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (PreH1 : (X_x_eq_y < SM2_P_Z)) (PreH2 : (0 <= X_x_eq_y)) (PreH3 : (x_pre = y_pre)) (PreH4 : (X_x_eq_y = 1)) ,
  (store_u256 y_pre X_x_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (limbs: (@list Z)) ,
  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = Y_r_eq_y) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (X_x_eq_y = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (X_x_eq_y = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_8_4_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (PreH1 : (Y_non_alias < SM2_P_Z)) (PreH2 : (0 <= Y_non_alias)) (PreH3 : (X_non_alias < SM2_P_Z)) (PreH4 : (0 <= X_non_alias)) (PreH5 : (X_non_alias = 1)) ,
  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (limbs: (@list Z)) ,
  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y = 1) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = Y_r_eq_y) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (X_x_eq_y = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (X_x_eq_y = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_9_1_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X_r_eq_y <> 1)) (PreH5 : (X_r_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_y)) (PreH7 : (result_pre = y_pre)) (PreH8 : (retval = 0)) ,
  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 y_pre Y_r_eq_y )
  **  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 y_pre Y_r_eq_x )
  **  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_9_2_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (X_r_eq_x <> 1)) (PreH5 : (X_r_eq_x < SM2_P_Z)) (PreH6 : (0 <= X_r_eq_x)) (PreH7 : (result_pre = x_pre)) (PreH8 : (retval_2 = 0)) ,
  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 y_pre Y_r_eq_y )
  **  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 y_pre Y_r_eq_x )
  **  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_9_3_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : (X_x_eq_y <> 1)) (PreH5 : (X_x_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_x_eq_y)) (PreH7 : (x_pre = y_pre)) (PreH8 : (retval_3 = 0)) ,
  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 y_pre Y_r_eq_y )
  **  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 y_pre Y_r_eq_x )
  **  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_9_4_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= 1)) (PreH3 : (retval_4 = 0)) (PreH4 : (X_non_alias <> 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval_4 = 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 y_pre Y_r_eq_y )
  **  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 y_pre Y_r_eq_x )
  **  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_3: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_10_1_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (PreH1 : (Y_r_eq_y < SM2_P_Z)) (PreH2 : (0 <= Y_r_eq_y)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (X_r_eq_y <> 1)) (PreH7 : (X_r_eq_y < SM2_P_Z)) (PreH8 : (0 <= X_r_eq_y)) (PreH9 : (result_pre = y_pre)) (PreH10 : (retval = 0)) ,
  (store_u256 y_pre Y_r_eq_y )
  **  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (retval_2: Z) ,
  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_3: Z) ,
  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (retval_4: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_10_2_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_2: Z) (PreH1 : (Y_r_eq_x < SM2_P_Z)) (PreH2 : (0 <= Y_r_eq_x)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (X_r_eq_x <> 1)) (PreH7 : (X_r_eq_x < SM2_P_Z)) (PreH8 : (0 <= X_r_eq_x)) (PreH9 : (result_pre = x_pre)) (PreH10 : (retval_2 = 0)) ,
  (store_u256 y_pre Y_r_eq_x )
  **  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_3: Z) ,
  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (retval_4: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_10_3_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : (X_x_eq_y <> 1)) (PreH5 : (X_x_eq_y < SM2_P_Z)) (PreH6 : (0 <= X_x_eq_y)) (PreH7 : (x_pre = y_pre)) (PreH8 : (retval_3 = 0)) ,
  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (retval_2: Z) ,
  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (retval_4: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_10_4_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_4: Z) (PreH1 : (Y_non_alias < SM2_P_Z)) (PreH2 : (0 <= Y_non_alias)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (retval_4 = 0)) (PreH6 : (X_non_alias <> 1)) (PreH7 : (X_non_alias < SM2_P_Z)) (PreH8 : (0 <= X_non_alias)) (PreH9 : (retval_4 = 0)) ,
  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (retval_2: Z) ,
  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_2 = 0) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_3: Z) ,
  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_3 = 0) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_4 = 0) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_11_1_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_9: Z) (PreH1 : (0 <= retval_9)) (PreH2 : (retval_9 <= 1)) (PreH3 : (retval_9 = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1)) (PreH5 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_y < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_y)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_y <> 1)) (PreH29 : (X_r_eq_y < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_y)) (PreH31 : (result_pre = y_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_9 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) <> 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_5: Z) ,
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) <> 1) ” 
  &&  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (retval_7: Z) ,
  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <> 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_11_2_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_y < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_y)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_y <> 1)) (PreH29 : (X_r_eq_y < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_y)) (PreH31 : (result_pre = y_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) <> 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_5: Z) ,
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) <> 1) ” 
  &&  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (retval_7: Z) ,
  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <> 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_11_3_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_3: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_9: Z) (PreH1 : (0 <= retval_9)) (PreH2 : (retval_9 <= 1)) (PreH3 : (retval_9 = 1)) (PreH4 : ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) = 1)) (PreH5 : (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (Y_r_eq_x < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_x)) (PreH25 : (0 <= retval_3)) (PreH26 : (retval_3 <= 1)) (PreH27 : (retval_3 = 0)) (PreH28 : (X_r_eq_x <> 1)) (PreH29 : (X_r_eq_x < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_x)) (PreH31 : (result_pre = x_pre)) (PreH32 : (retval_3 = 0)) (PreH33 : (retval_9 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) <> 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_5: Z) ,
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) <> 1) ” 
  &&  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (retval_7: Z) ,
  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <> 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_11_4_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_3: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= 1)) (PreH3 : (retval_4 = 0)) (PreH4 : ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) <> 1)) (PreH5 : (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (Y_r_eq_x < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_x)) (PreH25 : (0 <= retval_3)) (PreH26 : (retval_3 <= 1)) (PreH27 : (retval_3 = 0)) (PreH28 : (X_r_eq_x <> 1)) (PreH29 : (X_r_eq_x < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_x)) (PreH31 : (result_pre = x_pre)) (PreH32 : (retval_3 = 0)) (PreH33 : (retval_4 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) <> 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_5: Z) ,
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) <> 1) ” 
  &&  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (retval_7: Z) ,
  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <> 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_11_5_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_5: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= 1)) (PreH3 : (retval_6 = 0)) (PreH4 : ((u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) <> 1)) (PreH5 : (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH6 : (x3_5 < U64_MOD)) (PreH7 : (0 <= x3_5)) (PreH8 : (x2_5 < U64_MOD)) (PreH9 : (0 <= x2_5)) (PreH10 : (x1_5 < U64_MOD)) (PreH11 : (0 <= x1_5)) (PreH12 : (x0_5 < U64_MOD)) (PreH13 : (0 <= x0_5)) (PreH14 : (0 <= retval_5)) (PreH15 : (retval_5 <= 1)) (PreH16 : (retval_5 = 0)) (PreH17 : (X_x_eq_y <> 1)) (PreH18 : (X_x_eq_y < SM2_P_Z)) (PreH19 : (0 <= X_x_eq_y)) (PreH20 : (x_pre = y_pre)) (PreH21 : (retval_5 = 0)) (PreH22 : (retval_6 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) <> 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) <> 1) ” 
  &&  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (retval_7: Z) ,
  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <> 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_11_6_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_7: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (x0_7: Z) (x1_7: Z) (x2_7: Z) (x3_7: Z) (retval_9: Z) (PreH1 : (0 <= retval_9)) (PreH2 : (retval_9 <= 1)) (PreH3 : (retval_9 = 1)) (PreH4 : ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) = 1)) (PreH5 : (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)))) (PreH6 : (x3_7 < U64_MOD)) (PreH7 : (0 <= x3_7)) (PreH8 : (x2_7 < U64_MOD)) (PreH9 : (0 <= x2_7)) (PreH10 : (x1_7 < U64_MOD)) (PreH11 : (0 <= x1_7)) (PreH12 : (x0_7 < U64_MOD)) (PreH13 : (0 <= x0_7)) (PreH14 : (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH15 : (x3_6 < U64_MOD)) (PreH16 : (0 <= x3_6)) (PreH17 : (x2_6 < U64_MOD)) (PreH18 : (0 <= x2_6)) (PreH19 : (x1_6 < U64_MOD)) (PreH20 : (0 <= x1_6)) (PreH21 : (x0_6 < U64_MOD)) (PreH22 : (0 <= x0_6)) (PreH23 : (Y_non_alias < SM2_P_Z)) (PreH24 : (0 <= Y_non_alias)) (PreH25 : (0 <= retval_7)) (PreH26 : (retval_7 <= 1)) (PreH27 : (retval_7 = 0)) (PreH28 : (X_non_alias <> 1)) (PreH29 : (X_non_alias < SM2_P_Z)) (PreH30 : (0 <= X_non_alias)) (PreH31 : (retval_7 = 0)) (PreH32 : (retval_9 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) <> 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_5: Z) ,
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) <> 1) ” 
  &&  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_8: Z) ,
  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <> 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_11_7_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_7: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (x0_7: Z) (x1_7: Z) (x2_7: Z) (x3_7: Z) (retval_8: Z) (PreH1 : (0 <= retval_8)) (PreH2 : (retval_8 <= 1)) (PreH3 : (retval_8 = 0)) (PreH4 : ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <> 1)) (PreH5 : (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)))) (PreH6 : (x3_7 < U64_MOD)) (PreH7 : (0 <= x3_7)) (PreH8 : (x2_7 < U64_MOD)) (PreH9 : (0 <= x2_7)) (PreH10 : (x1_7 < U64_MOD)) (PreH11 : (0 <= x1_7)) (PreH12 : (x0_7 < U64_MOD)) (PreH13 : (0 <= x0_7)) (PreH14 : (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH15 : (x3_6 < U64_MOD)) (PreH16 : (0 <= x3_6)) (PreH17 : (x2_6 < U64_MOD)) (PreH18 : (0 <= x2_6)) (PreH19 : (x1_6 < U64_MOD)) (PreH20 : (0 <= x1_6)) (PreH21 : (x0_6 < U64_MOD)) (PreH22 : (0 <= x0_6)) (PreH23 : (Y_non_alias < SM2_P_Z)) (PreH24 : (0 <= Y_non_alias)) (PreH25 : (0 <= retval_7)) (PreH26 : (retval_7 <= 1)) (PreH27 : (retval_7 = 0)) (PreH28 : (X_non_alias <> 1)) (PreH29 : (X_non_alias < SM2_P_Z)) (PreH30 : (0 <= X_non_alias)) (PreH31 : (retval_7 = 0)) (PreH32 : (retval_8 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) <> 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_5: Z) ,
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) <> 1) ” 
  &&  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <> 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_12_1_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1)) (PreH5 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_y < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_y)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_y <> 1)) (PreH29 : (X_r_eq_y < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_y)) (PreH31 : (result_pre = y_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) = 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_6: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_5: Z) ,
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) = 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_12_2_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_7: Z) (PreH1 : (0 <= retval_7)) (PreH2 : (retval_7 <= 1)) (PreH3 : (retval_7 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_y < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_y)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_y <> 1)) (PreH29 : (X_r_eq_y < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_y)) (PreH31 : (result_pre = y_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_7 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) = 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_6: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_5: Z) ,
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) = 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_12_3_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_3: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= 1)) (PreH3 : (retval_4 = 1)) (PreH4 : ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) = 1)) (PreH5 : (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (Y_r_eq_x < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_x)) (PreH25 : (0 <= retval_3)) (PreH26 : (retval_3 <= 1)) (PreH27 : (retval_3 = 0)) (PreH28 : (X_r_eq_x <> 1)) (PreH29 : (X_r_eq_x < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_x)) (PreH31 : (result_pre = x_pre)) (PreH32 : (retval_3 = 0)) (PreH33 : (retval_4 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) = 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_6: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_5: Z) ,
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) = 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_12_4_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_3: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_7: Z) (PreH1 : (0 <= retval_7)) (PreH2 : (retval_7 <= 1)) (PreH3 : (retval_7 = 0)) (PreH4 : ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) <> 1)) (PreH5 : (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (Y_r_eq_x < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_x)) (PreH25 : (0 <= retval_3)) (PreH26 : (retval_3 <= 1)) (PreH27 : (retval_3 = 0)) (PreH28 : (X_r_eq_x <> 1)) (PreH29 : (X_r_eq_x < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_x)) (PreH31 : (result_pre = x_pre)) (PreH32 : (retval_3 = 0)) (PreH33 : (retval_7 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) = 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_6: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_5: Z) ,
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) = 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_12_5_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_7: Z) (x0_7: Z) (x1_7: Z) (x2_7: Z) (x3_7: Z) (retval_8: Z) (PreH1 : (0 <= retval_8)) (PreH2 : (retval_8 <= 1)) (PreH3 : (retval_8 = 0)) (PreH4 : ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <> 1)) (PreH5 : (X_x_eq_y = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)))) (PreH6 : (x3_7 < U64_MOD)) (PreH7 : (0 <= x3_7)) (PreH8 : (x2_7 < U64_MOD)) (PreH9 : (0 <= x2_7)) (PreH10 : (x1_7 < U64_MOD)) (PreH11 : (0 <= x1_7)) (PreH12 : (x0_7 < U64_MOD)) (PreH13 : (0 <= x0_7)) (PreH14 : (0 <= retval_7)) (PreH15 : (retval_7 <= 1)) (PreH16 : (retval_7 = 0)) (PreH17 : (X_x_eq_y <> 1)) (PreH18 : (X_x_eq_y < SM2_P_Z)) (PreH19 : (0 <= X_x_eq_y)) (PreH20 : (x_pre = y_pre)) (PreH21 : (retval_7 = 0)) (PreH22 : (retval_8 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) = 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_6: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_5: Z) ,
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) = 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_12_6_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_5: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= 1)) (PreH3 : (retval_6 = 1)) (PreH4 : ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) = 1)) (PreH5 : (Y_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH6 : (x3_6 < U64_MOD)) (PreH7 : (0 <= x3_6)) (PreH8 : (x2_6 < U64_MOD)) (PreH9 : (0 <= x2_6)) (PreH10 : (x1_6 < U64_MOD)) (PreH11 : (0 <= x1_6)) (PreH12 : (x0_6 < U64_MOD)) (PreH13 : (0 <= x0_6)) (PreH14 : (X_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH15 : (x3_5 < U64_MOD)) (PreH16 : (0 <= x3_5)) (PreH17 : (x2_5 < U64_MOD)) (PreH18 : (0 <= x2_5)) (PreH19 : (x1_5 < U64_MOD)) (PreH20 : (0 <= x1_5)) (PreH21 : (x0_5 < U64_MOD)) (PreH22 : (0 <= x0_5)) (PreH23 : (Y_non_alias < SM2_P_Z)) (PreH24 : (0 <= Y_non_alias)) (PreH25 : (0 <= retval_5)) (PreH26 : (retval_5 <= 1)) (PreH27 : (retval_5 = 0)) (PreH28 : (X_non_alias <> 1)) (PreH29 : (X_non_alias < SM2_P_Z)) (PreH30 : (0 <= X_non_alias)) (PreH31 : (retval_5 = 0)) (PreH32 : (retval_6 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) = 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) = 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_12_7_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_5: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (retval_7: Z) (PreH1 : (0 <= retval_7)) (PreH2 : (retval_7 <= 1)) (PreH3 : (retval_7 = 0)) (PreH4 : ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) <> 1)) (PreH5 : (Y_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH6 : (x3_6 < U64_MOD)) (PreH7 : (0 <= x3_6)) (PreH8 : (x2_6 < U64_MOD)) (PreH9 : (0 <= x2_6)) (PreH10 : (x1_6 < U64_MOD)) (PreH11 : (0 <= x1_6)) (PreH12 : (x0_6 < U64_MOD)) (PreH13 : (0 <= x0_6)) (PreH14 : (X_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH15 : (x3_5 < U64_MOD)) (PreH16 : (0 <= x3_5)) (PreH17 : (x2_5 < U64_MOD)) (PreH18 : (0 <= x2_5)) (PreH19 : (x1_5 < U64_MOD)) (PreH20 : (0 <= x1_5)) (PreH21 : (x0_5 < U64_MOD)) (PreH22 : (0 <= x0_5)) (PreH23 : (Y_non_alias < SM2_P_Z)) (PreH24 : (0 <= Y_non_alias)) (PreH25 : (0 <= retval_5)) (PreH26 : (retval_5 <= 1)) (PreH27 : (retval_5 = 0)) (PreH28 : (X_non_alias <> 1)) (PreH29 : (X_non_alias < SM2_P_Z)) (PreH30 : (0 <= X_non_alias)) (PreH31 : (retval_5 = 0)) (PreH32 : (retval_7 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) = 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_6: Z) ,
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) = 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 <> 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_13_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1)) (PreH5 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_non_alias < SM2_P_Z)) (PreH24 : (0 <= Y_non_alias)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_non_alias <> 1)) (PreH29 : (X_non_alias < SM2_P_Z)) (PreH30 : (0 <= X_non_alias)) (PreH31 : (retval = 0)) (PreH32 : (retval_2 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (X_non_alias <> 1) ” 
  &&  “ (Y_non_alias = 1) ”
  &&  (store_fp x_pre X_non_alias )
  **  (store_fp y_pre Y_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_entail_wit_14_r_eq_x := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1)) (PreH5 : (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_x < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_x)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_x <> 1)) (PreH29 : (X_r_eq_x < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_x)) (PreH31 : (result_pre = x_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (limbs: (@list Z)) ,
  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (Y_r_eq_x = 1) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = X_r_eq_x) ”
  &&  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (store_fp y_pre Y_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 >= 0)) (PreH6 : (x1 >= 0)) (PreH7 : (x2 >= 0)) (PreH8 : (x3 >= 0)) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 1)) (PreH12 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1)) (PreH13 : (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (Y_r_eq_x < SM2_P_Z)) (PreH32 : (0 <= Y_r_eq_x)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (retval = 0)) (PreH36 : (X_r_eq_x <> 1)) (PreH37 : (X_r_eq_x < SM2_P_Z)) (PreH38 : (0 <= X_r_eq_x)) (PreH39 : (result_pre = x_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 <> 0)) ,
  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  EX (limbs: (@list Z)) ,
  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = Y_r_eq_x) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (Y_r_eq_x = 1) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = X_r_eq_x) ”
  &&  (StructPredu32 result_pre (make_record_u32 (limbs)) )
).

Definition mul_mod_p_entail_wit_15_r_eq_y := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1)) (PreH5 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_y < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_y)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_y <> 1)) (PreH29 : (X_r_eq_y < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_y)) (PreH31 : (result_pre = y_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (Y_r_eq_y = 1) ”
  &&  (store_fp x_pre X_r_eq_y )
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (y_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1)) (PreH5 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_y < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_y)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_y <> 1)) (PreH29 : (X_r_eq_y < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_y)) (PreH31 : (result_pre = y_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
|--
  (UndefStructPredu32 result_pre )
).

Definition mul_mod_p_entail_wit_15_r_eq_y_split_goal_spatial := 
forall (result_pre: Z) (y_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = 1)) (PreH5 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_y < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_y)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_y <> 1)) (PreH29 : (X_r_eq_y < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_y)) (PreH31 : (result_pre = y_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 <> 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
|--
  (UndefStructPredu32 result_pre )
.

Definition mul_mod_p_entail_wit_16_1_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (PreH1 : (result_pre = y_pre)) (PreH2 : (X_r_eq_y <> 1)) (PreH3 : (Y_r_eq_y = 1)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp x_pre X_r_eq_y )
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (Y_r_eq_y = 1) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (limbs: (@list Z)) ,
  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (Y_r_eq_x = 1) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = X_r_eq_x) ”
  &&  (store_u256 y_pre Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (Y_non_alias = 1) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_16_2_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (limbs: (@list Z)) (PreH1 : (result_pre = x_pre)) (PreH2 : (X_r_eq_x <> 1)) (PreH3 : (Y_r_eq_x = 1)) (PreH4 : (0 <= X_r_eq_x)) (PreH5 : (X_r_eq_x < SM2_P_Z)) (PreH6 : ((Zlength (limbs)) = 4)) (PreH7 : (u64_list_bounded limbs )) (PreH8 : ((u64_list_value (limbs)) = X_r_eq_x)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (store_fp y_pre Y_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (Y_r_eq_y = 1) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (Y_r_eq_x = 1) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = X_r_eq_x) ”
  &&  (store_u256 y_pre Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (Y_non_alias = 1) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_16_3_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (PreH1 : (X_non_alias <> 1)) (PreH2 : (Y_non_alias = 1)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp x_pre X_non_alias )
  **  (store_fp y_pre Y_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (Y_r_eq_y = 1) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (limbs: (@list Z)) ,
  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (Y_r_eq_x = 1) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = X_r_eq_x) ”
  &&  (store_u256 y_pre Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (Y_non_alias = 1) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_17_1_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (PreH1 : (X_r_eq_y < SM2_P_Z)) (PreH2 : (0 <= X_r_eq_y)) (PreH3 : (result_pre = y_pre)) (PreH4 : (X_r_eq_y <> 1)) (PreH5 : (Y_r_eq_y = 1)) ,
  (store_u256 x_pre X_r_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (Y_r_eq_y = 1) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (limbs: (@list Z)) ,
  “ (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (Y_r_eq_x = 1) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = X_r_eq_x) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (Y_non_alias = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_17_2_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (limbs: (@list Z)) (PreH1 : (Y_r_eq_x < SM2_P_Z)) (PreH2 : (0 <= Y_r_eq_x)) (PreH3 : (result_pre = x_pre)) (PreH4 : (X_r_eq_x <> 1)) (PreH5 : (Y_r_eq_x = 1)) (PreH6 : (0 <= X_r_eq_x)) (PreH7 : (X_r_eq_x < SM2_P_Z)) (PreH8 : ((Zlength (limbs)) = 4)) (PreH9 : (u64_list_bounded limbs )) (PreH10 : ((u64_list_value (limbs)) = X_r_eq_x)) ,
  (store_u256 y_pre Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (Y_r_eq_y = 1) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (Y_r_eq_x = 1) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = X_r_eq_x) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (Y_non_alias = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_17_3_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (PreH1 : (Y_non_alias < SM2_P_Z)) (PreH2 : (0 <= Y_non_alias)) (PreH3 : (X_non_alias < SM2_P_Z)) (PreH4 : (0 <= X_non_alias)) (PreH5 : (X_non_alias <> 1)) (PreH6 : (Y_non_alias = 1)) ,
  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (Y_r_eq_y = 1) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (limbs: (@list Z)) ,
  “ (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (Y_r_eq_x = 1) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = X_r_eq_x) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (Y_non_alias = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition mul_mod_p_entail_wit_18_1_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (K: Z) (Zout: Z) (PreH1 : (0 <= Zout)) (PreH2 : (Zout < SM2_P_Z)) (PreH3 : ((X_r_eq_y * Y_r_eq_y ) = (Zout + (K * SM2_P_Z ) ))) (PreH4 : (0 <= (X_r_eq_y * Y_r_eq_y ))) (PreH5 : ((X_r_eq_y * Y_r_eq_y ) < U512_MOD)) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1)) (PreH8 : (retval_2 = 0)) (PreH9 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH10 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) (PreH28 : (Y_r_eq_y < SM2_P_Z)) (PreH29 : (0 <= Y_r_eq_y)) (PreH30 : (0 <= retval)) (PreH31 : (retval <= 1)) (PreH32 : (retval = 0)) (PreH33 : (X_r_eq_y <> 1)) (PreH34 : (X_r_eq_y < SM2_P_Z)) (PreH35 : (0 <= X_r_eq_y)) (PreH36 : (result_pre = y_pre)) (PreH37 : (retval = 0)) (PreH38 : (retval_2 = 0)) ,
  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_y * Y_r_eq_y ) )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (xs: (@list Z)) ,
  “ ((u64_list_value (xs)) = (X_r_eq_y * Y_r_eq_y )) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 8) ” 
  &&  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((X_r_eq_y * Y_r_eq_y ) = (Zout + (K * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_r_eq_y * Y_r_eq_y )) ” 
  &&  “ ((X_r_eq_y * Y_r_eq_y ) < U512_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (xs_2: (@list Z))  (K_2: Z)  (Zout_2: Z)  (retval_3: Z)  (x0_3: Z)  (x1_3: Z)  (x2_3: Z)  (x3_3: Z)  (x0_4: Z)  (x1_4: Z)  (x2_4: Z)  (x3_4: Z)  (retval_4: Z) ,
  “ ((u64_list_value (xs_2)) = (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ (u64_list_bounded xs_2 ) ” 
  &&  “ ((Zlength (xs_2)) = 8) ” 
  &&  “ (0 <= Zout_2) ” 
  &&  “ (Zout_2 < SM2_P_Z) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) = (Zout_2 + (K_2 * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < U512_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) <> 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs_2 )
  **  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (xs_3: (@list Z))  (K_3: Z)  (Zout_3: Z)  (retval_5: Z)  (x0_5: Z)  (x1_5: Z)  (x2_5: Z)  (x3_5: Z)  (retval_6: Z) ,
  “ ((u64_list_value (xs_3)) = (X_x_eq_y * X_x_eq_y )) ” 
  &&  “ (u64_list_bounded xs_3 ) ” 
  &&  “ ((Zlength (xs_3)) = 8) ” 
  &&  “ (0 <= Zout_3) ” 
  &&  “ (Zout_3 < SM2_P_Z) ” 
  &&  “ ((X_x_eq_y * X_x_eq_y ) = (Zout_3 + (K_3 * SM2_P_Z ) )) ” 
  &&  “ ((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) ” 
  &&  “ (0 <= (X_x_eq_y * X_x_eq_y )) ” 
  &&  “ ((X_x_eq_y * X_x_eq_y ) < U512_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) <> 1) ” 
  &&  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs_3 )
  **  (store_fp result_pre Zout_3 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_x_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (xs_4: (@list Z))  (K_4: Z)  (Zout_4: Z)  (retval_7: Z)  (x0_6: Z)  (x1_6: Z)  (x2_6: Z)  (x3_6: Z)  (x0_7: Z)  (x1_7: Z)  (x2_7: Z)  (x3_7: Z)  (retval_8: Z) ,
  “ ((u64_list_value (xs_4)) = (X_non_alias * Y_non_alias )) ” 
  &&  “ (u64_list_bounded xs_4 ) ” 
  &&  “ ((Zlength (xs_4)) = 8) ” 
  &&  “ (0 <= Zout_4) ” 
  &&  “ (Zout_4 < SM2_P_Z) ” 
  &&  “ ((X_non_alias * Y_non_alias ) = (Zout_4 + (K_4 * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < U512_MOD) ” 
  &&  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <> 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs_4 )
  **  (store_fp result_pre Zout_4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition mul_mod_p_entail_wit_18_2_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_3: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_4: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (0 <= Zout_2)) (PreH2 : (Zout_2 < SM2_P_Z)) (PreH3 : ((X_r_eq_x * Y_r_eq_x ) = (Zout_2 + (K_2 * SM2_P_Z ) ))) (PreH4 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH5 : ((X_r_eq_x * Y_r_eq_x ) < U512_MOD)) (PreH6 : (0 <= retval_4)) (PreH7 : (retval_4 <= 1)) (PreH8 : (retval_4 = 0)) (PreH9 : ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) <> 1)) (PreH10 : (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH11 : (x3_4 < U64_MOD)) (PreH12 : (0 <= x3_4)) (PreH13 : (x2_4 < U64_MOD)) (PreH14 : (0 <= x2_4)) (PreH15 : (x1_4 < U64_MOD)) (PreH16 : (0 <= x1_4)) (PreH17 : (x0_4 < U64_MOD)) (PreH18 : (0 <= x0_4)) (PreH19 : (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH20 : (x3_3 < U64_MOD)) (PreH21 : (0 <= x3_3)) (PreH22 : (x2_3 < U64_MOD)) (PreH23 : (0 <= x2_3)) (PreH24 : (x1_3 < U64_MOD)) (PreH25 : (0 <= x1_3)) (PreH26 : (x0_3 < U64_MOD)) (PreH27 : (0 <= x0_3)) (PreH28 : (Y_r_eq_x < SM2_P_Z)) (PreH29 : (0 <= Y_r_eq_x)) (PreH30 : (0 <= retval_3)) (PreH31 : (retval_3 <= 1)) (PreH32 : (retval_3 = 0)) (PreH33 : (X_r_eq_x <> 1)) (PreH34 : (X_r_eq_x < SM2_P_Z)) (PreH35 : (0 <= X_r_eq_x)) (PreH36 : (result_pre = x_pre)) (PreH37 : (retval_3 = 0)) (PreH38 : (retval_4 = 0)) ,
  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * Y_r_eq_x ) )
  **  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (xs: (@list Z))  (K: Z)  (Zout: Z)  (retval: Z)  (x0: Z)  (x1: Z)  (x2: Z)  (x3: Z)  (x0_2: Z)  (x1_2: Z)  (x2_2: Z)  (x3_2: Z)  (retval_2: Z) ,
  “ ((u64_list_value (xs)) = (X_r_eq_y * Y_r_eq_y )) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 8) ” 
  &&  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((X_r_eq_y * Y_r_eq_y ) = (Zout + (K * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_r_eq_y * Y_r_eq_y )) ” 
  &&  “ ((X_r_eq_y * Y_r_eq_y ) < U512_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (xs_2: (@list Z)) ,
  “ ((u64_list_value (xs_2)) = (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ (u64_list_bounded xs_2 ) ” 
  &&  “ ((Zlength (xs_2)) = 8) ” 
  &&  “ (0 <= Zout_2) ” 
  &&  “ (Zout_2 < SM2_P_Z) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) = (Zout_2 + (K_2 * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < U512_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) <> 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs_2 )
  **  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (xs_3: (@list Z))  (K_3: Z)  (Zout_3: Z)  (retval_5: Z)  (x0_5: Z)  (x1_5: Z)  (x2_5: Z)  (x3_5: Z)  (retval_6: Z) ,
  “ ((u64_list_value (xs_3)) = (X_x_eq_y * X_x_eq_y )) ” 
  &&  “ (u64_list_bounded xs_3 ) ” 
  &&  “ ((Zlength (xs_3)) = 8) ” 
  &&  “ (0 <= Zout_3) ” 
  &&  “ (Zout_3 < SM2_P_Z) ” 
  &&  “ ((X_x_eq_y * X_x_eq_y ) = (Zout_3 + (K_3 * SM2_P_Z ) )) ” 
  &&  “ ((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) ” 
  &&  “ (0 <= (X_x_eq_y * X_x_eq_y )) ” 
  &&  “ ((X_x_eq_y * X_x_eq_y ) < U512_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) <> 1) ” 
  &&  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs_3 )
  **  (store_fp result_pre Zout_3 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_x_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (xs_4: (@list Z))  (K_4: Z)  (Zout_4: Z)  (retval_7: Z)  (x0_6: Z)  (x1_6: Z)  (x2_6: Z)  (x3_6: Z)  (x0_7: Z)  (x1_7: Z)  (x2_7: Z)  (x3_7: Z)  (retval_8: Z) ,
  “ ((u64_list_value (xs_4)) = (X_non_alias * Y_non_alias )) ” 
  &&  “ (u64_list_bounded xs_4 ) ” 
  &&  “ ((Zlength (xs_4)) = 8) ” 
  &&  “ (0 <= Zout_4) ” 
  &&  “ (Zout_4 < SM2_P_Z) ” 
  &&  “ ((X_non_alias * Y_non_alias ) = (Zout_4 + (K_4 * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < U512_MOD) ” 
  &&  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <> 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs_4 )
  **  (store_fp result_pre Zout_4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition mul_mod_p_entail_wit_18_3_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_5: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (retval_6: Z) (K_3: Z) (Zout_3: Z) (PreH1 : (0 <= Zout_3)) (PreH2 : (Zout_3 < SM2_P_Z)) (PreH3 : ((X_x_eq_y * X_x_eq_y ) = (Zout_3 + (K_3 * SM2_P_Z ) ))) (PreH4 : ((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))) (PreH5 : (0 <= (X_x_eq_y * X_x_eq_y ))) (PreH6 : ((X_x_eq_y * X_x_eq_y ) < U512_MOD)) (PreH7 : (0 <= retval_6)) (PreH8 : (retval_6 <= 1)) (PreH9 : (retval_6 = 0)) (PreH10 : ((u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) <> 1)) (PreH11 : (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH12 : (x3_5 < U64_MOD)) (PreH13 : (0 <= x3_5)) (PreH14 : (x2_5 < U64_MOD)) (PreH15 : (0 <= x2_5)) (PreH16 : (x1_5 < U64_MOD)) (PreH17 : (0 <= x1_5)) (PreH18 : (x0_5 < U64_MOD)) (PreH19 : (0 <= x0_5)) (PreH20 : (0 <= retval_5)) (PreH21 : (retval_5 <= 1)) (PreH22 : (retval_5 = 0)) (PreH23 : (X_x_eq_y <> 1)) (PreH24 : (X_x_eq_y < SM2_P_Z)) (PreH25 : (0 <= X_x_eq_y)) (PreH26 : (x_pre = y_pre)) (PreH27 : (retval_5 = 0)) (PreH28 : (retval_6 = 0)) ,
  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_x_eq_y * X_x_eq_y ) )
  **  (store_fp result_pre Zout_3 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_x_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (xs: (@list Z))  (K: Z)  (Zout: Z)  (retval: Z)  (x0: Z)  (x1: Z)  (x2: Z)  (x3: Z)  (x0_2: Z)  (x1_2: Z)  (x2_2: Z)  (x3_2: Z)  (retval_2: Z) ,
  “ ((u64_list_value (xs)) = (X_r_eq_y * Y_r_eq_y )) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 8) ” 
  &&  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((X_r_eq_y * Y_r_eq_y ) = (Zout + (K * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_r_eq_y * Y_r_eq_y )) ” 
  &&  “ ((X_r_eq_y * Y_r_eq_y ) < U512_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (xs_2: (@list Z))  (K_2: Z)  (Zout_2: Z)  (retval_3: Z)  (x0_3: Z)  (x1_3: Z)  (x2_3: Z)  (x3_3: Z)  (x0_4: Z)  (x1_4: Z)  (x2_4: Z)  (x3_4: Z)  (retval_4: Z) ,
  “ ((u64_list_value (xs_2)) = (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ (u64_list_bounded xs_2 ) ” 
  &&  “ ((Zlength (xs_2)) = 8) ” 
  &&  “ (0 <= Zout_2) ” 
  &&  “ (Zout_2 < SM2_P_Z) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) = (Zout_2 + (K_2 * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < U512_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) <> 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs_2 )
  **  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (xs_3: (@list Z)) ,
  “ ((u64_list_value (xs_3)) = (X_x_eq_y * X_x_eq_y )) ” 
  &&  “ (u64_list_bounded xs_3 ) ” 
  &&  “ ((Zlength (xs_3)) = 8) ” 
  &&  “ (0 <= Zout_3) ” 
  &&  “ (Zout_3 < SM2_P_Z) ” 
  &&  “ ((X_x_eq_y * X_x_eq_y ) = (Zout_3 + (K_3 * SM2_P_Z ) )) ” 
  &&  “ ((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) ” 
  &&  “ (0 <= (X_x_eq_y * X_x_eq_y )) ” 
  &&  “ ((X_x_eq_y * X_x_eq_y ) < U512_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) <> 1) ” 
  &&  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs_3 )
  **  (store_fp result_pre Zout_3 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_x_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (xs_4: (@list Z))  (K_4: Z)  (Zout_4: Z)  (retval_7: Z)  (x0_6: Z)  (x1_6: Z)  (x2_6: Z)  (x3_6: Z)  (x0_7: Z)  (x1_7: Z)  (x2_7: Z)  (x3_7: Z)  (retval_8: Z) ,
  “ ((u64_list_value (xs_4)) = (X_non_alias * Y_non_alias )) ” 
  &&  “ (u64_list_bounded xs_4 ) ” 
  &&  “ ((Zlength (xs_4)) = 8) ” 
  &&  “ (0 <= Zout_4) ” 
  &&  “ (Zout_4 < SM2_P_Z) ” 
  &&  “ ((X_non_alias * Y_non_alias ) = (Zout_4 + (K_4 * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < U512_MOD) ” 
  &&  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <> 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs_4 )
  **  (store_fp result_pre Zout_4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition mul_mod_p_entail_wit_18_4_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (X_x_eq_y: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval_7: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (x0_7: Z) (x1_7: Z) (x2_7: Z) (x3_7: Z) (retval_8: Z) (K_4: Z) (Zout_4: Z) (PreH1 : (0 <= Zout_4)) (PreH2 : (Zout_4 < SM2_P_Z)) (PreH3 : ((X_non_alias * Y_non_alias ) = (Zout_4 + (K_4 * SM2_P_Z ) ))) (PreH4 : (0 <= (X_non_alias * Y_non_alias ))) (PreH5 : ((X_non_alias * Y_non_alias ) < U512_MOD)) (PreH6 : (0 <= retval_8)) (PreH7 : (retval_8 <= 1)) (PreH8 : (retval_8 = 0)) (PreH9 : ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <> 1)) (PreH10 : (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)))) (PreH11 : (x3_7 < U64_MOD)) (PreH12 : (0 <= x3_7)) (PreH13 : (x2_7 < U64_MOD)) (PreH14 : (0 <= x2_7)) (PreH15 : (x1_7 < U64_MOD)) (PreH16 : (0 <= x1_7)) (PreH17 : (x0_7 < U64_MOD)) (PreH18 : (0 <= x0_7)) (PreH19 : (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH20 : (x3_6 < U64_MOD)) (PreH21 : (0 <= x3_6)) (PreH22 : (x2_6 < U64_MOD)) (PreH23 : (0 <= x2_6)) (PreH24 : (x1_6 < U64_MOD)) (PreH25 : (0 <= x1_6)) (PreH26 : (x0_6 < U64_MOD)) (PreH27 : (0 <= x0_6)) (PreH28 : (Y_non_alias < SM2_P_Z)) (PreH29 : (0 <= Y_non_alias)) (PreH30 : (0 <= retval_7)) (PreH31 : (retval_7 <= 1)) (PreH32 : (retval_7 = 0)) (PreH33 : (X_non_alias <> 1)) (PreH34 : (X_non_alias < SM2_P_Z)) (PreH35 : (0 <= X_non_alias)) (PreH36 : (retval_7 = 0)) (PreH37 : (retval_8 = 0)) ,
  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * Y_non_alias ) )
  **  (store_fp result_pre Zout_4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (xs: (@list Z))  (K: Z)  (Zout: Z)  (retval: Z)  (x0: Z)  (x1: Z)  (x2: Z)  (x3: Z)  (x0_2: Z)  (x1_2: Z)  (x2_2: Z)  (x3_2: Z)  (retval_2: Z) ,
  “ ((u64_list_value (xs)) = (X_r_eq_y * Y_r_eq_y )) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 8) ” 
  &&  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((X_r_eq_y * Y_r_eq_y ) = (Zout + (K * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_r_eq_y * Y_r_eq_y )) ” 
  &&  “ ((X_r_eq_y * Y_r_eq_y ) < U512_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (xs_2: (@list Z))  (K_2: Z)  (Zout_2: Z)  (retval_3: Z)  (x0_3: Z)  (x1_3: Z)  (x2_3: Z)  (x3_3: Z)  (x0_4: Z)  (x1_4: Z)  (x2_4: Z)  (x3_4: Z)  (retval_4: Z) ,
  “ ((u64_list_value (xs_2)) = (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ (u64_list_bounded xs_2 ) ” 
  &&  “ ((Zlength (xs_2)) = 8) ” 
  &&  “ (0 <= Zout_2) ” 
  &&  “ (Zout_2 < SM2_P_Z) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) = (Zout_2 + (K_2 * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < U512_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) <> 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs_2 )
  **  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (xs_3: (@list Z))  (K_3: Z)  (Zout_3: Z)  (retval_5: Z)  (x0_5: Z)  (x1_5: Z)  (x2_5: Z)  (x3_5: Z)  (retval_6: Z) ,
  “ ((u64_list_value (xs_3)) = (X_x_eq_y * X_x_eq_y )) ” 
  &&  “ (u64_list_bounded xs_3 ) ” 
  &&  “ ((Zlength (xs_3)) = 8) ” 
  &&  “ (0 <= Zout_3) ” 
  &&  “ (Zout_3 < SM2_P_Z) ” 
  &&  “ ((X_x_eq_y * X_x_eq_y ) = (Zout_3 + (K_3 * SM2_P_Z ) )) ” 
  &&  “ ((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) ” 
  &&  “ (0 <= (X_x_eq_y * X_x_eq_y )) ” 
  &&  “ ((X_x_eq_y * X_x_eq_y ) < U512_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)) <> 1) ” 
  &&  “ (X_x_eq_y = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (retval_6 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs_3 )
  **  (store_fp result_pre Zout_3 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_x_eq_y )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (xs_4: (@list Z)) ,
  “ ((u64_list_value (xs_4)) = (X_non_alias * Y_non_alias )) ” 
  &&  “ (u64_list_bounded xs_4 ) ” 
  &&  “ ((Zlength (xs_4)) = 8) ” 
  &&  “ (0 <= Zout_4) ” 
  &&  “ (Zout_4 < SM2_P_Z) ” 
  &&  “ ((X_non_alias * Y_non_alias ) = (Zout_4 + (K_4 * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < U512_MOD) ” 
  &&  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <> 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs_4 )
  **  (store_fp result_pre Zout_4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition mul_mod_p_return_wit_1_non_alias := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_P_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias <> 1)) (PreH24 : (Y_non_alias = 1)) ,
  (UInt64Array.full &((result_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((x_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_fp x_pre X_non_alias )
  **  (store_fp y_pre Y_non_alias )
  **  (store_fp result_pre (Zmod ((X_non_alias * Y_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_P_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias <> 1)) (PreH24 : (Y_non_alias = 1)) ,
  TT && emp 
|--
  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = X_non_alias) ” 
  &&  “ (0 <= (Zmod ((X_non_alias * 1 )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((X_non_alias * 1 )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = (Zmod ((X_non_alias * 1 )) (SM2_P_Z))) ”
  &&  emp
).

Definition mul_mod_p_return_wit_1_non_alias_split_goal_1 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_P_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias <> 1)) (PreH24 : (Y_non_alias = 1)) ,
  ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = X_non_alias)
.

Definition mul_mod_p_return_wit_1_non_alias_split_goal_2 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_P_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias <> 1)) (PreH24 : (Y_non_alias = 1)) ,
  (0 <= (Zmod ((X_non_alias * 1 )) (SM2_P_Z)))
.

Definition mul_mod_p_return_wit_1_non_alias_split_goal_3 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_P_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias <> 1)) (PreH24 : (Y_non_alias = 1)) ,
  ((Zmod ((X_non_alias * 1 )) (SM2_P_Z)) < SM2_P_Z)
.

Definition mul_mod_p_return_wit_1_non_alias_split_goal_4 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_P_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias <> 1)) (PreH24 : (Y_non_alias = 1)) ,
  ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = (Zmod ((X_non_alias * 1 )) (SM2_P_Z)))
.

Definition mul_mod_p_return_wit_2_r_eq_x := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (limbs: (@list Z)) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (Y_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (Y_r_eq_x < SM2_P_Z)) (PreH11 : (0 <= Y_r_eq_x)) (PreH12 : (result_pre = x_pre)) (PreH13 : (X_r_eq_x <> 1)) (PreH14 : (Y_r_eq_x = 1)) (PreH15 : (0 <= X_r_eq_x)) (PreH16 : (X_r_eq_x < SM2_P_Z)) (PreH17 : ((Zlength (limbs)) = 4)) (PreH18 : (u64_list_bounded limbs )) (PreH19 : ((u64_list_value (limbs)) = X_r_eq_x)) ,
  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = x_pre) ”
  &&  (store_fp result_pre (Zmod ((X_r_eq_x * Y_r_eq_x )) (SM2_P_Z)) )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (limbs: (@list Z)) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (Y_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (Y_r_eq_x < SM2_P_Z)) (PreH11 : (0 <= Y_r_eq_x)) (PreH12 : (result_pre = x_pre)) (PreH13 : (X_r_eq_x <> 1)) (PreH14 : (Y_r_eq_x = 1)) (PreH15 : (0 <= X_r_eq_x)) (PreH16 : (X_r_eq_x < SM2_P_Z)) (PreH17 : ((Zlength (limbs)) = 4)) (PreH18 : (u64_list_bounded limbs )) (PreH19 : ((u64_list_value (limbs)) = X_r_eq_x)) ,
  (StructPredu32 result_pre (make_record_u32 (limbs)) )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (Y_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ ((Zmod ((X_r_eq_x * Y_r_eq_x )) (SM2_P_Z)) = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((Zmod ((X_r_eq_x * Y_r_eq_x )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod ((X_r_eq_x * Y_r_eq_x )) (SM2_P_Z))) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
).

Definition mul_mod_p_return_wit_3_r_eq_y := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_r_eq_y < SM2_P_Z)) (PreH11 : (0 <= X_r_eq_y)) (PreH12 : (result_pre = y_pre)) (PreH13 : (X_r_eq_y <> 1)) (PreH14 : (Y_r_eq_y = 1)) ,
  (UInt64Array.full &((result_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((x_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = y_pre) ”
  &&  (store_fp x_pre X_r_eq_y )
  **  (store_fp result_pre (Zmod ((X_r_eq_y * Y_r_eq_y )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (y_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_r_eq_y < SM2_P_Z)) (PreH11 : (0 <= X_r_eq_y)) (PreH12 : (result_pre = y_pre)) (PreH13 : (X_r_eq_y <> 1)) (PreH14 : (Y_r_eq_y = 1)) ,
  TT && emp 
|--
  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = X_r_eq_y) ” 
  &&  “ (0 <= (Zmod ((X_r_eq_y * 1 )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((X_r_eq_y * 1 )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = (Zmod ((X_r_eq_y * 1 )) (SM2_P_Z))) ”
  &&  emp
).

Definition mul_mod_p_return_wit_3_r_eq_y_split_goal_1 := 
forall (result_pre: Z) (y_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_r_eq_y < SM2_P_Z)) (PreH11 : (0 <= X_r_eq_y)) (PreH12 : (result_pre = y_pre)) (PreH13 : (X_r_eq_y <> 1)) (PreH14 : (Y_r_eq_y = 1)) ,
  ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = X_r_eq_y)
.

Definition mul_mod_p_return_wit_3_r_eq_y_split_goal_2 := 
forall (result_pre: Z) (y_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_r_eq_y < SM2_P_Z)) (PreH11 : (0 <= X_r_eq_y)) (PreH12 : (result_pre = y_pre)) (PreH13 : (X_r_eq_y <> 1)) (PreH14 : (Y_r_eq_y = 1)) ,
  (0 <= (Zmod ((X_r_eq_y * 1 )) (SM2_P_Z)))
.

Definition mul_mod_p_return_wit_3_r_eq_y_split_goal_3 := 
forall (result_pre: Z) (y_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_r_eq_y < SM2_P_Z)) (PreH11 : (0 <= X_r_eq_y)) (PreH12 : (result_pre = y_pre)) (PreH13 : (X_r_eq_y <> 1)) (PreH14 : (Y_r_eq_y = 1)) ,
  ((Zmod ((X_r_eq_y * 1 )) (SM2_P_Z)) < SM2_P_Z)
.

Definition mul_mod_p_return_wit_3_r_eq_y_split_goal_4 := 
forall (result_pre: Z) (y_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_r_eq_y < SM2_P_Z)) (PreH11 : (0 <= X_r_eq_y)) (PreH12 : (result_pre = y_pre)) (PreH13 : (X_r_eq_y <> 1)) (PreH14 : (Y_r_eq_y = 1)) ,
  ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = (Zmod ((X_r_eq_y * 1 )) (SM2_P_Z)))
.

Definition mul_mod_p_return_wit_4_non_alias := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_P_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias = 1)) ,
  (UInt64Array.full &((result_pre)  # "u32" ->ₛ "v") 4 (cons (x0_2) ((cons (x1_2) ((cons (x2_2) ((cons (x3_2) ((@nil Z))))))))) )
  **  (UInt64Array.full &((y_pre)  # "u32" ->ₛ "v") 4 (cons (x0_2) ((cons (x1_2) ((cons (x2_2) ((cons (x3_2) ((@nil Z))))))))) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_fp x_pre X_non_alias )
  **  (store_fp y_pre Y_non_alias )
  **  (store_fp result_pre (Zmod ((X_non_alias * Y_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_P_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias = 1)) ,
  TT && emp 
|--
  “ ((u64_list_value ((cons (x0_2) ((cons (x1_2) ((cons (x2_2) ((cons (x3_2) ((@nil Z))))))))))) = Y_non_alias) ” 
  &&  “ (0 <= (Zmod ((1 * Y_non_alias )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((1 * Y_non_alias )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ ((u64_list_value ((cons (x0_2) ((cons (x1_2) ((cons (x2_2) ((cons (x3_2) ((@nil Z))))))))))) = (Zmod ((1 * Y_non_alias )) (SM2_P_Z))) ”
  &&  emp
).

Definition mul_mod_p_return_wit_4_non_alias_split_goal_1 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_P_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias = 1)) ,
  ((u64_list_value ((cons (x0_2) ((cons (x1_2) ((cons (x2_2) ((cons (x3_2) ((@nil Z))))))))))) = Y_non_alias)
.

Definition mul_mod_p_return_wit_4_non_alias_split_goal_2 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_P_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias = 1)) ,
  (0 <= (Zmod ((1 * Y_non_alias )) (SM2_P_Z)))
.

Definition mul_mod_p_return_wit_4_non_alias_split_goal_3 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_P_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias = 1)) ,
  ((Zmod ((1 * Y_non_alias )) (SM2_P_Z)) < SM2_P_Z)
.

Definition mul_mod_p_return_wit_4_non_alias_split_goal_4 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_P_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias = 1)) ,
  ((u64_list_value ((cons (x0_2) ((cons (x1_2) ((cons (x2_2) ((cons (x3_2) ((@nil Z))))))))))) = (Zmod ((1 * Y_non_alias )) (SM2_P_Z)))
.

Definition mul_mod_p_return_wit_5_x_eq_y := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_x_eq_y < SM2_P_Z)) (PreH11 : (0 <= X_x_eq_y)) (PreH12 : (x_pre = y_pre)) (PreH13 : (X_x_eq_y = 1)) ,
  (UInt64Array.full &((result_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((y_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (x_pre = y_pre) ”
  &&  (store_fp x_pre X_x_eq_y )
  **  (store_fp result_pre (Zmod ((X_x_eq_y * X_x_eq_y )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_x_eq_y < SM2_P_Z)) (PreH11 : (0 <= X_x_eq_y)) (PreH12 : (x_pre = y_pre)) (PreH13 : (X_x_eq_y = 1)) ,
  (UInt64Array.full &((y_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = (Zmod ((X_x_eq_y * X_x_eq_y )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((X_x_eq_y * X_x_eq_y )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod ((X_x_eq_y * X_x_eq_y )) (SM2_P_Z))) ” 
  &&  “ (X_x_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
).

Definition mul_mod_p_return_wit_6_r_eq_x := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (Y_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (Y_r_eq_x < SM2_P_Z)) (PreH11 : (0 <= Y_r_eq_x)) (PreH12 : (result_pre = x_pre)) (PreH13 : (X_r_eq_x = 1)) ,
  (UInt64Array.full &((result_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((y_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = x_pre) ”
  &&  (store_fp result_pre (Zmod ((X_r_eq_x * Y_r_eq_x )) (SM2_P_Z)) )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (Y_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (Y_r_eq_x < SM2_P_Z)) (PreH11 : (0 <= Y_r_eq_x)) (PreH12 : (result_pre = x_pre)) (PreH13 : (X_r_eq_x = 1)) ,
  TT && emp 
|--
  “ (0 <= (Zmod ((1 * Y_r_eq_x )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((1 * Y_r_eq_x )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = (Zmod ((1 * Y_r_eq_x )) (SM2_P_Z))) ” 
  &&  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = Y_r_eq_x) ”
  &&  emp
).

Definition mul_mod_p_return_wit_6_r_eq_x_split_goal_1 := 
forall (result_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (Y_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (Y_r_eq_x < SM2_P_Z)) (PreH11 : (0 <= Y_r_eq_x)) (PreH12 : (result_pre = x_pre)) (PreH13 : (X_r_eq_x = 1)) ,
  (0 <= (Zmod ((1 * Y_r_eq_x )) (SM2_P_Z)))
.

Definition mul_mod_p_return_wit_6_r_eq_x_split_goal_2 := 
forall (result_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (Y_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (Y_r_eq_x < SM2_P_Z)) (PreH11 : (0 <= Y_r_eq_x)) (PreH12 : (result_pre = x_pre)) (PreH13 : (X_r_eq_x = 1)) ,
  ((Zmod ((1 * Y_r_eq_x )) (SM2_P_Z)) < SM2_P_Z)
.

Definition mul_mod_p_return_wit_6_r_eq_x_split_goal_3 := 
forall (result_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (Y_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (Y_r_eq_x < SM2_P_Z)) (PreH11 : (0 <= Y_r_eq_x)) (PreH12 : (result_pre = x_pre)) (PreH13 : (X_r_eq_x = 1)) ,
  ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = (Zmod ((1 * Y_r_eq_x )) (SM2_P_Z)))
.

Definition mul_mod_p_return_wit_6_r_eq_x_split_goal_4 := 
forall (result_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (Y_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (Y_r_eq_x < SM2_P_Z)) (PreH11 : (0 <= Y_r_eq_x)) (PreH12 : (result_pre = x_pre)) (PreH13 : (X_r_eq_x = 1)) ,
  ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = Y_r_eq_x)
.

Definition mul_mod_p_return_wit_7_r_eq_y := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (limbs: (@list Z)) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_r_eq_y < SM2_P_Z)) (PreH11 : (0 <= X_r_eq_y)) (PreH12 : (result_pre = y_pre)) (PreH13 : (X_r_eq_y = 1)) (PreH14 : (0 <= Y_r_eq_y)) (PreH15 : (Y_r_eq_y < SM2_P_Z)) (PreH16 : ((Zlength (limbs)) = 4)) (PreH17 : (u64_list_bounded limbs )) (PreH18 : ((u64_list_value (limbs)) = Y_r_eq_y)) ,
  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (StructPredu32 result_pre (make_record_u32 (limbs)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = y_pre) ”
  &&  (store_fp x_pre X_r_eq_y )
  **  (store_fp result_pre (Zmod ((X_r_eq_y * Y_r_eq_y )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (y_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (limbs: (@list Z)) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_r_eq_y < SM2_P_Z)) (PreH11 : (0 <= X_r_eq_y)) (PreH12 : (result_pre = y_pre)) (PreH13 : (X_r_eq_y = 1)) (PreH14 : (0 <= Y_r_eq_y)) (PreH15 : (Y_r_eq_y < SM2_P_Z)) (PreH16 : ((Zlength (limbs)) = 4)) (PreH17 : (u64_list_bounded limbs )) (PreH18 : ((u64_list_value (limbs)) = Y_r_eq_y)) ,
  (StructPredu32 result_pre (make_record_u32 (limbs)) )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ ((Zmod ((X_r_eq_y * Y_r_eq_y )) (SM2_P_Z)) = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((Zmod ((X_r_eq_y * Y_r_eq_y )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod ((X_r_eq_y * Y_r_eq_y )) (SM2_P_Z))) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
).

Definition mul_mod_p_return_wit_8_r_eq_y := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (K: Z) (Zout: Z) (xs: (@list Z)) (PreH1 : ((u64_list_value (xs)) = (X_r_eq_y * Y_r_eq_y ))) (PreH2 : (u64_list_bounded xs )) (PreH3 : ((Zlength (xs)) = 8)) (PreH4 : (0 <= Zout)) (PreH5 : (Zout < SM2_P_Z)) (PreH6 : ((X_r_eq_y * Y_r_eq_y ) = (Zout + (K * SM2_P_Z ) ))) (PreH7 : (0 <= (X_r_eq_y * Y_r_eq_y ))) (PreH8 : ((X_r_eq_y * Y_r_eq_y ) < U512_MOD)) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH13 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (Y_r_eq_y < SM2_P_Z)) (PreH32 : (0 <= Y_r_eq_y)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (retval = 0)) (PreH36 : (X_r_eq_y <> 1)) (PreH37 : (X_r_eq_y < SM2_P_Z)) (PreH38 : (0 <= X_r_eq_y)) (PreH39 : (result_pre = y_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) ,
  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_y )
|--
  “ (result_pre = y_pre) ”
  &&  (store_fp x_pre X_r_eq_y )
  **  (store_fp result_pre (Zmod ((X_r_eq_y * Y_r_eq_y )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (K: Z) (Zout: Z) (xs: (@list Z)) (PreH1 : ((u64_list_value (xs)) = (X_r_eq_y * Y_r_eq_y ))) (PreH2 : (u64_list_bounded xs )) (PreH3 : ((Zlength (xs)) = 8)) (PreH4 : (0 <= Zout)) (PreH5 : (Zout < SM2_P_Z)) (PreH6 : ((X_r_eq_y * Y_r_eq_y ) = (Zout + (K * SM2_P_Z ) ))) (PreH7 : (0 <= (X_r_eq_y * Y_r_eq_y ))) (PreH8 : ((X_r_eq_y * Y_r_eq_y ) < U512_MOD)) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH13 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (Y_r_eq_y < SM2_P_Z)) (PreH32 : (0 <= Y_r_eq_y)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (retval = 0)) (PreH36 : (X_r_eq_y <> 1)) (PreH37 : (X_r_eq_y < SM2_P_Z)) (PreH38 : (0 <= X_r_eq_y)) (PreH39 : (result_pre = y_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_y )
|--
  EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (X_r_eq_y = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (Zout = (Zmod ((X_r_eq_y * Y_r_eq_y )) (SM2_P_Z))) ” 
  &&  “ (result_pre = y_pre) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
).

Definition mul_mod_p_return_wit_9_r_eq_x := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (K: Z) (Zout: Z) (xs: (@list Z)) (PreH1 : ((u64_list_value (xs)) = (X_r_eq_x * Y_r_eq_x ))) (PreH2 : (u64_list_bounded xs )) (PreH3 : ((Zlength (xs)) = 8)) (PreH4 : (0 <= Zout)) (PreH5 : (Zout < SM2_P_Z)) (PreH6 : ((X_r_eq_x * Y_r_eq_x ) = (Zout + (K * SM2_P_Z ) ))) (PreH7 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH8 : ((X_r_eq_x * Y_r_eq_x ) < U512_MOD)) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH13 : (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (Y_r_eq_x < SM2_P_Z)) (PreH32 : (0 <= Y_r_eq_x)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (retval = 0)) (PreH36 : (X_r_eq_x <> 1)) (PreH37 : (X_r_eq_x < SM2_P_Z)) (PreH38 : (0 <= X_r_eq_x)) (PreH39 : (result_pre = x_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) ,
  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
|--
  “ (result_pre = x_pre) ”
  &&  (store_fp result_pre (Zmod ((X_r_eq_x * Y_r_eq_x )) (SM2_P_Z)) )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (K: Z) (Zout: Z) (xs: (@list Z)) (PreH1 : ((u64_list_value (xs)) = (X_r_eq_x * Y_r_eq_x ))) (PreH2 : (u64_list_bounded xs )) (PreH3 : ((Zlength (xs)) = 8)) (PreH4 : (0 <= Zout)) (PreH5 : (Zout < SM2_P_Z)) (PreH6 : ((X_r_eq_x * Y_r_eq_x ) = (Zout + (K * SM2_P_Z ) ))) (PreH7 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH8 : ((X_r_eq_x * Y_r_eq_x ) < U512_MOD)) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH13 : (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (Y_r_eq_x < SM2_P_Z)) (PreH32 : (0 <= Y_r_eq_x)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (retval = 0)) (PreH36 : (X_r_eq_x <> 1)) (PreH37 : (X_r_eq_x < SM2_P_Z)) (PreH38 : (0 <= X_r_eq_x)) (PreH39 : (result_pre = x_pre)) (PreH40 : (retval = 0)) (PreH41 : (retval_2 = 0)) ,
  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
|--
  EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (Y_r_eq_x = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (Zout = (Zmod ((X_r_eq_x * Y_r_eq_x )) (SM2_P_Z))) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
).

Definition mul_mod_p_return_wit_10_x_eq_y := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_2: Z) (K: Z) (Zout: Z) (xs: (@list Z)) (PreH1 : ((u64_list_value (xs)) = (X_x_eq_y * X_x_eq_y ))) (PreH2 : (u64_list_bounded xs )) (PreH3 : ((Zlength (xs)) = 8)) (PreH4 : (0 <= Zout)) (PreH5 : (Zout < SM2_P_Z)) (PreH6 : ((X_x_eq_y * X_x_eq_y ) = (Zout + (K * SM2_P_Z ) ))) (PreH7 : ((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))) (PreH8 : (0 <= (X_x_eq_y * X_x_eq_y ))) (PreH9 : ((X_x_eq_y * X_x_eq_y ) < U512_MOD)) (PreH10 : (0 <= retval_2)) (PreH11 : (retval_2 <= 1)) (PreH12 : (retval_2 = 0)) (PreH13 : ((u256_of_limbs (x0) (x1) (x2) (x3)) <> 1)) (PreH14 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (retval = 0)) (PreH26 : (X_x_eq_y <> 1)) (PreH27 : (X_x_eq_y < SM2_P_Z)) (PreH28 : (0 <= X_x_eq_y)) (PreH29 : (x_pre = y_pre)) (PreH30 : (retval = 0)) (PreH31 : (retval_2 = 0)) ,
  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_x_eq_y )
|--
  “ (x_pre = y_pre) ”
  &&  (store_fp x_pre X_x_eq_y )
  **  (store_fp result_pre (Zmod ((X_x_eq_y * X_x_eq_y )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_2: Z) (K: Z) (Zout: Z) (xs: (@list Z)) (PreH1 : ((u64_list_value (xs)) = (X_x_eq_y * X_x_eq_y ))) (PreH2 : (u64_list_bounded xs )) (PreH3 : ((Zlength (xs)) = 8)) (PreH4 : (0 <= Zout)) (PreH5 : (Zout < SM2_P_Z)) (PreH6 : ((X_x_eq_y * X_x_eq_y ) = (Zout + (K * SM2_P_Z ) ))) (PreH7 : ((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))) (PreH8 : (0 <= (X_x_eq_y * X_x_eq_y ))) (PreH9 : ((X_x_eq_y * X_x_eq_y ) < U512_MOD)) (PreH10 : (0 <= retval_2)) (PreH11 : (retval_2 <= 1)) (PreH12 : (retval_2 = 0)) (PreH13 : ((u256_of_limbs (x0) (x1) (x2) (x3)) <> 1)) (PreH14 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (retval = 0)) (PreH26 : (X_x_eq_y <> 1)) (PreH27 : (X_x_eq_y < SM2_P_Z)) (PreH28 : (0 <= X_x_eq_y)) (PreH29 : (x_pre = y_pre)) (PreH30 : (retval = 0)) (PreH31 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_x_eq_y )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (X_x_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (Zout = (Zmod ((X_x_eq_y * X_x_eq_y )) (SM2_P_Z))) ” 
  &&  “ (x_pre = y_pre) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
).

Definition mul_mod_p_return_wit_11_non_alias := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (K: Z) (Zout: Z) (xs: (@list Z)) (PreH1 : ((u64_list_value (xs)) = (X_non_alias * Y_non_alias ))) (PreH2 : (u64_list_bounded xs )) (PreH3 : ((Zlength (xs)) = 8)) (PreH4 : (0 <= Zout)) (PreH5 : (Zout < SM2_P_Z)) (PreH6 : ((X_non_alias * Y_non_alias ) = (Zout + (K * SM2_P_Z ) ))) (PreH7 : (0 <= (X_non_alias * Y_non_alias ))) (PreH8 : ((X_non_alias * Y_non_alias ) < U512_MOD)) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH13 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (Y_non_alias < SM2_P_Z)) (PreH32 : (0 <= Y_non_alias)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (retval = 0)) (PreH36 : (X_non_alias <> 1)) (PreH37 : (X_non_alias < SM2_P_Z)) (PreH38 : (0 <= X_non_alias)) (PreH39 : (retval = 0)) (PreH40 : (retval_2 = 0)) ,
  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
|--
  (store_fp x_pre X_non_alias )
  **  (store_fp y_pre Y_non_alias )
  **  (store_fp result_pre (Zmod ((X_non_alias * Y_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (K: Z) (Zout: Z) (xs: (@list Z)) (PreH1 : ((u64_list_value (xs)) = (X_non_alias * Y_non_alias ))) (PreH2 : (u64_list_bounded xs )) (PreH3 : ((Zlength (xs)) = 8)) (PreH4 : (0 <= Zout)) (PreH5 : (Zout < SM2_P_Z)) (PreH6 : ((X_non_alias * Y_non_alias ) = (Zout + (K * SM2_P_Z ) ))) (PreH7 : (0 <= (X_non_alias * Y_non_alias ))) (PreH8 : ((X_non_alias * Y_non_alias ) < U512_MOD)) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH13 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (Y_non_alias < SM2_P_Z)) (PreH32 : (0 <= Y_non_alias)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (retval = 0)) (PreH36 : (X_non_alias <> 1)) (PreH37 : (X_non_alias < SM2_P_Z)) (PreH38 : (0 <= X_non_alias)) (PreH39 : (retval = 0)) (PreH40 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
|--
  EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Zout = (Zmod ((X_non_alias * Y_non_alias )) (SM2_P_Z))) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
).

Definition mul_mod_p_partial_solve_wit_1_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (PreH1 : (result_pre = y_pre)) ,
  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp x_pre X_r_eq_y )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ”
  &&  (store_u256 x_pre X_r_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_y )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_2_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (PreH1 : (result_pre = x_pre)) ,
  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp x_pre X_r_eq_x )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (store_u256 x_pre X_r_eq_x )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_3_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (PreH1 : (x_pre = y_pre)) ,
  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp x_pre X_x_eq_y )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ”
  &&  (store_u256 x_pre X_x_eq_y )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_4_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) ,
  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp x_pre X_non_alias )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_5_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (Y_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (Y_r_eq_x < SM2_P_Z)) (PreH11 : (0 <= Y_r_eq_x)) (PreH12 : (result_pre = x_pre)) (PreH13 : (X_r_eq_x = 1)) ,
  (UndefStructPredu32 result_pre )
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (Y_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (X_r_eq_x = 1) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (UInt64Array.full &((y_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_6_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_x_eq_y < SM2_P_Z)) (PreH11 : (0 <= X_x_eq_y)) (PreH12 : (x_pre = y_pre)) (PreH13 : (X_x_eq_y = 1)) ,
  (UndefStructPredu32 result_pre )
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (X_x_eq_y = 1) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (UInt64Array.full &((y_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_7_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_P_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias = 1)) ,
  (UndefStructPredu32 result_pre )
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (UInt64Array.full &((y_pre)  # "u32" ->ₛ "v") 4 (cons (x0_2) ((cons (x1_2) ((cons (x2_2) ((cons (x3_2) ((@nil Z))))))))) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_8_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_r_eq_y < SM2_P_Z)) (PreH20 : (0 <= Y_r_eq_y)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : (retval = 0)) (PreH24 : (X_r_eq_y <> 1)) (PreH25 : (X_r_eq_y < SM2_P_Z)) (PreH26 : (0 <= X_r_eq_y)) (PreH27 : (result_pre = y_pre)) (PreH28 : (retval = 0)) ,
  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_9_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_r_eq_x < SM2_P_Z)) (PreH20 : (0 <= Y_r_eq_x)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : (retval = 0)) (PreH24 : (X_r_eq_x <> 1)) (PreH25 : (X_r_eq_x < SM2_P_Z)) (PreH26 : (0 <= X_r_eq_x)) (PreH27 : (result_pre = x_pre)) (PreH28 : (retval = 0)) ,
  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_10_x_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (0 <= retval)) (PreH11 : (retval <= 1)) (PreH12 : (retval = 0)) (PreH13 : (X_x_eq_y <> 1)) (PreH14 : (X_x_eq_y < SM2_P_Z)) (PreH15 : (0 <= X_x_eq_y)) (PreH16 : (x_pre = y_pre)) (PreH17 : (retval = 0)) ,
  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_11_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : (retval = 0)) (PreH24 : (X_non_alias <> 1)) (PreH25 : (X_non_alias < SM2_P_Z)) (PreH26 : (0 <= X_non_alias)) (PreH27 : (retval = 0)) ,
  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_12_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_r_eq_y < SM2_P_Z)) (PreH11 : (0 <= X_r_eq_y)) (PreH12 : (result_pre = y_pre)) (PreH13 : (X_r_eq_y <> 1)) (PreH14 : (Y_r_eq_y = 1)) ,
  (UndefStructPredu32 result_pre )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (Y_r_eq_y = 1) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (UInt64Array.full &((x_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_13_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_P_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_P_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias <> 1)) (PreH24 : (Y_non_alias = 1)) ,
  (UndefStructPredu32 result_pre )
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (Y_non_alias = 1) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (UInt64Array.full &((x_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_14_r_eq_y := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_y < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_y)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_y <> 1)) (PreH29 : (X_r_eq_y < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_y)) (PreH31 : (result_pre = y_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_y )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_y )
  **  (UInt64Array.undef_full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_15_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_r_eq_x < SM2_P_Z)) (PreH24 : (0 <= Y_r_eq_x)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_r_eq_x <> 1)) (PreH29 : (X_r_eq_x < SM2_P_Z)) (PreH30 : (0 <= X_r_eq_x)) (PreH31 : (result_pre = x_pre)) (PreH32 : (retval = 0)) (PreH33 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  (UInt64Array.undef_full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_16_x_eq_y_pure := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) <> 1)) (PreH5 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) (PreH14 : (0 <= retval)) (PreH15 : (retval <= 1)) (PreH16 : (retval = 0)) (PreH17 : (X_x_eq_y <> 1)) (PreH18 : (X_x_eq_y < SM2_P_Z)) (PreH19 : (0 <= X_x_eq_y)) (PreH20 : (x_pre = y_pre)) (PreH21 : (retval = 0)) (PreH22 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) ”
.

Definition mul_mod_p_partial_solve_wit_16_x_eq_y_aux := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) <> 1)) (PreH5 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) (PreH14 : (0 <= retval)) (PreH15 : (retval <= 1)) (PreH16 : (retval = 0)) (PreH17 : (X_x_eq_y <> 1)) (PreH18 : (X_x_eq_y < SM2_P_Z)) (PreH19 : (0 <= X_x_eq_y)) (PreH20 : (x_pre = y_pre)) (PreH21 : (retval = 0)) (PreH22 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) <> 1) ” 
  &&  “ (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_x_eq_y )
  **  (UInt64Array.undef_full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_16_x_eq_y := mul_mod_p_partial_solve_wit_16_x_eq_y_pure -> mul_mod_p_partial_solve_wit_16_x_eq_y_aux.

Definition mul_mod_p_partial_solve_wit_17_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH5 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (Y_non_alias < SM2_P_Z)) (PreH24 : (0 <= Y_non_alias)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 0)) (PreH28 : (X_non_alias <> 1)) (PreH29 : (X_non_alias < SM2_P_Z)) (PreH30 : (0 <= X_non_alias)) (PreH31 : (retval = 0)) (PreH32 : (retval_2 = 0)) ,
  (store_u256 y_pre (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  (UInt64Array.undef_full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition mul_mod_p_partial_solve_wit_18_r_eq_y_pure := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= (X_r_eq_y * Y_r_eq_y ))) (PreH2 : ((X_r_eq_y * Y_r_eq_y ) < U512_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH7 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (Y_r_eq_y < SM2_P_Z)) (PreH26 : (0 <= Y_r_eq_y)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 0)) (PreH30 : (X_r_eq_y <> 1)) (PreH31 : (X_r_eq_y < SM2_P_Z)) (PreH32 : (0 <= X_r_eq_y)) (PreH33 : (result_pre = y_pre)) (PreH34 : (retval = 0)) (PreH35 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_y )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_y )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_y * Y_r_eq_y ) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (X_r_eq_y * Y_r_eq_y )) ” 
  &&  “ ((X_r_eq_y * Y_r_eq_y ) < U512_MOD) ”
.

Definition mul_mod_p_partial_solve_wit_18_r_eq_y_aux := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_y: Z) (X_r_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= (X_r_eq_y * Y_r_eq_y ))) (PreH2 : ((X_r_eq_y * Y_r_eq_y ) < U512_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH7 : (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (Y_r_eq_y < SM2_P_Z)) (PreH26 : (0 <= Y_r_eq_y)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 0)) (PreH30 : (X_r_eq_y <> 1)) (PreH31 : (X_r_eq_y < SM2_P_Z)) (PreH32 : (0 <= X_r_eq_y)) (PreH33 : (result_pre = y_pre)) (PreH34 : (retval = 0)) (PreH35 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_y )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_y )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_y * Y_r_eq_y ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (X_r_eq_y * Y_r_eq_y )) ” 
  &&  “ ((X_r_eq_y * Y_r_eq_y ) < U512_MOD) ” 
  &&  “ (0 <= (X_r_eq_y * Y_r_eq_y )) ” 
  &&  “ ((X_r_eq_y * Y_r_eq_y ) < U512_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_y = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_y) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_y <> 1) ” 
  &&  “ (X_r_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_y) ” 
  &&  “ (result_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_y * Y_r_eq_y ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_y )
.

Definition mul_mod_p_partial_solve_wit_18_r_eq_y := mul_mod_p_partial_solve_wit_18_r_eq_y_pure -> mul_mod_p_partial_solve_wit_18_r_eq_y_aux.

Definition mul_mod_p_partial_solve_wit_19_r_eq_x_pure := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH2 : ((X_r_eq_x * Y_r_eq_x ) < U512_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH7 : (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (Y_r_eq_x < SM2_P_Z)) (PreH26 : (0 <= Y_r_eq_x)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 0)) (PreH30 : (X_r_eq_x <> 1)) (PreH31 : (X_r_eq_x < SM2_P_Z)) (PreH32 : (0 <= X_r_eq_x)) (PreH33 : (result_pre = x_pre)) (PreH34 : (retval = 0)) (PreH35 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * Y_r_eq_x ) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < U512_MOD) ”
.

Definition mul_mod_p_partial_solve_wit_19_r_eq_x_aux := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH2 : ((X_r_eq_x * Y_r_eq_x ) < U512_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH7 : (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (Y_r_eq_x < SM2_P_Z)) (PreH26 : (0 <= Y_r_eq_x)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 0)) (PreH30 : (X_r_eq_x <> 1)) (PreH31 : (X_r_eq_x < SM2_P_Z)) (PreH32 : (0 <= X_r_eq_x)) (PreH33 : (result_pre = x_pre)) (PreH34 : (retval = 0)) (PreH35 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * Y_r_eq_x ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < U512_MOD) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < U512_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_r_eq_x = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_r_eq_x <> 1) ” 
  &&  “ (X_r_eq_x < SM2_P_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * Y_r_eq_x ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
.

Definition mul_mod_p_partial_solve_wit_19_r_eq_x := mul_mod_p_partial_solve_wit_19_r_eq_x_pure -> mul_mod_p_partial_solve_wit_19_r_eq_x_aux.

Definition mul_mod_p_partial_solve_wit_20_x_eq_y_pure := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_2: Z) (PreH1 : ((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))) (PreH2 : (0 <= (X_x_eq_y * X_x_eq_y ))) (PreH3 : ((X_x_eq_y * X_x_eq_y ) < U512_MOD)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : ((u256_of_limbs (x0) (x1) (x2) (x3)) <> 1)) (PreH8 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 0)) (PreH20 : (X_x_eq_y <> 1)) (PreH21 : (X_x_eq_y < SM2_P_Z)) (PreH22 : (0 <= X_x_eq_y)) (PreH23 : (x_pre = y_pre)) (PreH24 : (retval = 0)) (PreH25 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_x_eq_y )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_x_eq_y * X_x_eq_y ) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (X_x_eq_y * X_x_eq_y )) ” 
  &&  “ ((X_x_eq_y * X_x_eq_y ) < U512_MOD) ”
.

Definition mul_mod_p_partial_solve_wit_20_x_eq_y_aux := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (X_x_eq_y: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_2: Z) (PreH1 : ((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))) (PreH2 : (0 <= (X_x_eq_y * X_x_eq_y ))) (PreH3 : ((X_x_eq_y * X_x_eq_y ) < U512_MOD)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : ((u256_of_limbs (x0) (x1) (x2) (x3)) <> 1)) (PreH8 : (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH9 : (x3 < U64_MOD)) (PreH10 : (0 <= x3)) (PreH11 : (x2 < U64_MOD)) (PreH12 : (0 <= x2)) (PreH13 : (x1 < U64_MOD)) (PreH14 : (0 <= x1)) (PreH15 : (x0 < U64_MOD)) (PreH16 : (0 <= x0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 0)) (PreH20 : (X_x_eq_y <> 1)) (PreH21 : (X_x_eq_y < SM2_P_Z)) (PreH22 : (0 <= X_x_eq_y)) (PreH23 : (x_pre = y_pre)) (PreH24 : (retval = 0)) (PreH25 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_x_eq_y )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_x_eq_y * X_x_eq_y ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (X_x_eq_y * X_x_eq_y )) ” 
  &&  “ ((X_x_eq_y * X_x_eq_y ) < U512_MOD) ” 
  &&  “ ((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) ” 
  &&  “ (0 <= (X_x_eq_y * X_x_eq_y )) ” 
  &&  “ ((X_x_eq_y * X_x_eq_y ) < U512_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) <> 1) ” 
  &&  “ (X_x_eq_y = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_x_eq_y <> 1) ” 
  &&  “ (X_x_eq_y < SM2_P_Z) ” 
  &&  “ (0 <= X_x_eq_y) ” 
  &&  “ (x_pre = y_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_x_eq_y * X_x_eq_y ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_x_eq_y )
.

Definition mul_mod_p_partial_solve_wit_20_x_eq_y := mul_mod_p_partial_solve_wit_20_x_eq_y_pure -> mul_mod_p_partial_solve_wit_20_x_eq_y_aux.

Definition mul_mod_p_partial_solve_wit_21_non_alias_pure := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= (X_non_alias * Y_non_alias ))) (PreH2 : ((X_non_alias * Y_non_alias ) < U512_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH7 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (Y_non_alias < SM2_P_Z)) (PreH26 : (0 <= Y_non_alias)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 0)) (PreH30 : (X_non_alias <> 1)) (PreH31 : (X_non_alias < SM2_P_Z)) (PreH32 : (0 <= X_non_alias)) (PreH33 : (retval = 0)) (PreH34 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * Y_non_alias ) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < U512_MOD) ”
.

Definition mul_mod_p_partial_solve_wit_21_non_alias_aux := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval_2: Z) (PreH1 : (0 <= (X_non_alias * Y_non_alias ))) (PreH2 : ((X_non_alias * Y_non_alias ) < U512_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1)) (PreH7 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH8 : (x3_2 < U64_MOD)) (PreH9 : (0 <= x3_2)) (PreH10 : (x2_2 < U64_MOD)) (PreH11 : (0 <= x2_2)) (PreH12 : (x1_2 < U64_MOD)) (PreH13 : (0 <= x1_2)) (PreH14 : (x0_2 < U64_MOD)) (PreH15 : (0 <= x0_2)) (PreH16 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (Y_non_alias < SM2_P_Z)) (PreH26 : (0 <= Y_non_alias)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 0)) (PreH30 : (X_non_alias <> 1)) (PreH31 : (X_non_alias < SM2_P_Z)) (PreH32 : (0 <= X_non_alias)) (PreH33 : (retval = 0)) (PreH34 : (retval_2 = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * Y_non_alias ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < U512_MOD) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < U512_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) <> 1) ” 
  &&  “ (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * Y_non_alias ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
.

Definition mul_mod_p_partial_solve_wit_21_non_alias := mul_mod_p_partial_solve_wit_21_non_alias_pure -> mul_mod_p_partial_solve_wit_21_non_alias_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include sm2_constants_Strategy_Correct.
Include u32_alias_Strategy_Correct.

Axiom proof_of_mul_mod_p_safety_wit_1_r_eq_y : mul_mod_p_safety_wit_1_r_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_2_r_eq_x : mul_mod_p_safety_wit_2_r_eq_x.
Axiom proof_of_mul_mod_p_safety_wit_3_x_eq_y : mul_mod_p_safety_wit_3_x_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_4_non_alias : mul_mod_p_safety_wit_4_non_alias.
Axiom proof_of_mul_mod_p_safety_wit_5_r_eq_y : mul_mod_p_safety_wit_5_r_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_6_r_eq_x : mul_mod_p_safety_wit_6_r_eq_x.
Axiom proof_of_mul_mod_p_safety_wit_7_x_eq_y : mul_mod_p_safety_wit_7_x_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_8_non_alias : mul_mod_p_safety_wit_8_non_alias.
Axiom proof_of_mul_mod_p_safety_wit_9_x_eq_y : mul_mod_p_safety_wit_9_x_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_10_r_eq_y : mul_mod_p_safety_wit_10_r_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_11_r_eq_x : mul_mod_p_safety_wit_11_r_eq_x.
Axiom proof_of_mul_mod_p_safety_wit_12_non_alias : mul_mod_p_safety_wit_12_non_alias.
Axiom proof_of_mul_mod_p_safety_wit_13_r_eq_y : mul_mod_p_safety_wit_13_r_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_14_r_eq_x : mul_mod_p_safety_wit_14_r_eq_x.
Axiom proof_of_mul_mod_p_safety_wit_15_x_eq_y : mul_mod_p_safety_wit_15_x_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_16_non_alias : mul_mod_p_safety_wit_16_non_alias.
Axiom proof_of_mul_mod_p_safety_wit_17_r_eq_y : mul_mod_p_safety_wit_17_r_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_18_r_eq_y : mul_mod_p_safety_wit_18_r_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_19_r_eq_y : mul_mod_p_safety_wit_19_r_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_20_r_eq_x : mul_mod_p_safety_wit_20_r_eq_x.
Axiom proof_of_mul_mod_p_safety_wit_21_r_eq_x : mul_mod_p_safety_wit_21_r_eq_x.
Axiom proof_of_mul_mod_p_safety_wit_22_r_eq_x : mul_mod_p_safety_wit_22_r_eq_x.
Axiom proof_of_mul_mod_p_safety_wit_23_x_eq_y : mul_mod_p_safety_wit_23_x_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_24_x_eq_y : mul_mod_p_safety_wit_24_x_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_25_x_eq_y : mul_mod_p_safety_wit_25_x_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_26_non_alias : mul_mod_p_safety_wit_26_non_alias.
Axiom proof_of_mul_mod_p_safety_wit_27_non_alias : mul_mod_p_safety_wit_27_non_alias.
Axiom proof_of_mul_mod_p_safety_wit_28_non_alias : mul_mod_p_safety_wit_28_non_alias.
Axiom proof_of_mul_mod_p_safety_wit_29_r_eq_y : mul_mod_p_safety_wit_29_r_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_30_r_eq_x : mul_mod_p_safety_wit_30_r_eq_x.
Axiom proof_of_mul_mod_p_safety_wit_31_x_eq_y : mul_mod_p_safety_wit_31_x_eq_y.
Axiom proof_of_mul_mod_p_safety_wit_32_non_alias : mul_mod_p_safety_wit_32_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_1_1_r_eq_y : mul_mod_p_entail_wit_1_1_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_1_2_r_eq_y : mul_mod_p_entail_wit_1_2_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_1_3_r_eq_x : mul_mod_p_entail_wit_1_3_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_1_4_r_eq_x : mul_mod_p_entail_wit_1_4_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_1_5_x_eq_y : mul_mod_p_entail_wit_1_5_x_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_1_6_x_eq_y : mul_mod_p_entail_wit_1_6_x_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_1_7_non_alias : mul_mod_p_entail_wit_1_7_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_1_8_non_alias : mul_mod_p_entail_wit_1_8_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_2_1_r_eq_y : mul_mod_p_entail_wit_2_1_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_2_2_r_eq_y : mul_mod_p_entail_wit_2_2_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_2_3_r_eq_x : mul_mod_p_entail_wit_2_3_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_2_4_r_eq_x : mul_mod_p_entail_wit_2_4_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_2_5_x_eq_y : mul_mod_p_entail_wit_2_5_x_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_2_6_x_eq_y : mul_mod_p_entail_wit_2_6_x_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_2_7_non_alias : mul_mod_p_entail_wit_2_7_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_2_8_non_alias : mul_mod_p_entail_wit_2_8_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_3_non_alias : mul_mod_p_entail_wit_3_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_4_x_eq_y : mul_mod_p_entail_wit_4_x_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_5_r_eq_x : mul_mod_p_entail_wit_5_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_6_r_eq_y : mul_mod_p_entail_wit_6_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_7_1_r_eq_y : mul_mod_p_entail_wit_7_1_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_7_2_r_eq_x : mul_mod_p_entail_wit_7_2_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_7_3_x_eq_y : mul_mod_p_entail_wit_7_3_x_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_7_4_non_alias : mul_mod_p_entail_wit_7_4_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_8_1_r_eq_y : mul_mod_p_entail_wit_8_1_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_8_2_r_eq_x : mul_mod_p_entail_wit_8_2_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_8_3_x_eq_y : mul_mod_p_entail_wit_8_3_x_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_8_4_non_alias : mul_mod_p_entail_wit_8_4_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_9_1_r_eq_y : mul_mod_p_entail_wit_9_1_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_9_2_r_eq_x : mul_mod_p_entail_wit_9_2_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_9_3_x_eq_y : mul_mod_p_entail_wit_9_3_x_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_9_4_non_alias : mul_mod_p_entail_wit_9_4_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_10_1_r_eq_y : mul_mod_p_entail_wit_10_1_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_10_2_r_eq_x : mul_mod_p_entail_wit_10_2_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_10_3_x_eq_y : mul_mod_p_entail_wit_10_3_x_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_10_4_non_alias : mul_mod_p_entail_wit_10_4_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_11_1_r_eq_y : mul_mod_p_entail_wit_11_1_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_11_2_r_eq_y : mul_mod_p_entail_wit_11_2_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_11_3_r_eq_x : mul_mod_p_entail_wit_11_3_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_11_4_r_eq_x : mul_mod_p_entail_wit_11_4_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_11_5_x_eq_y : mul_mod_p_entail_wit_11_5_x_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_11_6_non_alias : mul_mod_p_entail_wit_11_6_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_11_7_non_alias : mul_mod_p_entail_wit_11_7_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_12_1_r_eq_y : mul_mod_p_entail_wit_12_1_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_12_2_r_eq_y : mul_mod_p_entail_wit_12_2_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_12_3_r_eq_x : mul_mod_p_entail_wit_12_3_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_12_4_r_eq_x : mul_mod_p_entail_wit_12_4_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_12_5_x_eq_y : mul_mod_p_entail_wit_12_5_x_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_12_6_non_alias : mul_mod_p_entail_wit_12_6_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_12_7_non_alias : mul_mod_p_entail_wit_12_7_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_13_non_alias : mul_mod_p_entail_wit_13_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_14_r_eq_x : mul_mod_p_entail_wit_14_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_15_r_eq_y : mul_mod_p_entail_wit_15_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_16_1_r_eq_y : mul_mod_p_entail_wit_16_1_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_16_2_r_eq_x : mul_mod_p_entail_wit_16_2_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_16_3_non_alias : mul_mod_p_entail_wit_16_3_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_17_1_r_eq_y : mul_mod_p_entail_wit_17_1_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_17_2_r_eq_x : mul_mod_p_entail_wit_17_2_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_17_3_non_alias : mul_mod_p_entail_wit_17_3_non_alias.
Axiom proof_of_mul_mod_p_entail_wit_18_1_r_eq_y : mul_mod_p_entail_wit_18_1_r_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_18_2_r_eq_x : mul_mod_p_entail_wit_18_2_r_eq_x.
Axiom proof_of_mul_mod_p_entail_wit_18_3_x_eq_y : mul_mod_p_entail_wit_18_3_x_eq_y.
Axiom proof_of_mul_mod_p_entail_wit_18_4_non_alias : mul_mod_p_entail_wit_18_4_non_alias.
Axiom proof_of_mul_mod_p_return_wit_1_non_alias : mul_mod_p_return_wit_1_non_alias.
Axiom proof_of_mul_mod_p_return_wit_2_r_eq_x : mul_mod_p_return_wit_2_r_eq_x.
Axiom proof_of_mul_mod_p_return_wit_3_r_eq_y : mul_mod_p_return_wit_3_r_eq_y.
Axiom proof_of_mul_mod_p_return_wit_4_non_alias : mul_mod_p_return_wit_4_non_alias.
Axiom proof_of_mul_mod_p_return_wit_5_x_eq_y : mul_mod_p_return_wit_5_x_eq_y.
Axiom proof_of_mul_mod_p_return_wit_6_r_eq_x : mul_mod_p_return_wit_6_r_eq_x.
Axiom proof_of_mul_mod_p_return_wit_7_r_eq_y : mul_mod_p_return_wit_7_r_eq_y.
Axiom proof_of_mul_mod_p_return_wit_8_r_eq_y : mul_mod_p_return_wit_8_r_eq_y.
Axiom proof_of_mul_mod_p_return_wit_9_r_eq_x : mul_mod_p_return_wit_9_r_eq_x.
Axiom proof_of_mul_mod_p_return_wit_10_x_eq_y : mul_mod_p_return_wit_10_x_eq_y.
Axiom proof_of_mul_mod_p_return_wit_11_non_alias : mul_mod_p_return_wit_11_non_alias.
Axiom proof_of_mul_mod_p_partial_solve_wit_1_r_eq_y : mul_mod_p_partial_solve_wit_1_r_eq_y.
Axiom proof_of_mul_mod_p_partial_solve_wit_2_r_eq_x : mul_mod_p_partial_solve_wit_2_r_eq_x.
Axiom proof_of_mul_mod_p_partial_solve_wit_3_x_eq_y : mul_mod_p_partial_solve_wit_3_x_eq_y.
Axiom proof_of_mul_mod_p_partial_solve_wit_4_non_alias : mul_mod_p_partial_solve_wit_4_non_alias.
Axiom proof_of_mul_mod_p_partial_solve_wit_5_r_eq_x : mul_mod_p_partial_solve_wit_5_r_eq_x.
Axiom proof_of_mul_mod_p_partial_solve_wit_6_x_eq_y : mul_mod_p_partial_solve_wit_6_x_eq_y.
Axiom proof_of_mul_mod_p_partial_solve_wit_7_non_alias : mul_mod_p_partial_solve_wit_7_non_alias.
Axiom proof_of_mul_mod_p_partial_solve_wit_8_r_eq_y : mul_mod_p_partial_solve_wit_8_r_eq_y.
Axiom proof_of_mul_mod_p_partial_solve_wit_9_r_eq_x : mul_mod_p_partial_solve_wit_9_r_eq_x.
Axiom proof_of_mul_mod_p_partial_solve_wit_10_x_eq_y : mul_mod_p_partial_solve_wit_10_x_eq_y.
Axiom proof_of_mul_mod_p_partial_solve_wit_11_non_alias : mul_mod_p_partial_solve_wit_11_non_alias.
Axiom proof_of_mul_mod_p_partial_solve_wit_12_r_eq_y : mul_mod_p_partial_solve_wit_12_r_eq_y.
Axiom proof_of_mul_mod_p_partial_solve_wit_13_non_alias : mul_mod_p_partial_solve_wit_13_non_alias.
Axiom proof_of_mul_mod_p_partial_solve_wit_14_r_eq_y : mul_mod_p_partial_solve_wit_14_r_eq_y.
Axiom proof_of_mul_mod_p_partial_solve_wit_15_r_eq_x : mul_mod_p_partial_solve_wit_15_r_eq_x.
Axiom proof_of_mul_mod_p_partial_solve_wit_16_x_eq_y_pure : mul_mod_p_partial_solve_wit_16_x_eq_y_pure.
Axiom proof_of_mul_mod_p_partial_solve_wit_16_x_eq_y : mul_mod_p_partial_solve_wit_16_x_eq_y.
Axiom proof_of_mul_mod_p_partial_solve_wit_17_non_alias : mul_mod_p_partial_solve_wit_17_non_alias.
Axiom proof_of_mul_mod_p_partial_solve_wit_18_r_eq_y_pure : mul_mod_p_partial_solve_wit_18_r_eq_y_pure.
Axiom proof_of_mul_mod_p_partial_solve_wit_18_r_eq_y : mul_mod_p_partial_solve_wit_18_r_eq_y.
Axiom proof_of_mul_mod_p_partial_solve_wit_19_r_eq_x_pure : mul_mod_p_partial_solve_wit_19_r_eq_x_pure.
Axiom proof_of_mul_mod_p_partial_solve_wit_19_r_eq_x : mul_mod_p_partial_solve_wit_19_r_eq_x.
Axiom proof_of_mul_mod_p_partial_solve_wit_20_x_eq_y_pure : mul_mod_p_partial_solve_wit_20_x_eq_y_pure.
Axiom proof_of_mul_mod_p_partial_solve_wit_20_x_eq_y : mul_mod_p_partial_solve_wit_20_x_eq_y.
Axiom proof_of_mul_mod_p_partial_solve_wit_21_non_alias_pure : mul_mod_p_partial_solve_wit_21_non_alias_pure.
Axiom proof_of_mul_mod_p_partial_solve_wit_21_non_alias : mul_mod_p_partial_solve_wit_21_non_alias.

End VC_Correct.
