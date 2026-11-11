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
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_proof.

(*----- Function affine_to_jacobian -----*)

Definition affine_to_jacobian_safety_wit_1 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (X_non_alias = 0)) (PreH6 : (Y_non_alias = 0)) ,
  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ False ”
.

Definition affine_to_jacobian_safety_wit_2 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (Y_non_alias <> 0)) ,
  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ False ”
.

Definition affine_to_jacobian_safety_wit_3 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (X_non_alias <> 0)) ,
  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ False ”
.

Definition affine_to_jacobian_safety_wit_4 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition affine_to_jacobian_safety_wit_5 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition affine_to_jacobian_safety_wit_6 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition affine_to_jacobian_safety_wit_7 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition affine_to_jacobian_safety_wit_8 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 1 4 )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition affine_to_jacobian_safety_wit_9 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 1 4 )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition affine_to_jacobian_safety_wit_10 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 1 4 )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition affine_to_jacobian_safety_wit_11 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 1 4 )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition affine_to_jacobian_safety_wit_12 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition affine_to_jacobian_safety_wit_13 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition affine_to_jacobian_safety_wit_14 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition affine_to_jacobian_safety_wit_15 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition affine_to_jacobian_safety_wit_16 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition affine_to_jacobian_safety_wit_17 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition affine_to_jacobian_safety_wit_18 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition affine_to_jacobian_safety_wit_19 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition affine_to_jacobian_entail_wit_1_1 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (Y_non_alias <> 0)) ,
  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  (“ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y_non_alias <> 0) ”
  &&  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero ))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_non_alias <> 0) ”
  &&  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero ))
.

Definition affine_to_jacobian_entail_wit_1_2 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (X_non_alias <> 0)) ,
  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  (EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y_non_alias <> 0) ”
  &&  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero ))
  ||
  (“ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_non_alias <> 0) ”
  &&  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero ))
.

Definition affine_to_jacobian_entail_wit_2_1 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (Y_non_alias <> 0)) ,
  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  (EX (ys: (@list Z))  (xs: (@list Z)) ,
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y_non_alias <> 0) ”
  &&  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero ))
  ||
  (EX (ys_2: (@list Z))  (xs_2: (@list Z))  (retval_2: Z) ,
  “ ((u64_list_value (ys_2)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys_2 ) ” 
  &&  “ ((Zlength (ys_2)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs_2)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs_2 ) ” 
  &&  “ ((Zlength (xs_2)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_non_alias <> 0) ”
  &&  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys_2 )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs_2 )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero ))
.

Definition affine_to_jacobian_entail_wit_2_2 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (X_non_alias <> 0)) ,
  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  (EX (ys: (@list Z))  (xs: (@list Z))  (retval: Z) ,
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y_non_alias <> 0) ”
  &&  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero ))
  ||
  (EX (ys_2: (@list Z))  (xs_2: (@list Z)) ,
  “ ((u64_list_value (ys_2)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys_2 ) ” 
  &&  “ ((Zlength (ys_2)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs_2)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs_2 ) ” 
  &&  “ ((Zlength (xs_2)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_non_alias <> 0) ”
  &&  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys_2 )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs_2 )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero ))
.

Definition affine_to_jacobian_entail_wit_3 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (X_non_alias = 0)) (PreH6 : (Y_non_alias = 0)) ,
  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_non_alias = 0) ” 
  &&  “ (Y_non_alias = 0) ”
  &&  (UndefStructPredJPoint result_pre )
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
.

Definition affine_to_jacobian_entail_wit_4 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (X_non_alias = 0)) (PreH6 : (Y_non_alias = 0)) ,
  (UndefStructPredJPoint result_pre )
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_non_alias = 0) ” 
  &&  “ (Y_non_alias = 0) ”
  &&  (store_jpoint_fields ( &( "JPoint_ZERO" ) ) 1 1 0 )
  **  (UndefStructPredJPoint result_pre )
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
.

Definition affine_to_jacobian_entail_wit_5 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (X_non_alias = 0)) (PreH6 : (Y_non_alias = 0)) ,
  (store_jpoint_fields ( &( "JPoint_ZERO" ) ) 1 1 0 )
  **  (UndefStructPredJPoint result_pre )
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
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
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_non_alias = 0) ” 
  &&  “ (Y_non_alias = 0) ”
  &&  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredJPoint result_pre )
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
.

Definition affine_to_jacobian_return_wit_1 := 
(
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
|--
  EX (RX: Z)  (RY: Z)  (RZ: Z) ,
  “ (afpoint_to_jpoint_coordinates X_non_alias Y_non_alias RX RY RZ ) ”
  &&  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (store_jpoint_fields result_pre RX RY RZ )
  **  (store_jpoint_zero )
) \/
(
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  TT && emp 
|--
  “ (afpoint_to_jpoint_coordinates X_non_alias Y_non_alias X_non_alias Y_non_alias (u256_of_limbs (1) (0) (0) (0)) ) ” 
  &&  “ (0 <= (u256_of_limbs (1) (0) (0) (0))) ” 
  &&  “ ((u256_of_limbs (1) (0) (0) (0)) < SM2_P_Z) ” 
  &&  “ (1 < U64_MOD) ” 
  &&  “ (0 < U64_MOD) ” 
  &&  “ (0 < U64_MOD) ” 
  &&  “ (0 < U64_MOD) ”
  &&  emp
).

Definition affine_to_jacobian_return_wit_1_split_goal_1 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (afpoint_to_jpoint_coordinates X_non_alias Y_non_alias X_non_alias Y_non_alias (u256_of_limbs (1) (0) (0) (0)) )
.

Definition affine_to_jacobian_return_wit_1_split_goal_2 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (0 <= (u256_of_limbs (1) (0) (0) (0)))
.

Definition affine_to_jacobian_return_wit_1_split_goal_3 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  ((u256_of_limbs (1) (0) (0) (0)) < SM2_P_Z)
.

Definition affine_to_jacobian_return_wit_1_split_goal_4 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (1 < U64_MOD)
.

Definition affine_to_jacobian_return_wit_1_split_goal_5 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (0 < U64_MOD)
.

Definition affine_to_jacobian_return_wit_1_split_goal_6 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (0 < U64_MOD)
.

Definition affine_to_jacobian_return_wit_1_split_goal_7 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (0 < U64_MOD)
.

Definition affine_to_jacobian_return_wit_2 := 
(
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
|--
  EX (RX: Z)  (RY: Z)  (RZ: Z) ,
  “ (afpoint_to_jpoint_coordinates X_non_alias Y_non_alias RX RY RZ ) ”
  &&  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (store_jpoint_fields result_pre RX RY RZ )
  **  (store_jpoint_zero )
) \/
(
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  TT && emp 
|--
  “ (afpoint_to_jpoint_coordinates X_non_alias Y_non_alias X_non_alias Y_non_alias (u256_of_limbs (1) (0) (0) (0)) ) ” 
  &&  “ (0 <= (u256_of_limbs (1) (0) (0) (0))) ” 
  &&  “ ((u256_of_limbs (1) (0) (0) (0)) < SM2_P_Z) ” 
  &&  “ (1 < U64_MOD) ” 
  &&  “ (0 < U64_MOD) ” 
  &&  “ (0 < U64_MOD) ” 
  &&  “ (0 < U64_MOD) ”
  &&  emp
).

Definition affine_to_jacobian_return_wit_2_split_goal_1 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (afpoint_to_jpoint_coordinates X_non_alias Y_non_alias X_non_alias Y_non_alias (u256_of_limbs (1) (0) (0) (0)) )
.

Definition affine_to_jacobian_return_wit_2_split_goal_2 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (0 <= (u256_of_limbs (1) (0) (0) (0)))
.

Definition affine_to_jacobian_return_wit_2_split_goal_3 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  ((u256_of_limbs (1) (0) (0) (0)) < SM2_P_Z)
.

Definition affine_to_jacobian_return_wit_2_split_goal_4 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (1 < U64_MOD)
.

Definition affine_to_jacobian_return_wit_2_split_goal_5 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (0 < U64_MOD)
.

Definition affine_to_jacobian_return_wit_2_split_goal_6 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (0 < U64_MOD)
.

Definition affine_to_jacobian_return_wit_2_split_goal_7 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (0 < U64_MOD)
.

Definition affine_to_jacobian_return_wit_3 := 
(
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = 0)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (0 < SM2_P_Z)) (PreH5 : (0 <= 0)) (PreH6 : ((u64_list_value (ys)) = 1)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (1 < SM2_P_Z)) (PreH10 : (0 <= 1)) (PreH11 : ((u64_list_value (xs)) = 1)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (1 < SM2_P_Z)) (PreH15 : (0 <= 1)) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (X_non_alias = 0)) (PreH21 : (Y_non_alias = 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
|--
  EX (RX: Z)  (RY: Z)  (RZ: Z) ,
  “ (afpoint_to_jpoint_coordinates X_non_alias Y_non_alias RX RY RZ ) ”
  &&  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (store_jpoint_fields result_pre RX RY RZ )
  **  (store_jpoint_zero )
) \/
(
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = 0)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (0 < SM2_P_Z)) (PreH5 : (0 <= 0)) (PreH6 : ((u64_list_value (ys)) = 1)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (1 < SM2_P_Z)) (PreH10 : (0 <= 1)) (PreH11 : ((u64_list_value (xs)) = 1)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (1 < SM2_P_Z)) (PreH15 : (0 <= 1)) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (X_non_alias = 0)) (PreH21 : (Y_non_alias = 0)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  “ (afpoint_to_jpoint_coordinates 0 0 1 1 0 ) ”
  &&  (store_jpoint_zero )
).

Definition affine_to_jacobian_return_wit_3_split_goal_1 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = 0)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (0 < SM2_P_Z)) (PreH5 : (0 <= 0)) (PreH6 : ((u64_list_value (ys)) = 1)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (1 < SM2_P_Z)) (PreH10 : (0 <= 1)) (PreH11 : ((u64_list_value (xs)) = 1)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (1 < SM2_P_Z)) (PreH15 : (0 <= 1)) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (X_non_alias = 0)) (PreH21 : (Y_non_alias = 0)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  “ (afpoint_to_jpoint_coordinates 0 0 1 1 0 ) ”
.

Definition affine_to_jacobian_return_wit_3_split_goal_spatial := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = 0)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (0 < SM2_P_Z)) (PreH5 : (0 <= 0)) (PreH6 : ((u64_list_value (ys)) = 1)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (1 < SM2_P_Z)) (PreH10 : (0 <= 1)) (PreH11 : ((u64_list_value (xs)) = 1)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (1 < SM2_P_Z)) (PreH15 : (0 <= 1)) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (X_non_alias = 0)) (PreH21 : (Y_non_alias = 0)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  (store_jpoint_zero )
.

Definition affine_to_jacobian_partial_solve_wit_1 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) ,
  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition affine_to_jacobian_partial_solve_wit_2 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y_non_alias <> 0) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition affine_to_jacobian_partial_solve_wit_3 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 0) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition affine_to_jacobian_partial_solve_wit_4 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 0) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition affine_to_jacobian_partial_solve_wit_5 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y_non_alias <> 0) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition affine_to_jacobian_partial_solve_wit_6 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y_non_alias <> 0) ”
  &&  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 1 4 )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
.

Definition affine_to_jacobian_partial_solve_wit_7 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 0) ”
  &&  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 1 4 )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
.

Definition affine_to_jacobian_partial_solve_wit_8 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 1 4 )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y_non_alias <> 0) ”
  &&  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
.

Definition affine_to_jacobian_partial_solve_wit_9 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 1 4 )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 0) ”
  &&  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
.

Definition affine_to_jacobian_partial_solve_wit_10 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y_non_alias <> 0) ”
  &&  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 2 (1 + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
.

Definition affine_to_jacobian_partial_solve_wit_11 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 0) ”
  &&  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 2 (1 + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
.

Definition affine_to_jacobian_partial_solve_wit_12 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (Y_non_alias <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y_non_alias <> 0) ”
  &&  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 3 ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
.

Definition affine_to_jacobian_partial_solve_wit_13 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (retval = 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (X_non_alias <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 0) ”
  &&  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 3 ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_jpoint_zero )
.

Definition affine_to_jacobian_partial_solve_wit_14 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = 0)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (0 < SM2_P_Z)) (PreH5 : (0 <= 0)) (PreH6 : ((u64_list_value (ys)) = 1)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (1 < SM2_P_Z)) (PreH10 : (0 <= 1)) (PreH11 : ((u64_list_value (xs)) = 1)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (1 < SM2_P_Z)) (PreH15 : (0 <= 1)) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (X_non_alias = 0)) (PreH21 : (Y_non_alias = 0)) ,
  (UndefStructPredJPoint result_pre )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
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
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_non_alias = 0) ” 
  &&  “ (Y_non_alias = 0) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
.

Definition affine_to_jacobian_derive_point_non_alias_by_non_alias := 
forall (result_pre: Z) (point_pre: Z) (P_point_non_alias: ec_point) ,
  (store_afpoint point_pre P_point_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
EX (X_non_alias: Z) (Y_non_alias: Z) ,
  ((store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero ))
  **
  ((EX RX RY RZ,
  “ (afpoint_to_jpoint_coordinates X_non_alias Y_non_alias RX RY RZ ) ”
  &&  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (store_jpoint_fields result_pre RX RY RZ )
  **  (store_jpoint_zero ))
  -*
  ((store_afpoint point_pre P_point_non_alias )
  **  (store_jpoint_with_canonical_infinity result_pre P_point_non_alias )
  **  (store_jpoint_zero )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include ecc_point_copy_steps_Strategy_Correct.

Axiom proof_of_affine_to_jacobian_safety_wit_1 : affine_to_jacobian_safety_wit_1.
Axiom proof_of_affine_to_jacobian_safety_wit_2 : affine_to_jacobian_safety_wit_2.
Axiom proof_of_affine_to_jacobian_safety_wit_3 : affine_to_jacobian_safety_wit_3.
Axiom proof_of_affine_to_jacobian_safety_wit_4 : affine_to_jacobian_safety_wit_4.
Axiom proof_of_affine_to_jacobian_safety_wit_5 : affine_to_jacobian_safety_wit_5.
Axiom proof_of_affine_to_jacobian_safety_wit_6 : affine_to_jacobian_safety_wit_6.
Axiom proof_of_affine_to_jacobian_safety_wit_7 : affine_to_jacobian_safety_wit_7.
Axiom proof_of_affine_to_jacobian_safety_wit_8 : affine_to_jacobian_safety_wit_8.
Axiom proof_of_affine_to_jacobian_safety_wit_9 : affine_to_jacobian_safety_wit_9.
Axiom proof_of_affine_to_jacobian_safety_wit_10 : affine_to_jacobian_safety_wit_10.
Axiom proof_of_affine_to_jacobian_safety_wit_11 : affine_to_jacobian_safety_wit_11.
Axiom proof_of_affine_to_jacobian_safety_wit_12 : affine_to_jacobian_safety_wit_12.
Axiom proof_of_affine_to_jacobian_safety_wit_13 : affine_to_jacobian_safety_wit_13.
Axiom proof_of_affine_to_jacobian_safety_wit_14 : affine_to_jacobian_safety_wit_14.
Axiom proof_of_affine_to_jacobian_safety_wit_15 : affine_to_jacobian_safety_wit_15.
Axiom proof_of_affine_to_jacobian_safety_wit_16 : affine_to_jacobian_safety_wit_16.
Axiom proof_of_affine_to_jacobian_safety_wit_17 : affine_to_jacobian_safety_wit_17.
Axiom proof_of_affine_to_jacobian_safety_wit_18 : affine_to_jacobian_safety_wit_18.
Axiom proof_of_affine_to_jacobian_safety_wit_19 : affine_to_jacobian_safety_wit_19.
Axiom proof_of_affine_to_jacobian_entail_wit_1_1 : affine_to_jacobian_entail_wit_1_1.
Axiom proof_of_affine_to_jacobian_entail_wit_1_2 : affine_to_jacobian_entail_wit_1_2.
Axiom proof_of_affine_to_jacobian_entail_wit_2_1 : affine_to_jacobian_entail_wit_2_1.
Axiom proof_of_affine_to_jacobian_entail_wit_2_2 : affine_to_jacobian_entail_wit_2_2.
Axiom proof_of_affine_to_jacobian_entail_wit_3 : affine_to_jacobian_entail_wit_3.
Axiom proof_of_affine_to_jacobian_entail_wit_4 : affine_to_jacobian_entail_wit_4.
Axiom proof_of_affine_to_jacobian_entail_wit_5 : affine_to_jacobian_entail_wit_5.
Axiom proof_of_affine_to_jacobian_return_wit_1 : affine_to_jacobian_return_wit_1.
Axiom proof_of_affine_to_jacobian_return_wit_2 : affine_to_jacobian_return_wit_2.
Axiom proof_of_affine_to_jacobian_return_wit_3 : affine_to_jacobian_return_wit_3.
Axiom proof_of_affine_to_jacobian_partial_solve_wit_1 : affine_to_jacobian_partial_solve_wit_1.
Axiom proof_of_affine_to_jacobian_partial_solve_wit_2 : affine_to_jacobian_partial_solve_wit_2.
Axiom proof_of_affine_to_jacobian_partial_solve_wit_3 : affine_to_jacobian_partial_solve_wit_3.
Axiom proof_of_affine_to_jacobian_partial_solve_wit_4 : affine_to_jacobian_partial_solve_wit_4.
Axiom proof_of_affine_to_jacobian_partial_solve_wit_5 : affine_to_jacobian_partial_solve_wit_5.
Axiom proof_of_affine_to_jacobian_partial_solve_wit_6 : affine_to_jacobian_partial_solve_wit_6.
Axiom proof_of_affine_to_jacobian_partial_solve_wit_7 : affine_to_jacobian_partial_solve_wit_7.
Axiom proof_of_affine_to_jacobian_partial_solve_wit_8 : affine_to_jacobian_partial_solve_wit_8.
Axiom proof_of_affine_to_jacobian_partial_solve_wit_9 : affine_to_jacobian_partial_solve_wit_9.
Axiom proof_of_affine_to_jacobian_partial_solve_wit_10 : affine_to_jacobian_partial_solve_wit_10.
Axiom proof_of_affine_to_jacobian_partial_solve_wit_11 : affine_to_jacobian_partial_solve_wit_11.
Axiom proof_of_affine_to_jacobian_partial_solve_wit_12 : affine_to_jacobian_partial_solve_wit_12.
Axiom proof_of_affine_to_jacobian_partial_solve_wit_13 : affine_to_jacobian_partial_solve_wit_13.
Axiom proof_of_affine_to_jacobian_partial_solve_wit_14 : affine_to_jacobian_partial_solve_wit_14.
Axiom proof_of_affine_to_jacobian_derive_point_non_alias_by_non_alias : affine_to_jacobian_derive_point_non_alias_by_non_alias.

End VC_Correct.
