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
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_proof.

(*----- Function montg_is_apoint_zero -----*)

Definition montg_is_apoint_zero_safety_wit_1 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (X_coords)))) (PreH3 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (Y_coords)))) (PreH5 : (Y_coords < SM2_P_Z)) (PreH6 : (0 <= Y_coords)) (PreH7 : (X_coords < SM2_P_Z)) (PreH8 : (0 <= X_coords)) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_is_apoint_zero_safety_wit_2 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (X_coords)))) (PreH3 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (Y_coords)))) (PreH5 : (Y_coords < SM2_P_Z)) (PreH6 : (0 <= Y_coords)) (PreH7 : (X_coords < SM2_P_Z)) (PreH8 : (0 <= X_coords)) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_is_apoint_zero_safety_wit_3 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : ((mont_p (X_coords)) <> 0)) (PreH4 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH5 : (0 <= (mont_p (X_coords)))) (PreH6 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH7 : (0 <= (mont_p (Y_coords)))) (PreH8 : (Y_coords < SM2_P_Z)) (PreH9 : (0 <= Y_coords)) (PreH10 : (X_coords < SM2_P_Z)) (PreH11 : (0 <= X_coords)) (PreH12 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (store_u256_limbs (&((dst_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (X_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ False ”
.

Definition montg_is_apoint_zero_safety_wit_4 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 1)) (PreH3 : ((mont_p (X_coords)) = 0)) (PreH4 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH5 : (0 <= (mont_p (X_coords)))) (PreH6 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH7 : (0 <= (mont_p (Y_coords)))) (PreH8 : (Y_coords < SM2_P_Z)) (PreH9 : (0 <= Y_coords)) (PreH10 : (X_coords < SM2_P_Z)) (PreH11 : (0 <= X_coords)) (PreH12 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (store_u256_limbs (&((dst_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (X_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ False ”
.

Definition montg_is_apoint_zero_safety_wit_5 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : ((mont_p (X_coords)) <> 0)) (PreH4 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH5 : (0 <= (mont_p (X_coords)))) (PreH6 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH7 : (0 <= (mont_p (Y_coords)))) (PreH8 : (Y_coords < SM2_P_Z)) (PreH9 : (0 <= Y_coords)) (PreH10 : (X_coords < SM2_P_Z)) (PreH11 : (0 <= X_coords)) (PreH12 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_is_apoint_zero_safety_wit_6 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : ((mont_p (X_coords)) = 0)) (PreH4 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH5 : (0 <= (mont_p (X_coords)))) (PreH6 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH7 : (0 <= (mont_p (Y_coords)))) (PreH8 : (Y_coords < SM2_P_Z)) (PreH9 : (0 <= Y_coords)) (PreH10 : (X_coords < SM2_P_Z)) (PreH11 : (0 <= X_coords)) (PreH12 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_is_apoint_zero_safety_wit_7 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : ((mont_p (X_coords)) = 0)) (PreH4 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH5 : (0 <= (mont_p (X_coords)))) (PreH6 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH7 : (0 <= (mont_p (Y_coords)))) (PreH8 : (Y_coords < SM2_P_Z)) (PreH9 : (0 <= Y_coords)) (PreH10 : (X_coords < SM2_P_Z)) (PreH11 : (0 <= X_coords)) (PreH12 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_is_apoint_zero_safety_wit_8 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Y_coords)) <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : ((mont_p (X_coords)) = 0)) (PreH7 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (X_coords)))) (PreH9 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (Y_coords)))) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (store_u256_limbs (&((dst_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Y_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ False ”
.

Definition montg_is_apoint_zero_safety_wit_9 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Y_coords)) = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : ((mont_p (X_coords)) = 0)) (PreH7 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (X_coords)))) (PreH9 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (Y_coords)))) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (store_u256_limbs (&((dst_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Y_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ False ”
.

Definition montg_is_apoint_zero_safety_wit_10 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Y_coords)) <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : ((mont_p (X_coords)) = 0)) (PreH7 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (X_coords)))) (PreH9 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (Y_coords)))) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_is_apoint_zero_safety_wit_11 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Y_coords)) = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : ((mont_p (X_coords)) = 0)) (PreH7 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (X_coords)))) (PreH9 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (Y_coords)))) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_is_apoint_zero_entail_wit_1 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) ,
  (store_u256_limbs ( &( "BN_ZERO" ) ) 0 )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (store_mont_afpoint_coords dst_pre X_coords Y_coords )
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
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (store_mont_afpoint_coords dst_pre X_coords Y_coords )
.

Definition montg_is_apoint_zero_entail_wit_2 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (store_mont_afpoint_coords dst_pre X_coords Y_coords )
|--
  “ (Y_coords < SM2_P_Z) ” 
  &&  “ (0 <= Y_coords) ” 
  &&  “ (X_coords < SM2_P_Z) ” 
  &&  “ (0 <= X_coords) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (store_afpoint_fields dst_pre (mont_p (X_coords)) (mont_p (Y_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
.

Definition montg_is_apoint_zero_entail_wit_3 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (Y_coords < SM2_P_Z)) (PreH2 : (0 <= Y_coords)) (PreH3 : (X_coords < SM2_P_Z)) (PreH4 : (0 <= X_coords)) (PreH5 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) ,
  (store_afpoint_fields dst_pre (mont_p (X_coords)) (mont_p (Y_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (Y_coords < SM2_P_Z) ” 
  &&  “ (0 <= Y_coords) ” 
  &&  “ (X_coords < SM2_P_Z) ” 
  &&  “ (0 <= X_coords) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (store_fp &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (store_fp &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
.

Definition montg_is_apoint_zero_entail_wit_4 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (Y_coords < SM2_P_Z)) (PreH2 : (0 <= Y_coords)) (PreH3 : (X_coords < SM2_P_Z)) (PreH4 : (0 <= X_coords)) (PreH5 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH6 : (x3 < U64_MOD)) (PreH7 : (0 <= x3)) (PreH8 : (x2 < U64_MOD)) (PreH9 : (0 <= x2)) (PreH10 : (x1 < U64_MOD)) (PreH11 : (0 <= x1)) (PreH12 : (x0 < U64_MOD)) (PreH13 : (0 <= x0)) ,
  (store_fp &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (store_fp &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ ((mont_p (X_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_coords))) ” 
  &&  “ ((mont_p (Y_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_coords))) ” 
  &&  “ (Y_coords < SM2_P_Z) ” 
  &&  “ (0 <= Y_coords) ” 
  &&  “ (X_coords < SM2_P_Z) ” 
  &&  “ (0 <= X_coords) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
.

Definition montg_is_apoint_zero_entail_wit_5 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : ((mont_p (X_coords)) <> 0)) (PreH4 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH5 : (0 <= (mont_p (X_coords)))) (PreH6 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH7 : (0 <= (mont_p (Y_coords)))) (PreH8 : (Y_coords < SM2_P_Z)) (PreH9 : (0 <= Y_coords)) (PreH10 : (X_coords < SM2_P_Z)) (PreH11 : (0 <= X_coords)) (PreH12 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (store_u256_limbs (&((dst_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (X_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((mont_p (X_coords)) <> 0) ” 
  &&  “ ((mont_p (X_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_coords))) ” 
  &&  “ ((mont_p (Y_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_coords))) ” 
  &&  “ (Y_coords < SM2_P_Z) ” 
  &&  “ (0 <= Y_coords) ” 
  &&  “ (X_coords < SM2_P_Z) ” 
  &&  “ (0 <= X_coords) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
.

Definition montg_is_apoint_zero_entail_wit_6 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : ((mont_p (X_coords)) = 0)) (PreH4 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH5 : (0 <= (mont_p (X_coords)))) (PreH6 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH7 : (0 <= (mont_p (Y_coords)))) (PreH8 : (Y_coords < SM2_P_Z)) (PreH9 : (0 <= Y_coords)) (PreH10 : (X_coords < SM2_P_Z)) (PreH11 : (0 <= X_coords)) (PreH12 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (store_u256_limbs (&((dst_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (X_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (retval <> 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((mont_p (X_coords)) = 0) ” 
  &&  “ ((mont_p (X_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_coords))) ” 
  &&  “ ((mont_p (Y_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_coords))) ” 
  &&  “ (Y_coords < SM2_P_Z) ” 
  &&  “ (0 <= Y_coords) ” 
  &&  “ (X_coords < SM2_P_Z) ” 
  &&  “ (0 <= X_coords) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
.

Definition montg_is_apoint_zero_entail_wit_7 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Y_coords)) <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : ((mont_p (X_coords)) = 0)) (PreH7 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (X_coords)))) (PreH9 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (Y_coords)))) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (store_u256_limbs (&((dst_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Y_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Y_coords)) <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((mont_p (X_coords)) = 0) ” 
  &&  “ ((mont_p (X_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_coords))) ” 
  &&  “ ((mont_p (Y_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_coords))) ” 
  &&  “ (Y_coords < SM2_P_Z) ” 
  &&  “ (0 <= Y_coords) ” 
  &&  “ (X_coords < SM2_P_Z) ” 
  &&  “ (0 <= X_coords) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
.

Definition montg_is_apoint_zero_entail_wit_8 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Y_coords)) = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : ((mont_p (X_coords)) = 0)) (PreH7 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (X_coords)))) (PreH9 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (Y_coords)))) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (store_u256_limbs (&((dst_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Y_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((mont_p (Y_coords)) = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((mont_p (X_coords)) = 0) ” 
  &&  “ ((mont_p (X_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_coords))) ” 
  &&  “ ((mont_p (Y_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_coords))) ” 
  &&  “ (Y_coords < SM2_P_Z) ” 
  &&  “ (0 <= Y_coords) ” 
  &&  “ (X_coords < SM2_P_Z) ” 
  &&  “ (0 <= X_coords) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
.

Definition montg_is_apoint_zero_return_wit_1 := 
(
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Y_coords)) = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : ((mont_p (X_coords)) = 0)) (PreH7 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (X_coords)))) (PreH9 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (Y_coords)))) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
|--
  “ (1 = 1) ” 
  &&  “ (X_coords = 0) ” 
  &&  “ (Y_coords = 0) ”
  &&  (store_mont_afpoint_coords dst_pre X_coords Y_coords )
  **  (store_bn_zero )
) \/
(
forall (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Y_coords)) = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : ((mont_p (X_coords)) = 0)) (PreH7 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (X_coords)))) (PreH9 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (Y_coords)))) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
|--
  “ (Y_coords = 0) ” 
  &&  “ (X_coords = 0) ”
  &&  (store_bn_zero )
).

Definition montg_is_apoint_zero_return_wit_1_split_goal_1 := 
forall (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Y_coords)) = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : ((mont_p (X_coords)) = 0)) (PreH7 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (X_coords)))) (PreH9 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (Y_coords)))) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
|--
  “ (Y_coords = 0) ”
.

Definition montg_is_apoint_zero_return_wit_1_split_goal_2 := 
forall (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Y_coords)) = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : ((mont_p (X_coords)) = 0)) (PreH7 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (X_coords)))) (PreH9 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (Y_coords)))) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
|--
  “ (X_coords = 0) ”
.

Definition montg_is_apoint_zero_return_wit_1_split_goal_spatial := 
forall (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Y_coords)) = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : ((mont_p (X_coords)) = 0)) (PreH7 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (X_coords)))) (PreH9 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (Y_coords)))) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
|--
  (store_bn_zero )
.

Definition montg_is_apoint_zero_return_wit_2 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Y_coords)) <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : ((mont_p (X_coords)) = 0)) (PreH7 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (X_coords)))) (PreH9 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (Y_coords)))) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
|--
  (“ (0 = 0) ” 
  &&  “ (X_coords <> 0) ”
  &&  (store_mont_afpoint_coords dst_pre X_coords Y_coords )
  **  (store_bn_zero ))
  ||
  (“ (0 = 0) ” 
  &&  “ (Y_coords <> 0) ”
  &&  (store_mont_afpoint_coords dst_pre X_coords Y_coords )
  **  (store_bn_zero ))
.

Definition montg_is_apoint_zero_return_wit_3 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : ((mont_p (X_coords)) <> 0)) (PreH4 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH5 : (0 <= (mont_p (X_coords)))) (PreH6 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH7 : (0 <= (mont_p (Y_coords)))) (PreH8 : (Y_coords < SM2_P_Z)) (PreH9 : (0 <= Y_coords)) (PreH10 : (X_coords < SM2_P_Z)) (PreH11 : (0 <= X_coords)) (PreH12 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
|--
  (“ (0 = 0) ” 
  &&  “ (X_coords <> 0) ”
  &&  (store_mont_afpoint_coords dst_pre X_coords Y_coords )
  **  (store_bn_zero ))
  ||
  (“ (0 = 0) ” 
  &&  “ (Y_coords <> 0) ”
  &&  (store_mont_afpoint_coords dst_pre X_coords Y_coords )
  **  (store_bn_zero ))
.

Definition montg_is_apoint_zero_partial_solve_wit_1 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) ,
  (store_mont_afpoint_coords dst_pre X_coords Y_coords )
  **  (store_bn_zero )
|--
  (store_bn_zero )
  **  (store_mont_afpoint_coords dst_pre X_coords Y_coords )
.

Definition montg_is_apoint_zero_partial_solve_wit_2 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (X_coords)))) (PreH3 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (Y_coords)))) (PreH5 : (Y_coords < SM2_P_Z)) (PreH6 : (0 <= Y_coords)) (PreH7 : (X_coords < SM2_P_Z)) (PreH8 : (0 <= X_coords)) (PreH9 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ ((mont_p (X_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_coords))) ” 
  &&  “ ((mont_p (Y_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_coords))) ” 
  &&  “ (Y_coords < SM2_P_Z) ” 
  &&  “ (0 <= Y_coords) ” 
  &&  “ (X_coords < SM2_P_Z) ” 
  &&  “ (0 <= X_coords) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (store_u256_limbs (&((dst_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (X_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
.

Definition montg_is_apoint_zero_partial_solve_wit_3 := 
forall (dst_pre: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : ((mont_p (X_coords)) = 0)) (PreH4 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH5 : (0 <= (mont_p (X_coords)))) (PreH6 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH7 : (0 <= (mont_p (Y_coords)))) (PreH8 : (Y_coords < SM2_P_Z)) (PreH9 : (0 <= Y_coords)) (PreH10 : (X_coords < SM2_P_Z)) (PreH11 : (0 <= X_coords)) (PreH12 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_coords)) )
|--
  “ (retval <> 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((mont_p (X_coords)) = 0) ” 
  &&  “ ((mont_p (X_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_coords))) ” 
  &&  “ ((mont_p (Y_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_coords))) ” 
  &&  “ (Y_coords < SM2_P_Z) ” 
  &&  “ (0 <= Y_coords) ” 
  &&  “ (X_coords < SM2_P_Z) ” 
  &&  “ (0 <= X_coords) ” 
  &&  “ (0 = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (store_u256_limbs (&((dst_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Y_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_coords)) )
.

Definition montg_is_apoint_zero_which_implies_wit_1 := 
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

Definition montg_is_apoint_zero_derive_point_by_coords := 
forall (dst_pre: Z) (P_point: ec_point) ,
  (store_mont_afpoint dst_pre P_point )
  **  (store_bn_zero )
|--
EX (X_coords: Z) (Y_coords: Z) ,
  ((store_mont_afpoint_coords dst_pre X_coords Y_coords )
  **  (store_bn_zero ))
  **
  (((EX retval_2,
  “ (retval_2 = 0) ” 
  &&  “ (X_coords <> 0) ”
  &&  (store_mont_afpoint_coords dst_pre X_coords Y_coords )
  **  (store_bn_zero ))
  ||
  (EX retval_2,
  “ (retval_2 = 0) ” 
  &&  “ (Y_coords <> 0) ”
  &&  (store_mont_afpoint_coords dst_pre X_coords Y_coords )
  **  (store_bn_zero ))
  ||
  (EX retval_2,
  “ (retval_2 = 1) ” 
  &&  “ (X_coords = 0) ” 
  &&  “ (Y_coords = 0) ”
  &&  (store_mont_afpoint_coords dst_pre X_coords Y_coords )
  **  (store_bn_zero )))
  -*
  ((EX retval,
  “ (retval = 0) ” 
  &&  “ (P_point <> ECInfinity) ”
  &&  (store_mont_afpoint dst_pre P_point )
  **  (store_bn_zero ))
  ||
  (EX retval,
  “ (retval = 1) ” 
  &&  “ (P_point = ECInfinity) ”
  &&  (store_mont_afpoint dst_pre P_point )
  **  (store_bn_zero ))))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_montg_helper_views_Strategy_Correct.

Axiom proof_of_montg_is_apoint_zero_safety_wit_1 : montg_is_apoint_zero_safety_wit_1.
Axiom proof_of_montg_is_apoint_zero_safety_wit_2 : montg_is_apoint_zero_safety_wit_2.
Axiom proof_of_montg_is_apoint_zero_safety_wit_3 : montg_is_apoint_zero_safety_wit_3.
Axiom proof_of_montg_is_apoint_zero_safety_wit_4 : montg_is_apoint_zero_safety_wit_4.
Axiom proof_of_montg_is_apoint_zero_safety_wit_5 : montg_is_apoint_zero_safety_wit_5.
Axiom proof_of_montg_is_apoint_zero_safety_wit_6 : montg_is_apoint_zero_safety_wit_6.
Axiom proof_of_montg_is_apoint_zero_safety_wit_7 : montg_is_apoint_zero_safety_wit_7.
Axiom proof_of_montg_is_apoint_zero_safety_wit_8 : montg_is_apoint_zero_safety_wit_8.
Axiom proof_of_montg_is_apoint_zero_safety_wit_9 : montg_is_apoint_zero_safety_wit_9.
Axiom proof_of_montg_is_apoint_zero_safety_wit_10 : montg_is_apoint_zero_safety_wit_10.
Axiom proof_of_montg_is_apoint_zero_safety_wit_11 : montg_is_apoint_zero_safety_wit_11.
Axiom proof_of_montg_is_apoint_zero_entail_wit_1 : montg_is_apoint_zero_entail_wit_1.
Axiom proof_of_montg_is_apoint_zero_entail_wit_2 : montg_is_apoint_zero_entail_wit_2.
Axiom proof_of_montg_is_apoint_zero_entail_wit_3 : montg_is_apoint_zero_entail_wit_3.
Axiom proof_of_montg_is_apoint_zero_entail_wit_4 : montg_is_apoint_zero_entail_wit_4.
Axiom proof_of_montg_is_apoint_zero_entail_wit_5 : montg_is_apoint_zero_entail_wit_5.
Axiom proof_of_montg_is_apoint_zero_entail_wit_6 : montg_is_apoint_zero_entail_wit_6.
Axiom proof_of_montg_is_apoint_zero_entail_wit_7 : montg_is_apoint_zero_entail_wit_7.
Axiom proof_of_montg_is_apoint_zero_entail_wit_8 : montg_is_apoint_zero_entail_wit_8.
Axiom proof_of_montg_is_apoint_zero_return_wit_1 : montg_is_apoint_zero_return_wit_1.
Axiom proof_of_montg_is_apoint_zero_return_wit_2 : montg_is_apoint_zero_return_wit_2.
Axiom proof_of_montg_is_apoint_zero_return_wit_3 : montg_is_apoint_zero_return_wit_3.
Axiom proof_of_montg_is_apoint_zero_partial_solve_wit_1 : montg_is_apoint_zero_partial_solve_wit_1.
Axiom proof_of_montg_is_apoint_zero_partial_solve_wit_2 : montg_is_apoint_zero_partial_solve_wit_2.
Axiom proof_of_montg_is_apoint_zero_partial_solve_wit_3 : montg_is_apoint_zero_partial_solve_wit_3.
Axiom proof_of_montg_is_apoint_zero_which_implies_wit_1 : montg_is_apoint_zero_which_implies_wit_1.
Axiom proof_of_montg_is_apoint_zero_derive_point_by_coords : montg_is_apoint_zero_derive_point_by_coords.

End VC_Correct.
