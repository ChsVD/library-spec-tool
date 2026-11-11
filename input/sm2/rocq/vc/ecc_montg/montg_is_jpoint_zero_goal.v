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

(*----- Function montg_is_jpoint_zero -----*)

Definition montg_is_jpoint_zero_safety_wit_1 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (X_coords)))) (PreH3 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (Y_coords)))) (PreH5 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Z_coords)))) (PreH7 : (Z_coords < SM2_P_Z)) (PreH8 : (0 <= Z_coords)) (PreH9 : (Y_coords < SM2_P_Z)) (PreH10 : (0 <= Y_coords)) (PreH11 : (X_coords < SM2_P_Z)) (PreH12 : (0 <= X_coords)) (PreH13 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_is_jpoint_zero_safety_wit_2 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (X_coords)))) (PreH3 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (Y_coords)))) (PreH5 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Z_coords)))) (PreH7 : (Z_coords < SM2_P_Z)) (PreH8 : (0 <= Z_coords)) (PreH9 : (Y_coords < SM2_P_Z)) (PreH10 : (0 <= Y_coords)) (PreH11 : (X_coords < SM2_P_Z)) (PreH12 : (0 <= X_coords)) (PreH13 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_is_jpoint_zero_safety_wit_3 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((mont_p (Z_coords)) = 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval = 0)) ,
  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ False ”
.

Definition montg_is_jpoint_zero_safety_wit_4 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((mont_p (Z_coords)) <> 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval <> 0)) ,
  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ False ”
.

Definition montg_is_jpoint_zero_safety_wit_5 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((mont_p (Z_coords)) = 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval <> 0)) ,
  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_is_jpoint_zero_safety_wit_6 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((mont_p (Z_coords)) <> 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval = 0)) ,
  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_is_jpoint_zero_entail_wit_1 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) ,
  (store_u256_limbs ( &( "BN_ZERO" ) ) 0 )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (store_mont_jpoint_coords dst_pre X_coords Y_coords Z_coords )
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
  **  (store_mont_jpoint_coords dst_pre X_coords Y_coords Z_coords )
.

Definition montg_is_jpoint_zero_entail_wit_2 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (store_mont_jpoint_coords dst_pre X_coords Y_coords Z_coords )
|--
  “ (Z_coords < SM2_P_Z) ” 
  &&  “ (0 <= Z_coords) ” 
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
  &&  (store_jpoint_fields dst_pre (mont_p (X_coords)) (mont_p (Y_coords)) (mont_p (Z_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
.

Definition montg_is_jpoint_zero_entail_wit_3 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (Z_coords < SM2_P_Z)) (PreH2 : (0 <= Z_coords)) (PreH3 : (Y_coords < SM2_P_Z)) (PreH4 : (0 <= Y_coords)) (PreH5 : (X_coords < SM2_P_Z)) (PreH6 : (0 <= X_coords)) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) ,
  (store_jpoint_fields dst_pre (mont_p (X_coords)) (mont_p (Y_coords)) (mont_p (Z_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (Z_coords < SM2_P_Z) ” 
  &&  “ (0 <= Z_coords) ” 
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
  &&  (store_fp &((dst_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_coords)) )
  **  (store_fp &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (store_fp &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
.

Definition montg_is_jpoint_zero_entail_wit_4 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (Z_coords < SM2_P_Z)) (PreH2 : (0 <= Z_coords)) (PreH3 : (Y_coords < SM2_P_Z)) (PreH4 : (0 <= Y_coords)) (PreH5 : (X_coords < SM2_P_Z)) (PreH6 : (0 <= X_coords)) (PreH7 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH8 : (x3 < U64_MOD)) (PreH9 : (0 <= x3)) (PreH10 : (x2 < U64_MOD)) (PreH11 : (0 <= x2)) (PreH12 : (x1 < U64_MOD)) (PreH13 : (0 <= x1)) (PreH14 : (x0 < U64_MOD)) (PreH15 : (0 <= x0)) ,
  (store_fp &((dst_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_coords)) )
  **  (store_fp &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (store_fp &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
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
  &&  “ ((mont_p (Z_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Z_coords))) ” 
  &&  “ (Z_coords < SM2_P_Z) ” 
  &&  “ (0 <= Z_coords) ” 
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
  &&  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
.

Definition montg_is_jpoint_zero_entail_wit_5_1 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((mont_p (Z_coords)) <> 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval = 0)) ,
  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
|--
  “ (retval = 0) ” 
  &&  “ ((mont_p (Z_coords)) <> 0) ” 
  &&  “ ((mont_p (X_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_coords))) ” 
  &&  “ ((mont_p (Y_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_coords))) ” 
  &&  “ ((mont_p (Z_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Z_coords))) ” 
  &&  “ (Z_coords < SM2_P_Z) ” 
  &&  “ (0 <= Z_coords) ” 
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
  &&  “ (retval = 0) ”
  &&  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
.

Definition montg_is_jpoint_zero_entail_wit_5_2 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : ((mont_p (Z_coords)) = 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval_2 = 0)) ,
  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
|--
  EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ ((mont_p (Z_coords)) <> 0) ” 
  &&  “ ((mont_p (X_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_coords))) ” 
  &&  “ ((mont_p (Y_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_coords))) ” 
  &&  “ ((mont_p (Z_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Z_coords))) ” 
  &&  “ (Z_coords < SM2_P_Z) ” 
  &&  “ (0 <= Z_coords) ” 
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
  &&  “ (retval = 0) ”
  &&  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
.

Definition montg_is_jpoint_zero_entail_wit_6_1 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : ((mont_p (Z_coords)) <> 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval_2 <> 0)) ,
  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
|--
  EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ ((mont_p (Z_coords)) = 0) ” 
  &&  “ ((mont_p (X_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_coords))) ” 
  &&  “ ((mont_p (Y_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_coords))) ” 
  &&  “ ((mont_p (Z_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Z_coords))) ” 
  &&  “ (Z_coords < SM2_P_Z) ” 
  &&  “ (0 <= Z_coords) ” 
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
  &&  “ (retval <> 0) ”
  &&  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
.

Definition montg_is_jpoint_zero_entail_wit_6_2 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((mont_p (Z_coords)) = 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval <> 0)) ,
  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
|--
  “ (retval = 1) ” 
  &&  “ ((mont_p (Z_coords)) = 0) ” 
  &&  “ ((mont_p (X_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_coords))) ” 
  &&  “ ((mont_p (Y_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_coords))) ” 
  &&  “ ((mont_p (Z_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Z_coords))) ” 
  &&  “ (Z_coords < SM2_P_Z) ” 
  &&  “ (0 <= Z_coords) ” 
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
  &&  “ (retval <> 0) ”
  &&  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
.

Definition montg_is_jpoint_zero_entail_wit_7 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((mont_p (Z_coords)) = 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval <> 0)) ,
  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (retval = 1) ” 
  &&  “ ((mont_p (Z_coords)) = 0) ” 
  &&  “ ((mont_p (X_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_coords))) ” 
  &&  “ ((mont_p (Y_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_coords))) ” 
  &&  “ ((mont_p (Z_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Z_coords))) ” 
  &&  “ (Z_coords < SM2_P_Z) ” 
  &&  “ (0 <= Z_coords) ” 
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
  &&  “ (retval <> 0) ”
  &&  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
.

Definition montg_is_jpoint_zero_entail_wit_8 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((mont_p (Z_coords)) <> 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval = 0)) ,
  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (retval = 0) ” 
  &&  “ ((mont_p (Z_coords)) <> 0) ” 
  &&  “ ((mont_p (X_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_coords))) ” 
  &&  “ ((mont_p (Y_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_coords))) ” 
  &&  “ ((mont_p (Z_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Z_coords))) ” 
  &&  “ (Z_coords < SM2_P_Z) ” 
  &&  “ (0 <= Z_coords) ” 
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
  &&  “ (retval = 0) ”
  &&  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
.

Definition montg_is_jpoint_zero_return_wit_1 := 
(
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((mont_p (Z_coords)) <> 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval = 0)) ,
  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
|--
  “ (0 = 0) ” 
  &&  “ (Z_coords <> 0) ”
  &&  (store_mont_jpoint_coords dst_pre X_coords Y_coords Z_coords )
  **  (store_bn_zero )
) \/
(
forall (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((mont_p (Z_coords)) <> 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval = 0)) ,
  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
|--
  “ (Z_coords <> 0) ”
  &&  (store_bn_zero )
).

Definition montg_is_jpoint_zero_return_wit_1_split_goal_1 := 
forall (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((mont_p (Z_coords)) <> 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval = 0)) ,
  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
|--
  “ (Z_coords <> 0) ”
.

Definition montg_is_jpoint_zero_return_wit_1_split_goal_spatial := 
forall (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((mont_p (Z_coords)) <> 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval = 0)) ,
  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
|--
  (store_bn_zero )
.

Definition montg_is_jpoint_zero_return_wit_2 := 
(
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((mont_p (Z_coords)) = 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval <> 0)) ,
  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
|--
  “ (1 = 1) ” 
  &&  “ (Z_coords = 0) ”
  &&  (store_mont_jpoint_coords dst_pre X_coords Y_coords Z_coords )
  **  (store_bn_zero )
) \/
(
forall (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((mont_p (Z_coords)) = 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval <> 0)) ,
  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
|--
  “ (Z_coords = 0) ”
  &&  (store_bn_zero )
).

Definition montg_is_jpoint_zero_return_wit_2_split_goal_1 := 
forall (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((mont_p (Z_coords)) = 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval <> 0)) ,
  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
|--
  “ (Z_coords = 0) ”
.

Definition montg_is_jpoint_zero_return_wit_2_split_goal_spatial := 
forall (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((mont_p (Z_coords)) = 0)) (PreH3 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (X_coords)))) (PreH5 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Y_coords)))) (PreH7 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (Z_coords)))) (PreH9 : (Z_coords < SM2_P_Z)) (PreH10 : (0 <= Z_coords)) (PreH11 : (Y_coords < SM2_P_Z)) (PreH12 : (0 <= Y_coords)) (PreH13 : (X_coords < SM2_P_Z)) (PreH14 : (0 <= X_coords)) (PreH15 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (retval <> 0)) ,
  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
|--
  (store_bn_zero )
.

Definition montg_is_jpoint_zero_partial_solve_wit_1 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) ,
  (store_mont_jpoint_coords dst_pre X_coords Y_coords Z_coords )
  **  (store_bn_zero )
|--
  (store_bn_zero )
  **  (store_mont_jpoint_coords dst_pre X_coords Y_coords Z_coords )
.

Definition montg_is_jpoint_zero_partial_solve_wit_2 := 
forall (dst_pre: Z) (Z_coords: Z) (Y_coords: Z) (X_coords: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((mont_p (X_coords)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (X_coords)))) (PreH3 : ((mont_p (Y_coords)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (Y_coords)))) (PreH5 : ((mont_p (Z_coords)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (Z_coords)))) (PreH7 : (Z_coords < SM2_P_Z)) (PreH8 : (0 <= Z_coords)) (PreH9 : (Y_coords < SM2_P_Z)) (PreH10 : (0 <= Y_coords)) (PreH11 : (X_coords < SM2_P_Z)) (PreH12 : (0 <= X_coords)) (PreH13 : (0 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) ,
  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_coords)) )
  **  (((( &( "BN_ZERO" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "BN_ZERO" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "BN_ZERO" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ ((mont_p (X_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_coords))) ” 
  &&  “ ((mont_p (Y_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_coords))) ” 
  &&  “ ((mont_p (Z_coords)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Z_coords))) ” 
  &&  “ (Z_coords < SM2_P_Z) ” 
  &&  “ (0 <= Z_coords) ” 
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
  &&  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (Z_coords)) )
  **  (store_u256_limbs (( &( "BN_ZERO" ) ) + (0 * sizeof(UINT64))) 0 )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "x") (mont_p (X_coords)) )
  **  (store_u256 &((dst_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_coords)) )
.

Definition montg_is_jpoint_zero_which_implies_wit_1 := 
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

Definition montg_is_jpoint_zero_derive_point_by_coords := 
forall (dst_pre: Z) (P_point: ec_point) ,
  (store_mont_jpoint dst_pre P_point )
  **  (store_bn_zero )
|--
EX (X_coords: Z) (Y_coords: Z) (Z_coords: Z) ,
  ((store_mont_jpoint_coords dst_pre X_coords Y_coords Z_coords )
  **  (store_bn_zero ))
  **
  (((EX retval_2,
  “ (retval_2 = 0) ” 
  &&  “ (Z_coords <> 0) ”
  &&  (store_mont_jpoint_coords dst_pre X_coords Y_coords Z_coords )
  **  (store_bn_zero ))
  ||
  (EX retval_2,
  “ (retval_2 = 1) ” 
  &&  “ (Z_coords = 0) ”
  &&  (store_mont_jpoint_coords dst_pre X_coords Y_coords Z_coords )
  **  (store_bn_zero )))
  -*
  ((EX retval,
  “ (retval = 0) ” 
  &&  “ (P_point <> ECInfinity) ”
  &&  (store_mont_jpoint dst_pre P_point )
  **  (store_bn_zero ))
  ||
  (EX retval,
  “ (retval = 1) ” 
  &&  “ (P_point = ECInfinity) ”
  &&  (store_mont_jpoint dst_pre P_point )
  **  (store_bn_zero ))))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_montg_helper_views_Strategy_Correct.

Axiom proof_of_montg_is_jpoint_zero_safety_wit_1 : montg_is_jpoint_zero_safety_wit_1.
Axiom proof_of_montg_is_jpoint_zero_safety_wit_2 : montg_is_jpoint_zero_safety_wit_2.
Axiom proof_of_montg_is_jpoint_zero_safety_wit_3 : montg_is_jpoint_zero_safety_wit_3.
Axiom proof_of_montg_is_jpoint_zero_safety_wit_4 : montg_is_jpoint_zero_safety_wit_4.
Axiom proof_of_montg_is_jpoint_zero_safety_wit_5 : montg_is_jpoint_zero_safety_wit_5.
Axiom proof_of_montg_is_jpoint_zero_safety_wit_6 : montg_is_jpoint_zero_safety_wit_6.
Axiom proof_of_montg_is_jpoint_zero_entail_wit_1 : montg_is_jpoint_zero_entail_wit_1.
Axiom proof_of_montg_is_jpoint_zero_entail_wit_2 : montg_is_jpoint_zero_entail_wit_2.
Axiom proof_of_montg_is_jpoint_zero_entail_wit_3 : montg_is_jpoint_zero_entail_wit_3.
Axiom proof_of_montg_is_jpoint_zero_entail_wit_4 : montg_is_jpoint_zero_entail_wit_4.
Axiom proof_of_montg_is_jpoint_zero_entail_wit_5_1 : montg_is_jpoint_zero_entail_wit_5_1.
Axiom proof_of_montg_is_jpoint_zero_entail_wit_5_2 : montg_is_jpoint_zero_entail_wit_5_2.
Axiom proof_of_montg_is_jpoint_zero_entail_wit_6_1 : montg_is_jpoint_zero_entail_wit_6_1.
Axiom proof_of_montg_is_jpoint_zero_entail_wit_6_2 : montg_is_jpoint_zero_entail_wit_6_2.
Axiom proof_of_montg_is_jpoint_zero_entail_wit_7 : montg_is_jpoint_zero_entail_wit_7.
Axiom proof_of_montg_is_jpoint_zero_entail_wit_8 : montg_is_jpoint_zero_entail_wit_8.
Axiom proof_of_montg_is_jpoint_zero_return_wit_1 : montg_is_jpoint_zero_return_wit_1.
Axiom proof_of_montg_is_jpoint_zero_return_wit_2 : montg_is_jpoint_zero_return_wit_2.
Axiom proof_of_montg_is_jpoint_zero_partial_solve_wit_1 : montg_is_jpoint_zero_partial_solve_wit_1.
Axiom proof_of_montg_is_jpoint_zero_partial_solve_wit_2 : montg_is_jpoint_zero_partial_solve_wit_2.
Axiom proof_of_montg_is_jpoint_zero_which_implies_wit_1 : montg_is_jpoint_zero_which_implies_wit_1.
Axiom proof_of_montg_is_jpoint_zero_derive_point_by_coords : montg_is_jpoint_zero_derive_point_by_coords.

End VC_Correct.
