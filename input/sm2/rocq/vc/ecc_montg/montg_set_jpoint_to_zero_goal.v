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

(*----- Function montg_set_jpoint_to_zero -----*)

Definition montg_set_jpoint_to_zero_safety_wit_1 := 
forall (dst_pre: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_set_jpoint_to_zero_safety_wit_2 := 
forall (dst_pre: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_set_jpoint_to_zero_safety_wit_3 := 
forall (dst_pre: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH2 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH3 : (x3 < U64_MOD)) (PreH4 : (0 <= x3)) (PreH5 : (x2 < U64_MOD)) (PreH6 : (0 <= x2)) (PreH7 : (x1 < U64_MOD)) (PreH8 : (0 <= x1)) (PreH9 : (x0 < U64_MOD)) (PreH10 : (0 <= x0)) ,
  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_set_jpoint_to_zero_safety_wit_4 := 
forall (dst_pre: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH2 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH3 : (x3 < U64_MOD)) (PreH4 : (0 <= x3)) (PreH5 : (x2 < U64_MOD)) (PreH6 : (0 <= x2)) (PreH7 : (x1 < U64_MOD)) (PreH8 : (0 <= x1)) (PreH9 : (x0 < U64_MOD)) (PreH10 : (0 <= x0)) ,
  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_set_jpoint_to_zero_safety_wit_5 := 
forall (dst_pre: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH2 : (retval = (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH3 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH4 : (x3 < U64_MOD)) (PreH5 : (0 <= x3)) (PreH6 : (x2 < U64_MOD)) (PreH7 : (0 <= x2)) (PreH8 : (x1 < U64_MOD)) (PreH9 : (0 <= x1)) (PreH10 : (x0 < U64_MOD)) (PreH11 : (0 <= x0)) ,
  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_set_jpoint_to_zero_safety_wit_6 := 
forall (dst_pre: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH2 : (retval = (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH3 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH4 : (x3 < U64_MOD)) (PreH5 : (0 <= x3)) (PreH6 : (x2 < U64_MOD)) (PreH7 : (0 <= x2)) (PreH8 : (x1 < U64_MOD)) (PreH9 : (0 <= x1)) (PreH10 : (x0 < U64_MOD)) (PreH11 : (0 <= x0)) ,
  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_set_jpoint_to_zero_entail_wit_1 := 
forall (dst_pre: Z) ,
  (store_u256_limbs ( &( "MONTG_ONE" ) ) MONTG_ONE_Z )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_set_jpoint_to_zero_return_wit_1 := 
(
forall (dst_pre: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH2 : (retval_2 = (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH3 : (retval = (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH4 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH5 : (x3 < U64_MOD)) (PreH6 : (0 <= x3)) (PreH7 : (x2 < U64_MOD)) (PreH8 : (0 <= x2)) (PreH9 : (x1 < U64_MOD)) (PreH10 : (0 <= x1)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) ,
  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
|--
  (store_montg_one )
  **  (store_mont_jpoint_coords dst_pre 1 1 0 )
) \/
(
forall (dst_pre: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH2 : (retval_2 = (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH3 : (retval = (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH4 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH5 : (x3 < U64_MOD)) (PreH6 : (0 <= x3)) (PreH7 : (x2 < U64_MOD)) (PreH8 : (0 <= x2)) (PreH9 : (x1 < U64_MOD)) (PreH10 : (0 <= x1)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) ,
  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) 0 )
  **  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
|--
  EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ ((mont_p (1)) = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ ((mont_p (1)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (1))) ” 
  &&  “ ((mont_p (1)) = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((mont_p (1)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (1))) ” 
  &&  “ ((mont_p (0)) = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (0)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (0))) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ”
  &&  (((&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_montg_one )
).

Definition montg_set_jpoint_to_zero_partial_solve_wit_1 := 
forall (dst_pre: Z) ,
  (store_montg_one )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  (store_montg_one )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_set_jpoint_to_zero_partial_solve_wit_2_pure := 
forall (dst_pre: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ ((sizeof(UINT64) * 4) = 32) ”
.

Definition montg_set_jpoint_to_zero_partial_solve_wit_2_aux := 
forall (dst_pre: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ ((sizeof(UINT64) * 4) = 32) ” 
  &&  “ (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (UInt64Array.undef_full (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_set_jpoint_to_zero_partial_solve_wit_2 := montg_set_jpoint_to_zero_partial_solve_wit_2_pure -> montg_set_jpoint_to_zero_partial_solve_wit_2_aux.

Definition montg_set_jpoint_to_zero_partial_solve_wit_3_pure := 
forall (dst_pre: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH2 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH3 : (x3 < U64_MOD)) (PreH4 : (0 <= x3)) (PreH5 : (x2 < U64_MOD)) (PreH6 : (0 <= x2)) (PreH7 : (x1 < U64_MOD)) (PreH8 : (0 <= x1)) (PreH9 : (x0 < U64_MOD)) (PreH10 : (0 <= x0)) ,
  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ ((sizeof(UINT64) * 4) = 32) ”
.

Definition montg_set_jpoint_to_zero_partial_solve_wit_3_aux := 
forall (dst_pre: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (PreH1 : (retval = (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH2 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH3 : (x3 < U64_MOD)) (PreH4 : (0 <= x3)) (PreH5 : (x2 < U64_MOD)) (PreH6 : (0 <= x2)) (PreH7 : (x1 < U64_MOD)) (PreH8 : (0 <= x1)) (PreH9 : (x0 < U64_MOD)) (PreH10 : (0 <= x0)) ,
  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ ((sizeof(UINT64) * 4) = 32) ” 
  &&  “ (retval = (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) ” 
  &&  “ (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (UInt64Array.undef_full (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_set_jpoint_to_zero_partial_solve_wit_3 := montg_set_jpoint_to_zero_partial_solve_wit_3_pure -> montg_set_jpoint_to_zero_partial_solve_wit_3_aux.

Definition montg_set_jpoint_to_zero_partial_solve_wit_4_pure := 
forall (dst_pre: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH2 : (retval = (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH3 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH4 : (x3 < U64_MOD)) (PreH5 : (0 <= x3)) (PreH6 : (x2 < U64_MOD)) (PreH7 : (0 <= x2)) (PreH8 : (x1 < U64_MOD)) (PreH9 : (0 <= x1)) (PreH10 : (x0 < U64_MOD)) (PreH11 : (0 <= x0)) ,
  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 = 0) ” 
  &&  “ ((sizeof(UINT64) * 4) = 32) ”
.

Definition montg_set_jpoint_to_zero_partial_solve_wit_4_aux := 
forall (dst_pre: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH2 : (retval = (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))) (PreH3 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH4 : (x3 < U64_MOD)) (PreH5 : (0 <= x3)) (PreH6 : (x2 < U64_MOD)) (PreH7 : (0 <= x2)) (PreH8 : (x1 < U64_MOD)) (PreH9 : (0 <= x1)) (PreH10 : (x0 < U64_MOD)) (PreH11 : (0 <= x0)) ,
  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 = 0) ” 
  &&  “ ((sizeof(UINT64) * 4) = 32) ” 
  &&  “ (retval_2 = (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) ” 
  &&  “ (retval = (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) ” 
  &&  “ (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (UInt64Array.undef_full (&((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256_limbs (&((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (u256_of_limbs (x0) (x1) (x2) (x3)) )
.

Definition montg_set_jpoint_to_zero_partial_solve_wit_4 := montg_set_jpoint_to_zero_partial_solve_wit_4_pure -> montg_set_jpoint_to_zero_partial_solve_wit_4_aux.

Definition montg_set_jpoint_to_zero_which_implies_wit_1 := 
(
  (store_montg_one )
|--
  (store_u256_limbs ( &( "MONTG_ONE" ) ) MONTG_ONE_Z )
) \/
(
  (store_montg_one )
|--
  EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Definition montg_set_jpoint_to_zero_derive_point_by_coords := 
forall (dst_pre: Z) ,
  (store_montg_one )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  ((store_montg_one )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 ))
  **
  (((store_montg_one )
  **  (store_mont_jpoint_coords dst_pre 1 1 0 ))
  -*
  ((store_montg_one )
  **  (store_mont_jpoint dst_pre ECInfinity )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include ecc_representation_Strategy_Correct.

Axiom proof_of_montg_set_jpoint_to_zero_safety_wit_1 : montg_set_jpoint_to_zero_safety_wit_1.
Axiom proof_of_montg_set_jpoint_to_zero_safety_wit_2 : montg_set_jpoint_to_zero_safety_wit_2.
Axiom proof_of_montg_set_jpoint_to_zero_safety_wit_3 : montg_set_jpoint_to_zero_safety_wit_3.
Axiom proof_of_montg_set_jpoint_to_zero_safety_wit_4 : montg_set_jpoint_to_zero_safety_wit_4.
Axiom proof_of_montg_set_jpoint_to_zero_safety_wit_5 : montg_set_jpoint_to_zero_safety_wit_5.
Axiom proof_of_montg_set_jpoint_to_zero_safety_wit_6 : montg_set_jpoint_to_zero_safety_wit_6.
Axiom proof_of_montg_set_jpoint_to_zero_entail_wit_1 : montg_set_jpoint_to_zero_entail_wit_1.
Axiom proof_of_montg_set_jpoint_to_zero_return_wit_1 : montg_set_jpoint_to_zero_return_wit_1.
Axiom proof_of_montg_set_jpoint_to_zero_partial_solve_wit_1 : montg_set_jpoint_to_zero_partial_solve_wit_1.
Axiom proof_of_montg_set_jpoint_to_zero_partial_solve_wit_2_pure : montg_set_jpoint_to_zero_partial_solve_wit_2_pure.
Axiom proof_of_montg_set_jpoint_to_zero_partial_solve_wit_2 : montg_set_jpoint_to_zero_partial_solve_wit_2.
Axiom proof_of_montg_set_jpoint_to_zero_partial_solve_wit_3_pure : montg_set_jpoint_to_zero_partial_solve_wit_3_pure.
Axiom proof_of_montg_set_jpoint_to_zero_partial_solve_wit_3 : montg_set_jpoint_to_zero_partial_solve_wit_3.
Axiom proof_of_montg_set_jpoint_to_zero_partial_solve_wit_4_pure : montg_set_jpoint_to_zero_partial_solve_wit_4_pure.
Axiom proof_of_montg_set_jpoint_to_zero_partial_solve_wit_4 : montg_set_jpoint_to_zero_partial_solve_wit_4.
Axiom proof_of_montg_set_jpoint_to_zero_which_implies_wit_1 : montg_set_jpoint_to_zero_which_implies_wit_1.
Axiom proof_of_montg_set_jpoint_to_zero_derive_point_by_coords : montg_set_jpoint_to_zero_derive_point_by_coords.

End VC_Correct.
