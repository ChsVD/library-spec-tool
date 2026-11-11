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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import inv_for_mul_mod_n_def.
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

(*----- Function inv_for_mul_mod_n -----*)

Definition inv_for_mul_mod_n_safety_wit_1_in_place := 
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_N_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = input_pre)) (PreH13 : (A_in_place <> 0)) ,
  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition inv_for_mul_mod_n_safety_wit_2_non_alias := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_N_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (A_non_alias <> 0)) ,
  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition inv_for_mul_mod_n_safety_wit_3_in_place := 
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_N_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = input_pre)) (PreH13 : (A_in_place <> 0)) ,
  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition inv_for_mul_mod_n_safety_wit_4_non_alias := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_N_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (A_non_alias <> 0)) ,
  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition inv_for_mul_mod_n_safety_wit_5_in_place := 
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_N_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = input_pre)) (PreH13 : (A_in_place <> 0)) ,
  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition inv_for_mul_mod_n_safety_wit_6_non_alias := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_N_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (A_non_alias <> 0)) ,
  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition inv_for_mul_mod_n_safety_wit_7_in_place := 
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_N_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = input_pre)) (PreH13 : (A_in_place <> 0)) ,
  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition inv_for_mul_mod_n_safety_wit_8_non_alias := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_N_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (A_non_alias <> 0)) ,
  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition inv_for_mul_mod_n_safety_wit_9_non_alias := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_N_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (A_non_alias <> 0)) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition inv_for_mul_mod_n_safety_wit_10_non_alias := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_N_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (A_non_alias <> 0)) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition inv_for_mul_mod_n_safety_wit_11_in_place := 
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_N_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = input_pre)) (PreH13 : (A_in_place <> 0)) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition inv_for_mul_mod_n_safety_wit_12_in_place := 
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_N_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = input_pre)) (PreH13 : (A_in_place <> 0)) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition inv_for_mul_mod_n_entail_wit_1_1_in_place := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (result_pre = input_pre)) (PreH2 : (A_in_place <> 0)) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn input_pre A_in_place )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  (“ (A_in_place < SM2_N_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = input_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (store_u256 input_pre A_in_place )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
  ||
  (“ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias <> 0) ”
  &&  (store_u256 input_pre A_non_alias )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
.

Definition inv_for_mul_mod_n_entail_wit_1_2_non_alias := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (A_non_alias <> 0)) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn input_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  (“ (A_in_place < SM2_N_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = input_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (store_u256 input_pre A_in_place )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
  ||
  (“ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias <> 0) ”
  &&  (store_u256 input_pre A_non_alias )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
.

Definition inv_for_mul_mod_n_entail_wit_2_1_in_place := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (A_in_place < SM2_N_Z)) (PreH2 : (0 <= A_in_place)) (PreH3 : (result_pre = input_pre)) (PreH4 : (A_in_place <> 0)) ,
  (store_u256 input_pre A_in_place )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_N_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = input_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias <> 0) ”
  &&  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
.

Definition inv_for_mul_mod_n_entail_wit_2_2_non_alias := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (A_non_alias < SM2_N_Z)) (PreH2 : (0 <= A_non_alias)) (PreH3 : (A_non_alias <> 0)) ,
  (store_u256 input_pre A_non_alias )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_N_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = input_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias <> 0) ”
  &&  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
.

Definition inv_for_mul_mod_n_entail_wit_3_1_non_alias := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Znon: Z) (K1non: Z) (Zin: Z) (K1in: Z) (PreH1 : (0 <= Znon)) (PreH2 : (Znon < SM2_N_Z)) (PreH3 : ((A_non_alias * Znon ) = (U256_MOD + (K1non * SM2_N_Z ) ))) (PreH4 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH5 : (x3 < U64_MOD)) (PreH6 : (0 <= x3)) (PreH7 : (x2 < U64_MOD)) (PreH8 : (0 <= x2)) (PreH9 : (x1 < U64_MOD)) (PreH10 : (0 <= x1)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (A_non_alias < SM2_N_Z)) (PreH14 : (0 <= A_non_alias)) (PreH15 : (A_non_alias <> 0)) ,
  (store_u256_limbs (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) A_non_alias )
  **  (store_u256_limbs (&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Znon )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (Znon = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (0 <= Znon) ” 
  &&  “ (Znon < SM2_N_Z) ” 
  &&  “ ((A_non_alias * Znon ) = (U256_MOD + (K1non * SM2_N_Z ) )) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias <> 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z) ,
  “ (Zin = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ ((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) ” 
  &&  “ (0 <= Zin) ” 
  &&  “ (Zin < SM2_N_Z) ” 
  &&  “ ((A_in_place * Zin ) = (U256_MOD + (K1in * SM2_N_Z ) )) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (A_in_place < SM2_N_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = input_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition inv_for_mul_mod_n_entail_wit_3_2_in_place := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (A_in_place: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (Znon: Z) (K1non: Z) (Zin: Z) (K1in: Z) (PreH1 : ((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))) (PreH2 : (0 <= Zin)) (PreH3 : (Zin < SM2_N_Z)) (PreH4 : ((A_in_place * Zin ) = (U256_MOD + (K1in * SM2_N_Z ) ))) (PreH5 : (A_in_place = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (A_in_place < SM2_N_Z)) (PreH15 : (0 <= A_in_place)) (PreH16 : (result_pre = input_pre)) (PreH17 : (A_in_place <> 0)) ,
  (store_u256_limbs (&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Zin )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (Znon = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (0 <= Znon) ” 
  &&  “ (Znon < SM2_N_Z) ” 
  &&  “ ((A_non_alias * Znon ) = (U256_MOD + (K1non * SM2_N_Z ) )) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias <> 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (Zin = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ ((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) ” 
  &&  “ (0 <= Zin) ” 
  &&  “ (Zin < SM2_N_Z) ” 
  &&  “ ((A_in_place * Zin ) = (U256_MOD + (K1in * SM2_N_Z ) )) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (A_in_place < SM2_N_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = input_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition inv_for_mul_mod_n_return_wit_1_non_alias := 
(
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Znon: Z) (K1non: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (R: Z) (K2: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_N_Z)) (PreH3 : ((R * U256_MOD ) = ((Znon * 1 ) + (K2 * SM2_N_Z ) ))) (PreH4 : (Znon = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH5 : (x3_3 < U64_MOD)) (PreH6 : (0 <= x3_3)) (PreH7 : (x2_3 < U64_MOD)) (PreH8 : (0 <= x2_3)) (PreH9 : (x1_3 < U64_MOD)) (PreH10 : (0 <= x1_3)) (PreH11 : (x0_3 < U64_MOD)) (PreH12 : (0 <= x0_3)) (PreH13 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (0 <= Znon)) (PreH23 : (Znon < SM2_N_Z)) (PreH24 : ((A_non_alias * Znon ) = (U256_MOD + (K1non * SM2_N_Z ) ))) (PreH25 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (A_non_alias < SM2_N_Z)) (PreH35 : (0 <= A_non_alias)) (PreH36 : (A_non_alias <> 0)) ,
  (store_fn result_pre R )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  EX (Ainv: Z) ,
  “ (0 <= Ainv) ” 
  &&  “ (Ainv < SM2_N_Z) ” 
  &&  “ ((Zmod ((A_non_alias * Ainv )) (SM2_N_Z)) = 1) ”
  &&  (store_fn input_pre A_non_alias )
  **  (store_fn result_pre Ainv )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
) \/
(
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Znon: Z) (K1non: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (R: Z) (K2: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_N_Z)) (PreH3 : ((R * U256_MOD ) = ((Znon * 1 ) + (K2 * SM2_N_Z ) ))) (PreH4 : (Znon = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH5 : (x3_3 < U64_MOD)) (PreH6 : (0 <= x3_3)) (PreH7 : (x2_3 < U64_MOD)) (PreH8 : (0 <= x2_3)) (PreH9 : (x1_3 < U64_MOD)) (PreH10 : (0 <= x1_3)) (PreH11 : (x0_3 < U64_MOD)) (PreH12 : (0 <= x0_3)) (PreH13 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (0 <= Znon)) (PreH23 : (Znon < SM2_N_Z)) (PreH24 : ((A_non_alias * Znon ) = (U256_MOD + (K1non * SM2_N_Z ) ))) (PreH25 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (A_non_alias < SM2_N_Z)) (PreH35 : (0 <= A_non_alias)) (PreH36 : (A_non_alias <> 0)) ,
  TT && emp 
|--
  “ ((Zmod ((A_non_alias * R )) (SM2_N_Z)) = 1) ”
  &&  emp
).

Definition inv_for_mul_mod_n_return_wit_1_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Znon: Z) (K1non: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (R: Z) (K2: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_N_Z)) (PreH3 : ((R * U256_MOD ) = ((Znon * 1 ) + (K2 * SM2_N_Z ) ))) (PreH4 : (Znon = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH5 : (x3_3 < U64_MOD)) (PreH6 : (0 <= x3_3)) (PreH7 : (x2_3 < U64_MOD)) (PreH8 : (0 <= x2_3)) (PreH9 : (x1_3 < U64_MOD)) (PreH10 : (0 <= x1_3)) (PreH11 : (x0_3 < U64_MOD)) (PreH12 : (0 <= x0_3)) (PreH13 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (0 <= Znon)) (PreH23 : (Znon < SM2_N_Z)) (PreH24 : ((A_non_alias * Znon ) = (U256_MOD + (K1non * SM2_N_Z ) ))) (PreH25 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (A_non_alias < SM2_N_Z)) (PreH35 : (0 <= A_non_alias)) (PreH36 : (A_non_alias <> 0)) ,
  ((Zmod ((A_non_alias * R )) (SM2_N_Z)) = 1)
.

Definition inv_for_mul_mod_n_return_wit_2_in_place := 
(
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Zin: Z) (K1in: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (R: Z) (K2: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_N_Z)) (PreH3 : ((R * U256_MOD ) = ((Zin * 1 ) + (K2 * SM2_N_Z ) ))) (PreH4 : (Zin = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : ((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))) (PreH14 : (0 <= Zin)) (PreH15 : (Zin < SM2_N_Z)) (PreH16 : ((A_in_place * Zin ) = (U256_MOD + (K1in * SM2_N_Z ) ))) (PreH17 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH18 : (x3 < U64_MOD)) (PreH19 : (0 <= x3)) (PreH20 : (x2 < U64_MOD)) (PreH21 : (0 <= x2)) (PreH22 : (x1 < U64_MOD)) (PreH23 : (0 <= x1)) (PreH24 : (x0 < U64_MOD)) (PreH25 : (0 <= x0)) (PreH26 : (A_in_place < SM2_N_Z)) (PreH27 : (0 <= A_in_place)) (PreH28 : (result_pre = input_pre)) (PreH29 : (A_in_place <> 0)) ,
  (store_fn result_pre R )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  EX (Ainv: Z) ,
  “ (result_pre = input_pre) ” 
  &&  “ (0 <= Ainv) ” 
  &&  “ (Ainv < SM2_N_Z) ” 
  &&  “ ((Zmod ((A_in_place * Ainv )) (SM2_N_Z)) = 1) ”
  &&  (store_fn result_pre Ainv )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
) \/
(
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Zin: Z) (K1in: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (R: Z) (K2: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_N_Z)) (PreH3 : ((R * U256_MOD ) = ((Zin * 1 ) + (K2 * SM2_N_Z ) ))) (PreH4 : (Zin = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : ((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))) (PreH14 : (0 <= Zin)) (PreH15 : (Zin < SM2_N_Z)) (PreH16 : ((A_in_place * Zin ) = (U256_MOD + (K1in * SM2_N_Z ) ))) (PreH17 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH18 : (x3 < U64_MOD)) (PreH19 : (0 <= x3)) (PreH20 : (x2 < U64_MOD)) (PreH21 : (0 <= x2)) (PreH22 : (x1 < U64_MOD)) (PreH23 : (0 <= x1)) (PreH24 : (x0 < U64_MOD)) (PreH25 : (0 <= x0)) (PreH26 : (A_in_place < SM2_N_Z)) (PreH27 : (0 <= A_in_place)) (PreH28 : (result_pre = input_pre)) (PreH29 : (A_in_place <> 0)) ,
  TT && emp 
|--
  “ ((Zmod ((A_in_place * R )) (SM2_N_Z)) = 1) ”
  &&  emp
).

Definition inv_for_mul_mod_n_return_wit_2_in_place_split_goal_1 := 
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Zin: Z) (K1in: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (R: Z) (K2: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_N_Z)) (PreH3 : ((R * U256_MOD ) = ((Zin * 1 ) + (K2 * SM2_N_Z ) ))) (PreH4 : (Zin = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : ((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))) (PreH14 : (0 <= Zin)) (PreH15 : (Zin < SM2_N_Z)) (PreH16 : ((A_in_place * Zin ) = (U256_MOD + (K1in * SM2_N_Z ) ))) (PreH17 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH18 : (x3 < U64_MOD)) (PreH19 : (0 <= x3)) (PreH20 : (x2 < U64_MOD)) (PreH21 : (0 <= x2)) (PreH22 : (x1 < U64_MOD)) (PreH23 : (0 <= x1)) (PreH24 : (x0 < U64_MOD)) (PreH25 : (0 <= x0)) (PreH26 : (A_in_place < SM2_N_Z)) (PreH27 : (0 <= A_in_place)) (PreH28 : (result_pre = input_pre)) (PreH29 : (A_in_place <> 0)) ,
  ((Zmod ((A_in_place * R )) (SM2_N_Z)) = 1)
.

Definition inv_for_mul_mod_n_partial_solve_wit_1_non_alias_pure := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_N_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (A_non_alias <> 0)) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ”
.

Definition inv_for_mul_mod_n_partial_solve_wit_1_non_alias_aux := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_N_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (A_non_alias <> 0)) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias <> 0) ”
  &&  (store_u256_limbs (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) A_non_alias )
  **  (UInt64Array.undef_full (&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
.

Definition inv_for_mul_mod_n_partial_solve_wit_1_non_alias := inv_for_mul_mod_n_partial_solve_wit_1_non_alias_pure -> inv_for_mul_mod_n_partial_solve_wit_1_non_alias_aux.

Definition inv_for_mul_mod_n_partial_solve_wit_2_in_place_pure := 
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_N_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = input_pre)) (PreH13 : (A_in_place <> 0)) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ ((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_N_Z) ”
.

Definition inv_for_mul_mod_n_partial_solve_wit_2_in_place_aux := 
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_N_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = input_pre)) (PreH13 : (A_in_place <> 0)) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ ((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_N_Z) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_N_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = input_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (store_u256_limbs (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) A_in_place )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
.

Definition inv_for_mul_mod_n_partial_solve_wit_2_in_place := inv_for_mul_mod_n_partial_solve_wit_2_in_place_pure -> inv_for_mul_mod_n_partial_solve_wit_2_in_place_aux.

Definition inv_for_mul_mod_n_partial_solve_wit_3_non_alias_pure := 
(
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Znon: Z) (K1non: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (PreH1 : (Znon = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH2 : (x3_3 < U64_MOD)) (PreH3 : (0 <= x3_3)) (PreH4 : (x2_3 < U64_MOD)) (PreH5 : (0 <= x2_3)) (PreH6 : (x1_3 < U64_MOD)) (PreH7 : (0 <= x1_3)) (PreH8 : (x0_3 < U64_MOD)) (PreH9 : (0 <= x0_3)) (PreH10 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (0 <= Znon)) (PreH20 : (Znon < SM2_N_Z)) (PreH21 : ((A_non_alias * Znon ) = (U256_MOD + (K1non * SM2_N_Z ) ))) (PreH22 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (A_non_alias < SM2_N_Z)) (PreH32 : (0 <= A_non_alias)) (PreH33 : (A_non_alias <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (result_pre = result_pre) ” 
  &&  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ”
) \/
(
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Znon: Z) (K1non: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (x0_3 <= UINT64_MAX)) (PreH6 : (x1_3 <= UINT64_MAX)) (PreH7 : (x2_3 <= UINT64_MAX)) (PreH8 : (x3_3 <= UINT64_MAX)) (PreH9 : (x0_2 >= 0)) (PreH10 : (x1_2 >= 0)) (PreH11 : (x2_2 >= 0)) (PreH12 : (x3_2 >= 0)) (PreH13 : (x0_3 >= 0)) (PreH14 : (x1_3 >= 0)) (PreH15 : (x2_3 >= 0)) (PreH16 : (x3_3 >= 0)) (PreH17 : (Znon = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH18 : (x3_3 < U64_MOD)) (PreH19 : (0 <= x3_3)) (PreH20 : (x2_3 < U64_MOD)) (PreH21 : (0 <= x2_3)) (PreH22 : (x1_3 < U64_MOD)) (PreH23 : (0 <= x1_3)) (PreH24 : (x0_3 < U64_MOD)) (PreH25 : (0 <= x0_3)) (PreH26 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH27 : (x3_2 < U64_MOD)) (PreH28 : (0 <= x3_2)) (PreH29 : (x2_2 < U64_MOD)) (PreH30 : (0 <= x2_2)) (PreH31 : (x1_2 < U64_MOD)) (PreH32 : (0 <= x1_2)) (PreH33 : (x0_2 < U64_MOD)) (PreH34 : (0 <= x0_2)) (PreH35 : (0 <= Znon)) (PreH36 : (Znon < SM2_N_Z)) (PreH37 : ((A_non_alias * Znon ) = (U256_MOD + (K1non * SM2_N_Z ) ))) (PreH38 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH39 : (x3 < U64_MOD)) (PreH40 : (0 <= x3)) (PreH41 : (x2 < U64_MOD)) (PreH42 : (0 <= x2)) (PreH43 : (x1 < U64_MOD)) (PreH44 : (0 <= x1)) (PreH45 : (x0 < U64_MOD)) (PreH46 : (0 <= x0)) (PreH47 : (A_non_alias < SM2_N_Z)) (PreH48 : (0 <= A_non_alias)) (PreH49 : (A_non_alias <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ”
).

Definition inv_for_mul_mod_n_partial_solve_wit_3_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Znon: Z) (K1non: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (x0_3 <= UINT64_MAX)) (PreH6 : (x1_3 <= UINT64_MAX)) (PreH7 : (x2_3 <= UINT64_MAX)) (PreH8 : (x3_3 <= UINT64_MAX)) (PreH9 : (x0_2 >= 0)) (PreH10 : (x1_2 >= 0)) (PreH11 : (x2_2 >= 0)) (PreH12 : (x3_2 >= 0)) (PreH13 : (x0_3 >= 0)) (PreH14 : (x1_3 >= 0)) (PreH15 : (x2_3 >= 0)) (PreH16 : (x3_3 >= 0)) (PreH17 : (Znon = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH18 : (x3_3 < U64_MOD)) (PreH19 : (0 <= x3_3)) (PreH20 : (x2_3 < U64_MOD)) (PreH21 : (0 <= x2_3)) (PreH22 : (x1_3 < U64_MOD)) (PreH23 : (0 <= x1_3)) (PreH24 : (x0_3 < U64_MOD)) (PreH25 : (0 <= x0_3)) (PreH26 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH27 : (x3_2 < U64_MOD)) (PreH28 : (0 <= x3_2)) (PreH29 : (x2_2 < U64_MOD)) (PreH30 : (0 <= x2_2)) (PreH31 : (x1_2 < U64_MOD)) (PreH32 : (0 <= x1_2)) (PreH33 : (x0_2 < U64_MOD)) (PreH34 : (0 <= x0_2)) (PreH35 : (0 <= Znon)) (PreH36 : (Znon < SM2_N_Z)) (PreH37 : ((A_non_alias * Znon ) = (U256_MOD + (K1non * SM2_N_Z ) ))) (PreH38 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH39 : (x3 < U64_MOD)) (PreH40 : (0 <= x3)) (PreH41 : (x2 < U64_MOD)) (PreH42 : (0 <= x2)) (PreH43 : (x1 < U64_MOD)) (PreH44 : (0 <= x1)) (PreH45 : (x0 < U64_MOD)) (PreH46 : (0 <= x0)) (PreH47 : (A_non_alias < SM2_N_Z)) (PreH48 : (0 <= A_non_alias)) (PreH49 : (A_non_alias <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ”
.

Definition inv_for_mul_mod_n_partial_solve_wit_3_non_alias_aux := 
forall (result_pre: Z) (input_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Znon: Z) (K1non: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (PreH1 : (Znon = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH2 : (x3_3 < U64_MOD)) (PreH3 : (0 <= x3_3)) (PreH4 : (x2_3 < U64_MOD)) (PreH5 : (0 <= x2_3)) (PreH6 : (x1_3 < U64_MOD)) (PreH7 : (0 <= x1_3)) (PreH8 : (x0_3 < U64_MOD)) (PreH9 : (0 <= x0_3)) (PreH10 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (0 <= Znon)) (PreH20 : (Znon < SM2_N_Z)) (PreH21 : ((A_non_alias * Znon ) = (U256_MOD + (K1non * SM2_N_Z ) ))) (PreH22 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (A_non_alias < SM2_N_Z)) (PreH32 : (0 <= A_non_alias)) (PreH33 : (A_non_alias <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
|--
  “ (result_pre = result_pre) ” 
  &&  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ” 
  &&  “ (Znon = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (0 <= Znon) ” 
  &&  “ (Znon < SM2_N_Z) ” 
  &&  “ ((A_non_alias * Znon ) = (U256_MOD + (K1non * SM2_N_Z ) )) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias <> 0) ”
  &&  (store_fn result_pre Znon )
  **  (store_fn ( &( "ONE" ) ) 1 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition inv_for_mul_mod_n_partial_solve_wit_3_non_alias := inv_for_mul_mod_n_partial_solve_wit_3_non_alias_pure -> inv_for_mul_mod_n_partial_solve_wit_3_non_alias_aux.

Definition inv_for_mul_mod_n_partial_solve_wit_4_in_place_pure := 
(
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Zin: Z) (K1in: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Zin = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : ((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))) (PreH11 : (0 <= Zin)) (PreH12 : (Zin < SM2_N_Z)) (PreH13 : ((A_in_place * Zin ) = (U256_MOD + (K1in * SM2_N_Z ) ))) (PreH14 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (A_in_place < SM2_N_Z)) (PreH24 : (0 <= A_in_place)) (PreH25 : (result_pre = input_pre)) (PreH26 : (A_in_place <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (result_pre = result_pre) ” 
  &&  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ”
) \/
(
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Zin: Z) (K1in: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (x0_2 >= 0)) (PreH6 : (x1_2 >= 0)) (PreH7 : (x2_2 >= 0)) (PreH8 : (x3_2 >= 0)) (PreH9 : (Zin = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : ((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))) (PreH19 : (0 <= Zin)) (PreH20 : (Zin < SM2_N_Z)) (PreH21 : ((A_in_place * Zin ) = (U256_MOD + (K1in * SM2_N_Z ) ))) (PreH22 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (A_in_place < SM2_N_Z)) (PreH32 : (0 <= A_in_place)) (PreH33 : (result_pre = input_pre)) (PreH34 : (A_in_place <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ”
).

Definition inv_for_mul_mod_n_partial_solve_wit_4_in_place_pure_split_goal_1 := 
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Zin: Z) (K1in: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (x0_2 >= 0)) (PreH6 : (x1_2 >= 0)) (PreH7 : (x2_2 >= 0)) (PreH8 : (x3_2 >= 0)) (PreH9 : (Zin = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : ((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))) (PreH19 : (0 <= Zin)) (PreH20 : (Zin < SM2_N_Z)) (PreH21 : ((A_in_place * Zin ) = (U256_MOD + (K1in * SM2_N_Z ) ))) (PreH22 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (A_in_place < SM2_N_Z)) (PreH32 : (0 <= A_in_place)) (PreH33 : (result_pre = input_pre)) (PreH34 : (A_in_place <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ”
.

Definition inv_for_mul_mod_n_partial_solve_wit_4_in_place_aux := 
forall (result_pre: Z) (input_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (Zin: Z) (K1in: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Zin = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : ((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))))) (PreH11 : (0 <= Zin)) (PreH12 : (Zin < SM2_N_Z)) (PreH13 : ((A_in_place * Zin ) = (U256_MOD + (K1in * SM2_N_Z ) ))) (PreH14 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (A_in_place < SM2_N_Z)) (PreH24 : (0 <= A_in_place)) (PreH25 : (result_pre = input_pre)) (PreH26 : (A_in_place <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
|--
  “ (result_pre = result_pre) ” 
  &&  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ” 
  &&  “ (Zin = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) = (&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) ” 
  &&  “ (0 <= Zin) ” 
  &&  “ (Zin < SM2_N_Z) ” 
  &&  “ ((A_in_place * Zin ) = (U256_MOD + (K1in * SM2_N_Z ) )) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_N_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = input_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (store_fn result_pre Zin )
  **  (store_fn ( &( "ONE" ) ) 1 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition inv_for_mul_mod_n_partial_solve_wit_4_in_place := inv_for_mul_mod_n_partial_solve_wit_4_in_place_pure -> inv_for_mul_mod_n_partial_solve_wit_4_in_place_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_inv_for_mul_mod_n_safety_wit_1_in_place : inv_for_mul_mod_n_safety_wit_1_in_place.
Axiom proof_of_inv_for_mul_mod_n_safety_wit_2_non_alias : inv_for_mul_mod_n_safety_wit_2_non_alias.
Axiom proof_of_inv_for_mul_mod_n_safety_wit_3_in_place : inv_for_mul_mod_n_safety_wit_3_in_place.
Axiom proof_of_inv_for_mul_mod_n_safety_wit_4_non_alias : inv_for_mul_mod_n_safety_wit_4_non_alias.
Axiom proof_of_inv_for_mul_mod_n_safety_wit_5_in_place : inv_for_mul_mod_n_safety_wit_5_in_place.
Axiom proof_of_inv_for_mul_mod_n_safety_wit_6_non_alias : inv_for_mul_mod_n_safety_wit_6_non_alias.
Axiom proof_of_inv_for_mul_mod_n_safety_wit_7_in_place : inv_for_mul_mod_n_safety_wit_7_in_place.
Axiom proof_of_inv_for_mul_mod_n_safety_wit_8_non_alias : inv_for_mul_mod_n_safety_wit_8_non_alias.
Axiom proof_of_inv_for_mul_mod_n_safety_wit_9_non_alias : inv_for_mul_mod_n_safety_wit_9_non_alias.
Axiom proof_of_inv_for_mul_mod_n_safety_wit_10_non_alias : inv_for_mul_mod_n_safety_wit_10_non_alias.
Axiom proof_of_inv_for_mul_mod_n_safety_wit_11_in_place : inv_for_mul_mod_n_safety_wit_11_in_place.
Axiom proof_of_inv_for_mul_mod_n_safety_wit_12_in_place : inv_for_mul_mod_n_safety_wit_12_in_place.
Axiom proof_of_inv_for_mul_mod_n_entail_wit_1_1_in_place : inv_for_mul_mod_n_entail_wit_1_1_in_place.
Axiom proof_of_inv_for_mul_mod_n_entail_wit_1_2_non_alias : inv_for_mul_mod_n_entail_wit_1_2_non_alias.
Axiom proof_of_inv_for_mul_mod_n_entail_wit_2_1_in_place : inv_for_mul_mod_n_entail_wit_2_1_in_place.
Axiom proof_of_inv_for_mul_mod_n_entail_wit_2_2_non_alias : inv_for_mul_mod_n_entail_wit_2_2_non_alias.
Axiom proof_of_inv_for_mul_mod_n_entail_wit_3_1_non_alias : inv_for_mul_mod_n_entail_wit_3_1_non_alias.
Axiom proof_of_inv_for_mul_mod_n_entail_wit_3_2_in_place : inv_for_mul_mod_n_entail_wit_3_2_in_place.
Axiom proof_of_inv_for_mul_mod_n_return_wit_1_non_alias : inv_for_mul_mod_n_return_wit_1_non_alias.
Axiom proof_of_inv_for_mul_mod_n_return_wit_2_in_place : inv_for_mul_mod_n_return_wit_2_in_place.
Axiom proof_of_inv_for_mul_mod_n_partial_solve_wit_1_non_alias_pure : inv_for_mul_mod_n_partial_solve_wit_1_non_alias_pure.
Axiom proof_of_inv_for_mul_mod_n_partial_solve_wit_1_non_alias : inv_for_mul_mod_n_partial_solve_wit_1_non_alias.
Axiom proof_of_inv_for_mul_mod_n_partial_solve_wit_2_in_place_pure : inv_for_mul_mod_n_partial_solve_wit_2_in_place_pure.
Axiom proof_of_inv_for_mul_mod_n_partial_solve_wit_2_in_place : inv_for_mul_mod_n_partial_solve_wit_2_in_place.
Axiom proof_of_inv_for_mul_mod_n_partial_solve_wit_3_non_alias_pure : inv_for_mul_mod_n_partial_solve_wit_3_non_alias_pure.
Axiom proof_of_inv_for_mul_mod_n_partial_solve_wit_3_non_alias : inv_for_mul_mod_n_partial_solve_wit_3_non_alias.
Axiom proof_of_inv_for_mul_mod_n_partial_solve_wit_4_in_place_pure : inv_for_mul_mod_n_partial_solve_wit_4_in_place_pure.
Axiom proof_of_inv_for_mul_mod_n_partial_solve_wit_4_in_place : inv_for_mul_mod_n_partial_solve_wit_4_in_place.

End VC_Correct.
