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
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.

(*----- Function mod_n -----*)

Definition mod_n_safety_wit_1_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (result_pre <> a_pre)) (PreH2 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH3 : (x3 < U64_MOD)) (PreH4 : (0 <= x3)) (PreH5 : (x2 < U64_MOD)) (PreH6 : (0 <= x2)) (PreH7 : (x1 < U64_MOD)) (PreH8 : (0 <= x1)) (PreH9 : (x0 < U64_MOD)) (PreH10 : (0 <= x0)) (PreH11 : (result_pre = a_pre)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  “ False ”
.

Definition mod_n_safety_wit_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH3 : (x3 < U64_MOD)) (PreH4 : (0 <= x3)) (PreH5 : (x2 < U64_MOD)) (PreH6 : (0 <= x2)) (PreH7 : (x1 < U64_MOD)) (PreH8 : (0 <= x1)) (PreH9 : (x0 < U64_MOD)) (PreH10 : (0 <= x0)) (PreH11 : (result_pre <> a_pre)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  “ False ”
.

Definition mod_n_safety_wit_3_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH6 : (x3_3 < U64_MOD)) (PreH7 : (0 <= x3_3)) (PreH8 : (x2_3 < U64_MOD)) (PreH9 : (0 <= x2_3)) (PreH10 : (x1_3 < U64_MOD)) (PreH11 : (0 <= x1_3)) (PreH12 : (x0_3 < U64_MOD)) (PreH13 : (0 <= x0_3)) (PreH14 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH15 : (x3_2 < U64_MOD)) (PreH16 : (0 <= x3_2)) (PreH17 : (x2_2 < U64_MOD)) (PreH18 : (0 <= x2_2)) (PreH19 : (x1_2 < U64_MOD)) (PreH20 : (0 <= x1_2)) (PreH21 : (x0_2 < U64_MOD)) (PreH22 : (0 <= x0_2)) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (result_pre <> a_pre)) (PreH33 : (0 <= A_non_alias)) (PreH34 : (A_non_alias < U256_MOD)) (PreH35 : (retval = 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ False ”
.

Definition mod_n_safety_wit_4_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (result_pre = a_pre)) (PreH24 : (0 <= A_in_place)) (PreH25 : (A_in_place < U256_MOD)) (PreH26 : (retval = 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ False ”
.

Definition mod_n_safety_wit_5_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH6 : (x3_3 < U64_MOD)) (PreH7 : (0 <= x3_3)) (PreH8 : (x2_3 < U64_MOD)) (PreH9 : (0 <= x2_3)) (PreH10 : (x1_3 < U64_MOD)) (PreH11 : (0 <= x1_3)) (PreH12 : (x0_3 < U64_MOD)) (PreH13 : (0 <= x0_3)) (PreH14 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH15 : (x3_2 < U64_MOD)) (PreH16 : (0 <= x3_2)) (PreH17 : (x2_2 < U64_MOD)) (PreH18 : (0 <= x2_2)) (PreH19 : (x1_2 < U64_MOD)) (PreH20 : (0 <= x1_2)) (PreH21 : (x0_2 < U64_MOD)) (PreH22 : (0 <= x0_2)) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (result_pre <> a_pre)) (PreH33 : (0 <= A_non_alias)) (PreH34 : (A_non_alias < U256_MOD)) (PreH35 : (retval <> 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ False ”
.

Definition mod_n_safety_wit_6_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (result_pre = a_pre)) (PreH24 : (0 <= A_in_place)) (PreH25 : (A_in_place < U256_MOD)) (PreH26 : (retval <> 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ False ”
.

Definition mod_n_entail_wit_1_1_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_in_place )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
.

Definition mod_n_entail_wit_1_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (result_pre <> a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (result_pre <> a_pre) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
.

Definition mod_n_entail_wit_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (result_pre <> a_pre)) (PreH2 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH3 : (x3 < U64_MOD)) (PreH4 : (0 <= x3)) (PreH5 : (x2 < U64_MOD)) (PreH6 : (0 <= x2)) (PreH7 : (x1 < U64_MOD)) (PreH8 : (0 <= x1)) (PreH9 : (x0 < U64_MOD)) (PreH10 : (0 <= x0)) (PreH11 : (result_pre <> a_pre)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  “ (result_pre <> a_pre) ”
  &&  (store_u256 a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
.

Definition mod_n_entail_wit_3_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (result_pre <> a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre <> a_pre) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
.

Definition mod_n_entail_wit_4_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (result_pre <> a_pre)) ,
  (UInt64Array.full &((result_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  “ (result_pre <> a_pre) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias < U256_MOD) ”
  &&  (store_u256 a_pre A_non_alias )
  **  (store_u256 result_pre A_non_alias )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (result_pre <> a_pre)) ,
  TT && emp 
|--
  “ (A_non_alias < U256_MOD) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = A_non_alias) ” 
  &&  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = A_non_alias) ”
  &&  emp
).

Definition mod_n_entail_wit_4_non_alias_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (result_pre <> a_pre)) ,
  (A_non_alias < U256_MOD)
.

Definition mod_n_entail_wit_4_non_alias_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (result_pre <> a_pre)) ,
  (0 <= A_non_alias)
.

Definition mod_n_entail_wit_4_non_alias_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (result_pre <> a_pre)) ,
  ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = A_non_alias)
.

Definition mod_n_entail_wit_4_non_alias_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (result_pre <> a_pre)) ,
  ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = A_non_alias)
.

Definition mod_n_entail_wit_5_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH3 : (x3 < U64_MOD)) (PreH4 : (0 <= x3)) (PreH5 : (x2 < U64_MOD)) (PreH6 : (0 <= x2)) (PreH7 : (x1 < U64_MOD)) (PreH8 : (0 <= x1)) (PreH9 : (x0 < U64_MOD)) (PreH10 : (0 <= x0)) (PreH11 : (result_pre = a_pre)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (A_in_place < U256_MOD) ”
  &&  (store_u256 result_pre A_in_place )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 >= 0)) (PreH6 : (x1 >= 0)) (PreH7 : (x2 >= 0)) (PreH8 : (x3 >= 0)) (PreH9 : (result_pre = a_pre)) (PreH10 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = a_pre)) ,
  TT && emp 
|--
  “ (A_in_place < U256_MOD) ” 
  &&  “ (0 <= A_in_place) ”
  &&  emp
).

Definition mod_n_entail_wit_5_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 >= 0)) (PreH6 : (x1 >= 0)) (PreH7 : (x2 >= 0)) (PreH8 : (x3 >= 0)) (PreH9 : (result_pre = a_pre)) (PreH10 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = a_pre)) ,
  (A_in_place < U256_MOD)
.

Definition mod_n_entail_wit_5_in_place_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 >= 0)) (PreH6 : (x1 >= 0)) (PreH7 : (x2 >= 0)) (PreH8 : (x3 >= 0)) (PreH9 : (result_pre = a_pre)) (PreH10 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = a_pre)) ,
  (0 <= A_in_place)
.

Definition mod_n_entail_wit_6_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (result_pre <> a_pre)) (PreH2 : (0 <= A_non_alias)) (PreH3 : (A_non_alias < U256_MOD)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (store_u256 result_pre A_non_alias )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  “ (result_pre <> a_pre) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias < U256_MOD) ”
  &&  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (store_u256 result_pre A_non_alias )
  **  (store_sm2_rhon )
.

Definition mod_n_entail_wit_6_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= A_in_place)) (PreH3 : (A_in_place < U256_MOD)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 result_pre A_in_place )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (A_in_place < U256_MOD) ”
  &&  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 result_pre A_in_place )
  **  (store_sm2_rhon )
.

Definition mod_n_entail_wit_7_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (result_pre <> a_pre)) (PreH2 : (0 <= A_non_alias)) (PreH3 : (A_non_alias < U256_MOD)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (store_u256 result_pre A_non_alias )
  **  (store_sm2_rhon )
|--
  “ (result_pre <> a_pre) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias < U256_MOD) ”
  &&  (store_u256 ( &( "SM2_rhoN" ) ) SM2_RHON_Z )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (store_u256 result_pre A_non_alias )
.

Definition mod_n_entail_wit_7_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= A_in_place)) (PreH3 : (A_in_place < U256_MOD)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 result_pre A_in_place )
  **  (store_sm2_rhon )
|--
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (A_in_place < U256_MOD) ”
  &&  (store_u256 ( &( "SM2_rhoN" ) ) SM2_RHON_Z )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 result_pre A_in_place )
.

Definition mod_n_entail_wit_8_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (result_pre <> a_pre)) (PreH2 : (0 <= A_non_alias)) (PreH3 : (A_non_alias < U256_MOD)) ,
  (store_u256 ( &( "SM2_rhoN" ) ) SM2_RHON_Z )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (store_u256 result_pre A_non_alias )
|--
  EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
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
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre <> a_pre) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias < U256_MOD) ”
  &&  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
.

Definition mod_n_entail_wit_8_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= A_in_place)) (PreH3 : (A_in_place < U256_MOD)) ,
  (store_u256 ( &( "SM2_rhoN" ) ) SM2_RHON_Z )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 result_pre A_in_place )
|--
  EX (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z) ,
  “ (SM2_RHON_Z = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (A_in_place < U256_MOD) ”
  &&  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
.

Definition mod_n_entail_wit_9_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 1)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH6 : (x3_3 < U64_MOD)) (PreH7 : (0 <= x3_3)) (PreH8 : (x2_3 < U64_MOD)) (PreH9 : (0 <= x2_3)) (PreH10 : (x1_3 < U64_MOD)) (PreH11 : (0 <= x1_3)) (PreH12 : (x0_3 < U64_MOD)) (PreH13 : (0 <= x0_3)) (PreH14 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH15 : (x3_2 < U64_MOD)) (PreH16 : (0 <= x3_2)) (PreH17 : (x2_2 < U64_MOD)) (PreH18 : (0 <= x2_2)) (PreH19 : (x1_2 < U64_MOD)) (PreH20 : (0 <= x1_2)) (PreH21 : (x0_2 < U64_MOD)) (PreH22 : (0 <= x0_2)) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (result_pre <> a_pre)) (PreH33 : (0 <= A_non_alias)) (PreH34 : (A_non_alias < U256_MOD)) (PreH35 : (retval_3 = 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
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
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre <> a_pre) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias < U256_MOD) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2))
  ||
  (EX (retval_2: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (SM2_RHON_Z = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (A_in_place < U256_MOD) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5))
.

Definition mod_n_entail_wit_9_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH6 : (x3_3 < U64_MOD)) (PreH7 : (0 <= x3_3)) (PreH8 : (x2_3 < U64_MOD)) (PreH9 : (0 <= x2_3)) (PreH10 : (x1_3 < U64_MOD)) (PreH11 : (0 <= x1_3)) (PreH12 : (x0_3 < U64_MOD)) (PreH13 : (0 <= x0_3)) (PreH14 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH15 : (x3_2 < U64_MOD)) (PreH16 : (0 <= x3_2)) (PreH17 : (x2_2 < U64_MOD)) (PreH18 : (0 <= x2_2)) (PreH19 : (x1_2 < U64_MOD)) (PreH20 : (0 <= x1_2)) (PreH21 : (x0_2 < U64_MOD)) (PreH22 : (0 <= x0_2)) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (result_pre <> a_pre)) (PreH33 : (0 <= A_non_alias)) (PreH34 : (A_non_alias < U256_MOD)) (PreH35 : (retval = 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
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
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre <> a_pre) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias < U256_MOD) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition mod_n_entail_wit_9_3_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 1)) (PreH4 : ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH6 : (x3_5 < U64_MOD)) (PreH7 : (0 <= x3_5)) (PreH8 : (x2_5 < U64_MOD)) (PreH9 : (0 <= x2_5)) (PreH10 : (x1_5 < U64_MOD)) (PreH11 : (0 <= x1_5)) (PreH12 : (x0_5 < U64_MOD)) (PreH13 : (0 <= x0_5)) (PreH14 : (A_in_place = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH15 : (x3_4 < U64_MOD)) (PreH16 : (0 <= x3_4)) (PreH17 : (x2_4 < U64_MOD)) (PreH18 : (0 <= x2_4)) (PreH19 : (x1_4 < U64_MOD)) (PreH20 : (0 <= x1_4)) (PreH21 : (x0_4 < U64_MOD)) (PreH22 : (0 <= x0_4)) (PreH23 : (result_pre = a_pre)) (PreH24 : (0 <= A_in_place)) (PreH25 : (A_in_place < U256_MOD)) (PreH26 : (retval_3 = 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
|--
  (EX (retval: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
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
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre <> a_pre) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias < U256_MOD) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (SM2_RHON_Z = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (A_in_place < U256_MOD) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5))
.

Definition mod_n_entail_wit_9_4_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH6 : (x3_5 < U64_MOD)) (PreH7 : (0 <= x3_5)) (PreH8 : (x2_5 < U64_MOD)) (PreH9 : (0 <= x2_5)) (PreH10 : (x1_5 < U64_MOD)) (PreH11 : (0 <= x1_5)) (PreH12 : (x0_5 < U64_MOD)) (PreH13 : (0 <= x0_5)) (PreH14 : (A_in_place = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH15 : (x3_4 < U64_MOD)) (PreH16 : (0 <= x3_4)) (PreH17 : (x2_4 < U64_MOD)) (PreH18 : (0 <= x2_4)) (PreH19 : (x1_4 < U64_MOD)) (PreH20 : (0 <= x1_4)) (PreH21 : (x0_4 < U64_MOD)) (PreH22 : (0 <= x0_4)) (PreH23 : (result_pre = a_pre)) (PreH24 : (0 <= A_in_place)) (PreH25 : (A_in_place < U256_MOD)) (PreH26 : (retval_2 = 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (SM2_RHON_Z = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (A_in_place < U256_MOD) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
.

Definition mod_n_entail_wit_10_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH6 : (x3_3 < U64_MOD)) (PreH7 : (0 <= x3_3)) (PreH8 : (x2_3 < U64_MOD)) (PreH9 : (0 <= x2_3)) (PreH10 : (x1_3 < U64_MOD)) (PreH11 : (0 <= x1_3)) (PreH12 : (x0_3 < U64_MOD)) (PreH13 : (0 <= x0_3)) (PreH14 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH15 : (x3_2 < U64_MOD)) (PreH16 : (0 <= x3_2)) (PreH17 : (x2_2 < U64_MOD)) (PreH18 : (0 <= x2_2)) (PreH19 : (x1_2 < U64_MOD)) (PreH20 : (0 <= x1_2)) (PreH21 : (x0_2 < U64_MOD)) (PreH22 : (0 <= x0_2)) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (result_pre <> a_pre)) (PreH33 : (0 <= A_non_alias)) (PreH34 : (A_non_alias < U256_MOD)) (PreH35 : (retval <> 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
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
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre <> a_pre) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias < U256_MOD) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition mod_n_entail_wit_10_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH6 : (x3_3 < U64_MOD)) (PreH7 : (0 <= x3_3)) (PreH8 : (x2_3 < U64_MOD)) (PreH9 : (0 <= x2_3)) (PreH10 : (x1_3 < U64_MOD)) (PreH11 : (0 <= x1_3)) (PreH12 : (x0_3 < U64_MOD)) (PreH13 : (0 <= x0_3)) (PreH14 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH15 : (x3_2 < U64_MOD)) (PreH16 : (0 <= x3_2)) (PreH17 : (x2_2 < U64_MOD)) (PreH18 : (0 <= x2_2)) (PreH19 : (x1_2 < U64_MOD)) (PreH20 : (0 <= x1_2)) (PreH21 : (x0_2 < U64_MOD)) (PreH22 : (0 <= x0_2)) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (result_pre <> a_pre)) (PreH33 : (0 <= A_non_alias)) (PreH34 : (A_non_alias < U256_MOD)) (PreH35 : (retval_3 <> 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
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
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre <> a_pre) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias < U256_MOD) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2))
  ||
  (EX (retval_2: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (SM2_RHON_Z = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (A_in_place < U256_MOD) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5))
.

Definition mod_n_entail_wit_10_3_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH6 : (x3_5 < U64_MOD)) (PreH7 : (0 <= x3_5)) (PreH8 : (x2_5 < U64_MOD)) (PreH9 : (0 <= x2_5)) (PreH10 : (x1_5 < U64_MOD)) (PreH11 : (0 <= x1_5)) (PreH12 : (x0_5 < U64_MOD)) (PreH13 : (0 <= x0_5)) (PreH14 : (A_in_place = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH15 : (x3_4 < U64_MOD)) (PreH16 : (0 <= x3_4)) (PreH17 : (x2_4 < U64_MOD)) (PreH18 : (0 <= x2_4)) (PreH19 : (x1_4 < U64_MOD)) (PreH20 : (0 <= x1_4)) (PreH21 : (x0_4 < U64_MOD)) (PreH22 : (0 <= x0_4)) (PreH23 : (result_pre = a_pre)) (PreH24 : (0 <= A_in_place)) (PreH25 : (A_in_place < U256_MOD)) (PreH26 : (retval_2 <> 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (SM2_RHON_Z = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (A_in_place < U256_MOD) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
.

Definition mod_n_entail_wit_10_4_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH6 : (x3_5 < U64_MOD)) (PreH7 : (0 <= x3_5)) (PreH8 : (x2_5 < U64_MOD)) (PreH9 : (0 <= x2_5)) (PreH10 : (x1_5 < U64_MOD)) (PreH11 : (0 <= x1_5)) (PreH12 : (x0_5 < U64_MOD)) (PreH13 : (0 <= x0_5)) (PreH14 : (A_in_place = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH15 : (x3_4 < U64_MOD)) (PreH16 : (0 <= x3_4)) (PreH17 : (x2_4 < U64_MOD)) (PreH18 : (0 <= x2_4)) (PreH19 : (x1_4 < U64_MOD)) (PreH20 : (0 <= x1_4)) (PreH21 : (x0_4 < U64_MOD)) (PreH22 : (0 <= x0_4)) (PreH23 : (result_pre = a_pre)) (PreH24 : (0 <= A_in_place)) (PreH25 : (A_in_place < U256_MOD)) (PreH26 : (retval_3 <> 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
|--
  (EX (retval: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
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
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre <> a_pre) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias < U256_MOD) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (SM2_RHON_Z = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (A_in_place < U256_MOD) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5))
.

Definition mod_n_return_wit_1_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (S: Z) (retval_2: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((u256_of_limbs (x0) (x1) (x2) (x3)) + (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) ) = (S + (retval_2 * U256_MOD ) ))) (PreH6 : (result_pre = result_pre)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH12 : (x3_3 < U64_MOD)) (PreH13 : (0 <= x3_3)) (PreH14 : (x2_3 < U64_MOD)) (PreH15 : (0 <= x2_3)) (PreH16 : (x1_3 < U64_MOD)) (PreH17 : (0 <= x1_3)) (PreH18 : (x0_3 < U64_MOD)) (PreH19 : (0 <= x0_3)) (PreH20 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH21 : (x3_2 < U64_MOD)) (PreH22 : (0 <= x3_2)) (PreH23 : (x2_2 < U64_MOD)) (PreH24 : (0 <= x2_2)) (PreH25 : (x1_2 < U64_MOD)) (PreH26 : (0 <= x1_2)) (PreH27 : (x0_2 < U64_MOD)) (PreH28 : (0 <= x0_2)) (PreH29 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH30 : (x3 < U64_MOD)) (PreH31 : (0 <= x3)) (PreH32 : (x2 < U64_MOD)) (PreH33 : (0 <= x2)) (PreH34 : (x1 < U64_MOD)) (PreH35 : (0 <= x1)) (PreH36 : (x0 < U64_MOD)) (PreH37 : (0 <= x0)) (PreH38 : (result_pre <> a_pre)) (PreH39 : (0 <= A_non_alias)) (PreH40 : (A_non_alias < U256_MOD)) (PreH41 : (retval <> 0)) ,
  (store_u256 result_pre S )
  **  (store_u256 ( &( "SM2_rhoN" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  (store_u256 a_pre A_non_alias )
  **  (store_fn result_pre (Zmod (A_non_alias) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (S: Z) (retval_2: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((u256_of_limbs (x0) (x1) (x2) (x3)) + (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) ) = (S + (retval_2 * U256_MOD ) ))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH10 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (result_pre <> a_pre)) (PreH38 : (0 <= A_non_alias)) (PreH39 : (A_non_alias < U256_MOD)) (PreH40 : (retval <> 0)) ,
  TT && emp 
|--
  “ (0 <= (Zmod (A_non_alias) (SM2_N_Z))) ” 
  &&  “ ((Zmod (A_non_alias) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (S = (Zmod (A_non_alias) (SM2_N_Z))) ” 
  &&  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
  &&  emp
).

Definition mod_n_return_wit_1_non_alias_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (S: Z) (retval_2: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((u256_of_limbs (x0) (x1) (x2) (x3)) + (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) ) = (S + (retval_2 * U256_MOD ) ))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH10 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (result_pre <> a_pre)) (PreH38 : (0 <= A_non_alias)) (PreH39 : (A_non_alias < U256_MOD)) (PreH40 : (retval <> 0)) ,
  (0 <= (Zmod (A_non_alias) (SM2_N_Z)))
.

Definition mod_n_return_wit_1_non_alias_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (S: Z) (retval_2: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((u256_of_limbs (x0) (x1) (x2) (x3)) + (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) ) = (S + (retval_2 * U256_MOD ) ))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH10 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (result_pre <> a_pre)) (PreH38 : (0 <= A_non_alias)) (PreH39 : (A_non_alias < U256_MOD)) (PreH40 : (retval <> 0)) ,
  ((Zmod (A_non_alias) (SM2_N_Z)) < SM2_N_Z)
.

Definition mod_n_return_wit_1_non_alias_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (S: Z) (retval_2: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((u256_of_limbs (x0) (x1) (x2) (x3)) + (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) ) = (S + (retval_2 * U256_MOD ) ))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH10 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (result_pre <> a_pre)) (PreH38 : (0 <= A_non_alias)) (PreH39 : (A_non_alias < U256_MOD)) (PreH40 : (retval <> 0)) ,
  (S = (Zmod (A_non_alias) (SM2_N_Z)))
.

Definition mod_n_return_wit_1_non_alias_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (S: Z) (retval_2: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((u256_of_limbs (x0) (x1) (x2) (x3)) + (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) ) = (S + (retval_2 * U256_MOD ) ))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH10 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (result_pre <> a_pre)) (PreH38 : (0 <= A_non_alias)) (PreH39 : (A_non_alias < U256_MOD)) (PreH40 : (retval <> 0)) ,
  ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z)
.

Definition mod_n_return_wit_2_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (S: Z) (retval_2: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((u256_of_limbs (x0) (x1) (x2) (x3)) + (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) ) = (S + (retval_2 * U256_MOD ) ))) (PreH6 : (result_pre = result_pre)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (result_pre = a_pre)) (PreH30 : (0 <= A_in_place)) (PreH31 : (A_in_place < U256_MOD)) (PreH32 : (retval <> 0)) ,
  (store_u256 result_pre S )
  **  (store_u256 ( &( "SM2_rhoN" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
|--
  “ (result_pre = a_pre) ”
  &&  (store_fn result_pre (Zmod (A_in_place) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (S: Z) (retval_2: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((u256_of_limbs (x0) (x1) (x2) (x3)) + (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) ) = (S + (retval_2 * U256_MOD ) ))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH10 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) (PreH28 : (result_pre = a_pre)) (PreH29 : (0 <= A_in_place)) (PreH30 : (A_in_place < U256_MOD)) (PreH31 : (retval <> 0)) ,
  TT && emp 
|--
  “ (0 <= (Zmod (A_in_place) (SM2_N_Z))) ” 
  &&  “ ((Zmod (A_in_place) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (S = (Zmod (A_in_place) (SM2_N_Z))) ” 
  &&  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
  &&  emp
).

Definition mod_n_return_wit_2_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (S: Z) (retval_2: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((u256_of_limbs (x0) (x1) (x2) (x3)) + (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) ) = (S + (retval_2 * U256_MOD ) ))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH10 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) (PreH28 : (result_pre = a_pre)) (PreH29 : (0 <= A_in_place)) (PreH30 : (A_in_place < U256_MOD)) (PreH31 : (retval <> 0)) ,
  (0 <= (Zmod (A_in_place) (SM2_N_Z)))
.

Definition mod_n_return_wit_2_in_place_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (S: Z) (retval_2: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((u256_of_limbs (x0) (x1) (x2) (x3)) + (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) ) = (S + (retval_2 * U256_MOD ) ))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH10 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) (PreH28 : (result_pre = a_pre)) (PreH29 : (0 <= A_in_place)) (PreH30 : (A_in_place < U256_MOD)) (PreH31 : (retval <> 0)) ,
  ((Zmod (A_in_place) (SM2_N_Z)) < SM2_N_Z)
.

Definition mod_n_return_wit_2_in_place_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (S: Z) (retval_2: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((u256_of_limbs (x0) (x1) (x2) (x3)) + (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) ) = (S + (retval_2 * U256_MOD ) ))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH10 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) (PreH28 : (result_pre = a_pre)) (PreH29 : (0 <= A_in_place)) (PreH30 : (A_in_place < U256_MOD)) (PreH31 : (retval <> 0)) ,
  (S = (Zmod (A_in_place) (SM2_N_Z)))
.

Definition mod_n_return_wit_2_in_place_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (S: Z) (retval_2: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((u256_of_limbs (x0) (x1) (x2) (x3)) + (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) ) = (S + (retval_2 * U256_MOD ) ))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH10 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) (PreH28 : (result_pre = a_pre)) (PreH29 : (0 <= A_in_place)) (PreH30 : (A_in_place < U256_MOD)) (PreH31 : (retval <> 0)) ,
  ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z)
.

Definition mod_n_return_wit_3_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH6 : (x3_3 < U64_MOD)) (PreH7 : (0 <= x3_3)) (PreH8 : (x2_3 < U64_MOD)) (PreH9 : (0 <= x2_3)) (PreH10 : (x1_3 < U64_MOD)) (PreH11 : (0 <= x1_3)) (PreH12 : (x0_3 < U64_MOD)) (PreH13 : (0 <= x0_3)) (PreH14 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH15 : (x3_2 < U64_MOD)) (PreH16 : (0 <= x3_2)) (PreH17 : (x2_2 < U64_MOD)) (PreH18 : (0 <= x2_2)) (PreH19 : (x1_2 < U64_MOD)) (PreH20 : (0 <= x1_2)) (PreH21 : (x0_2 < U64_MOD)) (PreH22 : (0 <= x0_2)) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (result_pre <> a_pre)) (PreH33 : (0 <= A_non_alias)) (PreH34 : (A_non_alias < U256_MOD)) (PreH35 : (retval = 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  (store_u256 a_pre A_non_alias )
  **  (store_fn result_pre (Zmod (A_non_alias) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (PreH1 : (x0_3 <= UINT64_MAX)) (PreH2 : (x1_3 <= UINT64_MAX)) (PreH3 : (x2_3 <= UINT64_MAX)) (PreH4 : (x3_3 <= UINT64_MAX)) (PreH5 : (x0_3 >= 0)) (PreH6 : (x1_3 >= 0)) (PreH7 : (x2_3 >= 0)) (PreH8 : (x3_3 >= 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 0)) (PreH12 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH13 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH14 : (x3_3 < U64_MOD)) (PreH15 : (0 <= x3_3)) (PreH16 : (x2_3 < U64_MOD)) (PreH17 : (0 <= x2_3)) (PreH18 : (x1_3 < U64_MOD)) (PreH19 : (0 <= x1_3)) (PreH20 : (x0_3 < U64_MOD)) (PreH21 : (0 <= x0_3)) (PreH22 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (result_pre <> a_pre)) (PreH41 : (0 <= A_non_alias)) (PreH42 : (A_non_alias < U256_MOD)) (PreH43 : (retval = 0)) ,
  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
|--
  “ (0 <= (Zmod (A_non_alias) (SM2_N_Z))) ” 
  &&  “ ((Zmod (A_non_alias) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (A_non_alias = (Zmod (A_non_alias) (SM2_N_Z))) ” 
  &&  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
  &&  (store_sm2_rhon )
).

Definition mod_n_return_wit_3_non_alias_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (PreH1 : (x0_3 <= UINT64_MAX)) (PreH2 : (x1_3 <= UINT64_MAX)) (PreH3 : (x2_3 <= UINT64_MAX)) (PreH4 : (x3_3 <= UINT64_MAX)) (PreH5 : (x0_3 >= 0)) (PreH6 : (x1_3 >= 0)) (PreH7 : (x2_3 >= 0)) (PreH8 : (x3_3 >= 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 0)) (PreH12 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH13 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH14 : (x3_3 < U64_MOD)) (PreH15 : (0 <= x3_3)) (PreH16 : (x2_3 < U64_MOD)) (PreH17 : (0 <= x2_3)) (PreH18 : (x1_3 < U64_MOD)) (PreH19 : (0 <= x1_3)) (PreH20 : (x0_3 < U64_MOD)) (PreH21 : (0 <= x0_3)) (PreH22 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (result_pre <> a_pre)) (PreH41 : (0 <= A_non_alias)) (PreH42 : (A_non_alias < U256_MOD)) (PreH43 : (retval = 0)) ,
  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
|--
  “ (0 <= (Zmod (A_non_alias) (SM2_N_Z))) ”
.

Definition mod_n_return_wit_3_non_alias_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (PreH1 : (x0_3 <= UINT64_MAX)) (PreH2 : (x1_3 <= UINT64_MAX)) (PreH3 : (x2_3 <= UINT64_MAX)) (PreH4 : (x3_3 <= UINT64_MAX)) (PreH5 : (x0_3 >= 0)) (PreH6 : (x1_3 >= 0)) (PreH7 : (x2_3 >= 0)) (PreH8 : (x3_3 >= 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 0)) (PreH12 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH13 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH14 : (x3_3 < U64_MOD)) (PreH15 : (0 <= x3_3)) (PreH16 : (x2_3 < U64_MOD)) (PreH17 : (0 <= x2_3)) (PreH18 : (x1_3 < U64_MOD)) (PreH19 : (0 <= x1_3)) (PreH20 : (x0_3 < U64_MOD)) (PreH21 : (0 <= x0_3)) (PreH22 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (result_pre <> a_pre)) (PreH41 : (0 <= A_non_alias)) (PreH42 : (A_non_alias < U256_MOD)) (PreH43 : (retval = 0)) ,
  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
|--
  “ ((Zmod (A_non_alias) (SM2_N_Z)) < SM2_N_Z) ”
.

Definition mod_n_return_wit_3_non_alias_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (PreH1 : (x0_3 <= UINT64_MAX)) (PreH2 : (x1_3 <= UINT64_MAX)) (PreH3 : (x2_3 <= UINT64_MAX)) (PreH4 : (x3_3 <= UINT64_MAX)) (PreH5 : (x0_3 >= 0)) (PreH6 : (x1_3 >= 0)) (PreH7 : (x2_3 >= 0)) (PreH8 : (x3_3 >= 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 0)) (PreH12 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH13 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH14 : (x3_3 < U64_MOD)) (PreH15 : (0 <= x3_3)) (PreH16 : (x2_3 < U64_MOD)) (PreH17 : (0 <= x2_3)) (PreH18 : (x1_3 < U64_MOD)) (PreH19 : (0 <= x1_3)) (PreH20 : (x0_3 < U64_MOD)) (PreH21 : (0 <= x0_3)) (PreH22 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (result_pre <> a_pre)) (PreH41 : (0 <= A_non_alias)) (PreH42 : (A_non_alias < U256_MOD)) (PreH43 : (retval = 0)) ,
  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
|--
  “ (A_non_alias = (Zmod (A_non_alias) (SM2_N_Z))) ”
.

Definition mod_n_return_wit_3_non_alias_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (PreH1 : (x0_3 <= UINT64_MAX)) (PreH2 : (x1_3 <= UINT64_MAX)) (PreH3 : (x2_3 <= UINT64_MAX)) (PreH4 : (x3_3 <= UINT64_MAX)) (PreH5 : (x0_3 >= 0)) (PreH6 : (x1_3 >= 0)) (PreH7 : (x2_3 >= 0)) (PreH8 : (x3_3 >= 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 0)) (PreH12 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH13 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH14 : (x3_3 < U64_MOD)) (PreH15 : (0 <= x3_3)) (PreH16 : (x2_3 < U64_MOD)) (PreH17 : (0 <= x2_3)) (PreH18 : (x1_3 < U64_MOD)) (PreH19 : (0 <= x1_3)) (PreH20 : (x0_3 < U64_MOD)) (PreH21 : (0 <= x0_3)) (PreH22 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (result_pre <> a_pre)) (PreH41 : (0 <= A_non_alias)) (PreH42 : (A_non_alias < U256_MOD)) (PreH43 : (retval = 0)) ,
  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
|--
  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
.

Definition mod_n_return_wit_3_non_alias_split_goal_spatial := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (PreH1 : (x0_3 <= UINT64_MAX)) (PreH2 : (x1_3 <= UINT64_MAX)) (PreH3 : (x2_3 <= UINT64_MAX)) (PreH4 : (x3_3 <= UINT64_MAX)) (PreH5 : (x0_3 >= 0)) (PreH6 : (x1_3 >= 0)) (PreH7 : (x2_3 >= 0)) (PreH8 : (x3_3 >= 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 0)) (PreH12 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH13 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH14 : (x3_3 < U64_MOD)) (PreH15 : (0 <= x3_3)) (PreH16 : (x2_3 < U64_MOD)) (PreH17 : (0 <= x2_3)) (PreH18 : (x1_3 < U64_MOD)) (PreH19 : (0 <= x1_3)) (PreH20 : (x0_3 < U64_MOD)) (PreH21 : (0 <= x0_3)) (PreH22 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (result_pre <> a_pre)) (PreH41 : (0 <= A_non_alias)) (PreH42 : (A_non_alias < U256_MOD)) (PreH43 : (retval = 0)) ,
  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
|--
  (store_sm2_rhon )
.

Definition mod_n_return_wit_4_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (result_pre = a_pre)) (PreH24 : (0 <= A_in_place)) (PreH25 : (A_in_place < U256_MOD)) (PreH26 : (retval = 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (result_pre = a_pre) ”
  &&  (store_fn result_pre (Zmod (A_in_place) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (x0_2 >= 0)) (PreH6 : (x1_2 >= 0)) (PreH7 : (x2_2 >= 0)) (PreH8 : (x3_2 >= 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 0)) (PreH12 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH13 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (result_pre = a_pre)) (PreH32 : (0 <= A_in_place)) (PreH33 : (A_in_place < U256_MOD)) (PreH34 : (retval = 0)) ,
  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (0 <= (Zmod (A_in_place) (SM2_N_Z))) ” 
  &&  “ ((Zmod (A_in_place) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (A_in_place = (Zmod (A_in_place) (SM2_N_Z))) ” 
  &&  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
  &&  (store_sm2_rhon )
).

Definition mod_n_return_wit_4_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (x0_2 >= 0)) (PreH6 : (x1_2 >= 0)) (PreH7 : (x2_2 >= 0)) (PreH8 : (x3_2 >= 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 0)) (PreH12 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH13 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (result_pre = a_pre)) (PreH32 : (0 <= A_in_place)) (PreH33 : (A_in_place < U256_MOD)) (PreH34 : (retval = 0)) ,
  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (0 <= (Zmod (A_in_place) (SM2_N_Z))) ”
.

Definition mod_n_return_wit_4_in_place_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (x0_2 >= 0)) (PreH6 : (x1_2 >= 0)) (PreH7 : (x2_2 >= 0)) (PreH8 : (x3_2 >= 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 0)) (PreH12 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH13 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (result_pre = a_pre)) (PreH32 : (0 <= A_in_place)) (PreH33 : (A_in_place < U256_MOD)) (PreH34 : (retval = 0)) ,
  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ ((Zmod (A_in_place) (SM2_N_Z)) < SM2_N_Z) ”
.

Definition mod_n_return_wit_4_in_place_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (x0_2 >= 0)) (PreH6 : (x1_2 >= 0)) (PreH7 : (x2_2 >= 0)) (PreH8 : (x3_2 >= 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 0)) (PreH12 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH13 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (result_pre = a_pre)) (PreH32 : (0 <= A_in_place)) (PreH33 : (A_in_place < U256_MOD)) (PreH34 : (retval = 0)) ,
  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (A_in_place = (Zmod (A_in_place) (SM2_N_Z))) ”
.

Definition mod_n_return_wit_4_in_place_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (x0_2 >= 0)) (PreH6 : (x1_2 >= 0)) (PreH7 : (x2_2 >= 0)) (PreH8 : (x3_2 >= 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 0)) (PreH12 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH13 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (result_pre = a_pre)) (PreH32 : (0 <= A_in_place)) (PreH33 : (A_in_place < U256_MOD)) (PreH34 : (retval = 0)) ,
  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
.

Definition mod_n_return_wit_4_in_place_split_goal_spatial := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (x0_2 >= 0)) (PreH6 : (x1_2 >= 0)) (PreH7 : (x2_2 >= 0)) (PreH8 : (x3_2 >= 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 0)) (PreH12 : ((u256_of_limbs (x0) (x1) (x2) (x3)) < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH13 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH14 : (x3_2 < U64_MOD)) (PreH15 : (0 <= x3_2)) (PreH16 : (x2_2 < U64_MOD)) (PreH17 : (0 <= x2_2)) (PreH18 : (x1_2 < U64_MOD)) (PreH19 : (0 <= x1_2)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (result_pre = a_pre)) (PreH32 : (0 <= A_in_place)) (PreH33 : (A_in_place < U256_MOD)) (PreH34 : (retval = 0)) ,
  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  (store_sm2_rhon )
.

Definition mod_n_partial_solve_wit_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (result_pre <> a_pre)) ,
  (UndefStructPredu32 result_pre )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre <> a_pre) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
.

Definition mod_n_partial_solve_wit_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (PreH1 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH2 : (x3_3 < U64_MOD)) (PreH3 : (0 <= x3_3)) (PreH4 : (x2_3 < U64_MOD)) (PreH5 : (0 <= x2_3)) (PreH6 : (x1_3 < U64_MOD)) (PreH7 : (0 <= x1_3)) (PreH8 : (x0_3 < U64_MOD)) (PreH9 : (0 <= x0_3)) (PreH10 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) (PreH28 : (result_pre <> a_pre)) (PreH29 : (0 <= A_non_alias)) (PreH30 : (A_non_alias < U256_MOD)) ,
  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
|--
  “ (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
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
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre <> a_pre) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias < U256_MOD) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition mod_n_partial_solve_wit_3_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = a_pre)) (PreH20 : (0 <= A_in_place)) (PreH21 : (A_in_place < U256_MOD)) ,
  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
|--
  “ (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (A_in_place < U256_MOD) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition mod_n_partial_solve_wit_4_non_alias_pure := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH6 : (x3_3 < U64_MOD)) (PreH7 : (0 <= x3_3)) (PreH8 : (x2_3 < U64_MOD)) (PreH9 : (0 <= x2_3)) (PreH10 : (x1_3 < U64_MOD)) (PreH11 : (0 <= x1_3)) (PreH12 : (x0_3 < U64_MOD)) (PreH13 : (0 <= x0_3)) (PreH14 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH15 : (x3_2 < U64_MOD)) (PreH16 : (0 <= x3_2)) (PreH17 : (x2_2 < U64_MOD)) (PreH18 : (0 <= x2_2)) (PreH19 : (x1_2 < U64_MOD)) (PreH20 : (0 <= x1_2)) (PreH21 : (x0_2 < U64_MOD)) (PreH22 : (0 <= x0_2)) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (result_pre <> a_pre)) (PreH33 : (0 <= A_non_alias)) (PreH34 : (A_non_alias < U256_MOD)) (PreH35 : (retval <> 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (result_pre = result_pre) ”
.

Definition mod_n_partial_solve_wit_4_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH6 : (x3_3 < U64_MOD)) (PreH7 : (0 <= x3_3)) (PreH8 : (x2_3 < U64_MOD)) (PreH9 : (0 <= x2_3)) (PreH10 : (x1_3 < U64_MOD)) (PreH11 : (0 <= x1_3)) (PreH12 : (x0_3 < U64_MOD)) (PreH13 : (0 <= x0_3)) (PreH14 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH15 : (x3_2 < U64_MOD)) (PreH16 : (0 <= x3_2)) (PreH17 : (x2_2 < U64_MOD)) (PreH18 : (0 <= x2_2)) (PreH19 : (x1_2 < U64_MOD)) (PreH20 : (0 <= x1_2)) (PreH21 : (x0_2 < U64_MOD)) (PreH22 : (0 <= x0_2)) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (result_pre <> a_pre)) (PreH33 : (0 <= A_non_alias)) (PreH34 : (A_non_alias < U256_MOD)) (PreH35 : (retval <> 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (result_pre = result_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (SM2_RHON_Z = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
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
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre <> a_pre) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (A_non_alias < U256_MOD) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_rhoN" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition mod_n_partial_solve_wit_4_non_alias := mod_n_partial_solve_wit_4_non_alias_pure -> mod_n_partial_solve_wit_4_non_alias_aux.

Definition mod_n_partial_solve_wit_5_in_place_pure := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (result_pre = a_pre)) (PreH24 : (0 <= A_in_place)) (PreH25 : (A_in_place < U256_MOD)) (PreH26 : (retval <> 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (result_pre = result_pre) ”
.

Definition mod_n_partial_solve_wit_5_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) (PreH23 : (result_pre = a_pre)) (PreH24 : (0 <= A_in_place)) (PreH25 : (A_in_place < U256_MOD)) (PreH26 : (retval <> 0)) ,
  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "SM2_rhoN" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (result_pre = result_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (SM2_RHON_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (A_in_place < U256_MOD) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 result_pre (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "SM2_rhoN" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
.

Definition mod_n_partial_solve_wit_5_in_place := mod_n_partial_solve_wit_5_in_place_pure -> mod_n_partial_solve_wit_5_in_place_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_mod_n_safety_wit_1_in_place : mod_n_safety_wit_1_in_place.
Axiom proof_of_mod_n_safety_wit_2_non_alias : mod_n_safety_wit_2_non_alias.
Axiom proof_of_mod_n_safety_wit_3_non_alias : mod_n_safety_wit_3_non_alias.
Axiom proof_of_mod_n_safety_wit_4_in_place : mod_n_safety_wit_4_in_place.
Axiom proof_of_mod_n_safety_wit_5_non_alias : mod_n_safety_wit_5_non_alias.
Axiom proof_of_mod_n_safety_wit_6_in_place : mod_n_safety_wit_6_in_place.
Axiom proof_of_mod_n_entail_wit_1_1_in_place : mod_n_entail_wit_1_1_in_place.
Axiom proof_of_mod_n_entail_wit_1_2_non_alias : mod_n_entail_wit_1_2_non_alias.
Axiom proof_of_mod_n_entail_wit_2_non_alias : mod_n_entail_wit_2_non_alias.
Axiom proof_of_mod_n_entail_wit_3_non_alias : mod_n_entail_wit_3_non_alias.
Axiom proof_of_mod_n_entail_wit_4_non_alias : mod_n_entail_wit_4_non_alias.
Axiom proof_of_mod_n_entail_wit_5_in_place : mod_n_entail_wit_5_in_place.
Axiom proof_of_mod_n_entail_wit_6_1_non_alias : mod_n_entail_wit_6_1_non_alias.
Axiom proof_of_mod_n_entail_wit_6_2_in_place : mod_n_entail_wit_6_2_in_place.
Axiom proof_of_mod_n_entail_wit_7_1_non_alias : mod_n_entail_wit_7_1_non_alias.
Axiom proof_of_mod_n_entail_wit_7_2_in_place : mod_n_entail_wit_7_2_in_place.
Axiom proof_of_mod_n_entail_wit_8_1_non_alias : mod_n_entail_wit_8_1_non_alias.
Axiom proof_of_mod_n_entail_wit_8_2_in_place : mod_n_entail_wit_8_2_in_place.
Axiom proof_of_mod_n_entail_wit_9_1_non_alias : mod_n_entail_wit_9_1_non_alias.
Axiom proof_of_mod_n_entail_wit_9_2_non_alias : mod_n_entail_wit_9_2_non_alias.
Axiom proof_of_mod_n_entail_wit_9_3_in_place : mod_n_entail_wit_9_3_in_place.
Axiom proof_of_mod_n_entail_wit_9_4_in_place : mod_n_entail_wit_9_4_in_place.
Axiom proof_of_mod_n_entail_wit_10_1_non_alias : mod_n_entail_wit_10_1_non_alias.
Axiom proof_of_mod_n_entail_wit_10_2_non_alias : mod_n_entail_wit_10_2_non_alias.
Axiom proof_of_mod_n_entail_wit_10_3_in_place : mod_n_entail_wit_10_3_in_place.
Axiom proof_of_mod_n_entail_wit_10_4_in_place : mod_n_entail_wit_10_4_in_place.
Axiom proof_of_mod_n_return_wit_1_non_alias : mod_n_return_wit_1_non_alias.
Axiom proof_of_mod_n_return_wit_2_in_place : mod_n_return_wit_2_in_place.
Axiom proof_of_mod_n_return_wit_3_non_alias : mod_n_return_wit_3_non_alias.
Axiom proof_of_mod_n_return_wit_4_in_place : mod_n_return_wit_4_in_place.
Axiom proof_of_mod_n_partial_solve_wit_1_non_alias : mod_n_partial_solve_wit_1_non_alias.
Axiom proof_of_mod_n_partial_solve_wit_2_non_alias : mod_n_partial_solve_wit_2_non_alias.
Axiom proof_of_mod_n_partial_solve_wit_3_in_place : mod_n_partial_solve_wit_3_in_place.
Axiom proof_of_mod_n_partial_solve_wit_4_non_alias_pure : mod_n_partial_solve_wit_4_non_alias_pure.
Axiom proof_of_mod_n_partial_solve_wit_4_non_alias : mod_n_partial_solve_wit_4_non_alias.
Axiom proof_of_mod_n_partial_solve_wit_5_in_place_pure : mod_n_partial_solve_wit_5_in_place_pure.
Axiom proof_of_mod_n_partial_solve_wit_5_in_place : mod_n_partial_solve_wit_5_in_place.

End VC_Correct.
