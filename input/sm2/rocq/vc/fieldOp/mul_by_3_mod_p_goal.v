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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.

(*----- Function mul_by_3_mod_p -----*)

Definition mul_by_3_mod_p_entail_wit_1_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  (“ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  ||
  (“ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (store_u256 a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
.

Definition mul_by_3_mod_p_entail_wit_1_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
|--
  (“ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  ||
  (“ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (store_u256 a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
.

Definition mul_by_3_mod_p_entail_wit_2_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (A_non_alias < SM2_P_Z)) (PreH2 : (0 <= A_non_alias)) ,
  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
.

Definition mul_by_3_mod_p_entail_wit_2_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (A_in_place < SM2_P_Z)) (PreH2 : (0 <= A_in_place)) (PreH3 : (result_pre = a_pre)) ,
  (store_u256 a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
.

Definition mul_by_3_mod_p_return_wit_1_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  (store_fp result_pre (Zmod (((Zmod ((2 * (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) + (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
|--
  “ (result_pre = a_pre) ”
  &&  (store_fp result_pre (Zmod ((3 * A_in_place )) (SM2_P_Z)) )
  **  (store_sm2_p )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  TT && emp 
|--
  “ ((Zmod (((Zmod ((2 * (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) + (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) = (Zmod ((3 * A_in_place )) (SM2_P_Z))) ”
  &&  emp
).

Definition mul_by_3_mod_p_return_wit_1_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  ((Zmod (((Zmod ((2 * (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) + (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) = (Zmod ((3 * A_in_place )) (SM2_P_Z)))
.

Definition mul_by_3_mod_p_return_wit_2_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (store_fp result_pre (Zmod (((Zmod ((2 * (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) + (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre (Zmod ((3 * A_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
) \/
(
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  TT && emp 
|--
  “ ((Zmod (((Zmod ((2 * (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) + (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) = (Zmod ((3 * A_non_alias )) (SM2_P_Z))) ” 
  &&  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = A_non_alias) ”
  &&  emp
).

Definition mul_by_3_mod_p_return_wit_2_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((Zmod (((Zmod ((2 * (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) + (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) = (Zmod ((3 * A_non_alias )) (SM2_P_Z)))
.

Definition mul_by_3_mod_p_return_wit_2_non_alias_split_goal_2 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = A_non_alias)
.

Definition mul_by_3_mod_p_partial_solve_wit_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UndefStructPredu32 ( &( "tmp_a" ) ) )
  **  (UndefStructPredu32 ( &( "tmp_2a" ) ) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
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
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (UInt64Array.undef_full &(( &( "tmp_a" ) )->ₛ "v") 4 )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UndefStructPredu32 ( &( "tmp_2a" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
.

Definition mul_by_3_mod_p_partial_solve_wit_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  (UndefStructPredu32 ( &( "tmp_a" ) ) )
  **  (UndefStructPredu32 ( &( "tmp_2a" ) ) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
|--
  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (UInt64Array.undef_full &(( &( "tmp_a" ) )->ₛ "v") 4 )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UndefStructPredu32 ( &( "tmp_2a" ) ) )
  **  (store_sm2_p )
.

Definition mul_by_3_mod_p_partial_solve_wit_3_in_place_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "tmp_a" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UndefStructPredu32 ( &( "tmp_2a" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (0 <= (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))))) ” 
  &&  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) < SM2_P_Z) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "tmp_a" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UndefStructPredu32 ( &( "tmp_2a" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) < SM2_P_Z) ” 
  &&  “ (0 <= (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))))) ”
).

Definition mul_by_3_mod_p_partial_solve_wit_3_in_place_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "tmp_a" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UndefStructPredu32 ( &( "tmp_2a" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) < SM2_P_Z) ”
.

Definition mul_by_3_mod_p_partial_solve_wit_3_in_place_pure_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "tmp_a" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UndefStructPredu32 ( &( "tmp_2a" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (0 <= (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))))) ”
.

Definition mul_by_3_mod_p_partial_solve_wit_3_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "tmp_a" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UndefStructPredu32 ( &( "tmp_2a" ) ) )
  **  (store_sm2_p )
|--
  “ (0 <= (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))))) ” 
  &&  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) < SM2_P_Z) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (store_fp ( &( "tmp_a" ) ) (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.undef_full &(( &( "tmp_2a" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
.

Definition mul_by_3_mod_p_partial_solve_wit_3_in_place := mul_by_3_mod_p_partial_solve_wit_3_in_place_pure -> mul_by_3_mod_p_partial_solve_wit_3_in_place_aux.

Definition mul_by_3_mod_p_partial_solve_wit_4_non_alias_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "tmp_a" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UndefStructPredu32 ( &( "tmp_2a" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (0 <= (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))))) ” 
  &&  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) < SM2_P_Z) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "tmp_a" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UndefStructPredu32 ( &( "tmp_2a" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) < SM2_P_Z) ” 
  &&  “ (0 <= (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))))) ”
).

Definition mul_by_3_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "tmp_a" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UndefStructPredu32 ( &( "tmp_2a" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) < SM2_P_Z) ”
.

Definition mul_by_3_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "tmp_a" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UndefStructPredu32 ( &( "tmp_2a" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (0 <= (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))))) ”
.

Definition mul_by_3_mod_p_partial_solve_wit_4_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "tmp_a" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UndefStructPredu32 ( &( "tmp_2a" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (0 <= (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))))) ” 
  &&  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) < SM2_P_Z) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (store_fp ( &( "tmp_a" ) ) (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.undef_full &(( &( "tmp_2a" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition mul_by_3_mod_p_partial_solve_wit_4_non_alias := mul_by_3_mod_p_partial_solve_wit_4_non_alias_pure -> mul_by_3_mod_p_partial_solve_wit_4_non_alias_aux.

Definition mul_by_3_mod_p_partial_solve_wit_5_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  (store_fp ( &( "tmp_a" ) ) (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (store_fp ( &( "tmp_2a" ) ) (Zmod ((2 * (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (store_fp ( &( "tmp_2a" ) ) (Zmod ((2 * (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp_a" ) ) (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
.

Definition mul_by_3_mod_p_partial_solve_wit_6_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (store_fp ( &( "tmp_a" ) ) (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (store_fp ( &( "tmp_2a" ) ) (Zmod ((2 * (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
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
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (store_fp ( &( "tmp_2a" ) ) (Zmod ((2 * (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp_a" ) ) (u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
.

Definition mul_by_3_mod_p_derive_mont_in_place_by_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_mont_in_place: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_mont_in_place) ” 
  &&  “ (A_mont_in_place < SM2_P_Z) ”
  &&  (store_fp a_pre (mont_p (A_mont_in_place)) )
  **  (store_sm2_p )
|--
EX (A_in_place: Z) ,
  (“ (result_pre = a_pre) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p ))
  **
  ((“ (result_pre = a_pre) ”
  &&  (store_fp result_pre (Zmod ((3 * A_in_place )) (SM2_P_Z)) )
  **  (store_sm2_p ))
  -*
  (“ (result_pre = a_pre) ”
  &&  (store_fp result_pre (mont_p ((3 * A_mont_in_place ))) )
  **  (store_sm2_p )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_mul_by_3_mod_p_entail_wit_1_1_non_alias : mul_by_3_mod_p_entail_wit_1_1_non_alias.
Axiom proof_of_mul_by_3_mod_p_entail_wit_1_2_in_place : mul_by_3_mod_p_entail_wit_1_2_in_place.
Axiom proof_of_mul_by_3_mod_p_entail_wit_2_1_non_alias : mul_by_3_mod_p_entail_wit_2_1_non_alias.
Axiom proof_of_mul_by_3_mod_p_entail_wit_2_2_in_place : mul_by_3_mod_p_entail_wit_2_2_in_place.
Axiom proof_of_mul_by_3_mod_p_return_wit_1_in_place : mul_by_3_mod_p_return_wit_1_in_place.
Axiom proof_of_mul_by_3_mod_p_return_wit_2_non_alias : mul_by_3_mod_p_return_wit_2_non_alias.
Axiom proof_of_mul_by_3_mod_p_partial_solve_wit_1_non_alias : mul_by_3_mod_p_partial_solve_wit_1_non_alias.
Axiom proof_of_mul_by_3_mod_p_partial_solve_wit_2_in_place : mul_by_3_mod_p_partial_solve_wit_2_in_place.
Axiom proof_of_mul_by_3_mod_p_partial_solve_wit_3_in_place_pure : mul_by_3_mod_p_partial_solve_wit_3_in_place_pure.
Axiom proof_of_mul_by_3_mod_p_partial_solve_wit_3_in_place : mul_by_3_mod_p_partial_solve_wit_3_in_place.
Axiom proof_of_mul_by_3_mod_p_partial_solve_wit_4_non_alias_pure : mul_by_3_mod_p_partial_solve_wit_4_non_alias_pure.
Axiom proof_of_mul_by_3_mod_p_partial_solve_wit_4_non_alias : mul_by_3_mod_p_partial_solve_wit_4_non_alias.
Axiom proof_of_mul_by_3_mod_p_partial_solve_wit_5_in_place : mul_by_3_mod_p_partial_solve_wit_5_in_place.
Axiom proof_of_mul_by_3_mod_p_partial_solve_wit_6_non_alias : mul_by_3_mod_p_partial_solve_wit_6_non_alias.
Axiom proof_of_mul_by_3_mod_p_derive_mont_in_place_by_in_place : mul_by_3_mod_p_derive_mont_in_place_by_in_place.

End VC_Correct.
