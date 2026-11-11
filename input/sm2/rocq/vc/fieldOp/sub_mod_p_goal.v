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
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.

(*----- Function sub_mod_p -----*)

Definition sub_mod_p_safety_wit_1_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_non_alias < SM2_P_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_P_Z)) (PreH22 : (0 <= A_non_alias)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_2_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_a < SM2_P_Z)) (PreH20 : (0 <= B_r_eq_a)) (PreH21 : (A_r_eq_a < SM2_P_Z)) (PreH22 : (0 <= A_r_eq_a)) (PreH23 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_3_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_b < SM2_P_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_P_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_4_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_non_alias < SM2_P_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_P_Z)) (PreH22 : (0 <= A_non_alias)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_5_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_non_alias < SM2_P_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_P_Z)) (PreH22 : (0 <= A_non_alias)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_6_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_non_alias < SM2_P_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_P_Z)) (PreH22 : (0 <= A_non_alias)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_7_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_a < SM2_P_Z)) (PreH20 : (0 <= B_r_eq_a)) (PreH21 : (A_r_eq_a < SM2_P_Z)) (PreH22 : (0 <= A_r_eq_a)) (PreH23 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_8_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_a < SM2_P_Z)) (PreH20 : (0 <= B_r_eq_a)) (PreH21 : (A_r_eq_a < SM2_P_Z)) (PreH22 : (0 <= A_r_eq_a)) (PreH23 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_9_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_a < SM2_P_Z)) (PreH20 : (0 <= B_r_eq_a)) (PreH21 : (A_r_eq_a < SM2_P_Z)) (PreH22 : (0 <= A_r_eq_a)) (PreH23 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_10_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_b < SM2_P_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_P_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_11_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_b < SM2_P_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_P_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_12_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_b < SM2_P_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_P_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_13_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_non_alias < SM2_P_Z)) (PreH25 : (0 <= B_non_alias)) (PreH26 : (A_non_alias < SM2_P_Z)) (PreH27 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_14_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_non_alias < SM2_P_Z)) (PreH25 : (0 <= B_non_alias)) (PreH26 : (A_non_alias < SM2_P_Z)) (PreH27 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_15_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_non_alias < SM2_P_Z)) (PreH25 : (0 <= B_non_alias)) (PreH26 : (A_non_alias < SM2_P_Z)) (PreH27 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_16_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_a < SM2_P_Z)) (PreH25 : (0 <= B_r_eq_a)) (PreH26 : (A_r_eq_a < SM2_P_Z)) (PreH27 : (0 <= A_r_eq_a)) (PreH28 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_17_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_a < SM2_P_Z)) (PreH25 : (0 <= B_r_eq_a)) (PreH26 : (A_r_eq_a < SM2_P_Z)) (PreH27 : (0 <= A_r_eq_a)) (PreH28 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_18_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_a < SM2_P_Z)) (PreH25 : (0 <= B_r_eq_a)) (PreH26 : (A_r_eq_a < SM2_P_Z)) (PreH27 : (0 <= A_r_eq_a)) (PreH28 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_19_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_b < SM2_P_Z)) (PreH25 : (0 <= B_r_eq_b)) (PreH26 : (A_r_eq_b < SM2_P_Z)) (PreH27 : (0 <= A_r_eq_b)) (PreH28 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_20_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_b < SM2_P_Z)) (PreH25 : (0 <= B_r_eq_b)) (PreH26 : (A_r_eq_b < SM2_P_Z)) (PreH27 : (0 <= A_r_eq_b)) (PreH28 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_21_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_b < SM2_P_Z)) (PreH25 : (0 <= B_r_eq_b)) (PreH26 : (A_r_eq_b < SM2_P_Z)) (PreH27 : (0 <= A_r_eq_b)) (PreH28 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_22_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_non_alias < SM2_P_Z)) (PreH30 : (0 <= B_non_alias)) (PreH31 : (A_non_alias < SM2_P_Z)) (PreH32 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_23_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_non_alias < SM2_P_Z)) (PreH30 : (0 <= B_non_alias)) (PreH31 : (A_non_alias < SM2_P_Z)) (PreH32 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_24_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_non_alias < SM2_P_Z)) (PreH30 : (0 <= B_non_alias)) (PreH31 : (A_non_alias < SM2_P_Z)) (PreH32 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_25_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_a < SM2_P_Z)) (PreH30 : (0 <= B_r_eq_a)) (PreH31 : (A_r_eq_a < SM2_P_Z)) (PreH32 : (0 <= A_r_eq_a)) (PreH33 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_26_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_a < SM2_P_Z)) (PreH30 : (0 <= B_r_eq_a)) (PreH31 : (A_r_eq_a < SM2_P_Z)) (PreH32 : (0 <= A_r_eq_a)) (PreH33 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_27_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_a < SM2_P_Z)) (PreH30 : (0 <= B_r_eq_a)) (PreH31 : (A_r_eq_a < SM2_P_Z)) (PreH32 : (0 <= A_r_eq_a)) (PreH33 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_28_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_b < SM2_P_Z)) (PreH30 : (0 <= B_r_eq_b)) (PreH31 : (A_r_eq_b < SM2_P_Z)) (PreH32 : (0 <= A_r_eq_b)) (PreH33 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_29_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_b < SM2_P_Z)) (PreH30 : (0 <= B_r_eq_b)) (PreH31 : (A_r_eq_b < SM2_P_Z)) (PreH32 : (0 <= A_r_eq_b)) (PreH33 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_30_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_b < SM2_P_Z)) (PreH30 : (0 <= B_r_eq_b)) (PreH31 : (A_r_eq_b < SM2_P_Z)) (PreH32 : (0 <= A_r_eq_b)) (PreH33 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_31_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_non_alias < SM2_P_Z)) (PreH35 : (0 <= B_non_alias)) (PreH36 : (A_non_alias < SM2_P_Z)) (PreH37 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_32_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_non_alias < SM2_P_Z)) (PreH35 : (0 <= B_non_alias)) (PreH36 : (A_non_alias < SM2_P_Z)) (PreH37 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_33_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_non_alias < SM2_P_Z)) (PreH35 : (0 <= B_non_alias)) (PreH36 : (A_non_alias < SM2_P_Z)) (PreH37 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_34_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_a < SM2_P_Z)) (PreH35 : (0 <= B_r_eq_a)) (PreH36 : (A_r_eq_a < SM2_P_Z)) (PreH37 : (0 <= A_r_eq_a)) (PreH38 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_35_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_a < SM2_P_Z)) (PreH35 : (0 <= B_r_eq_a)) (PreH36 : (A_r_eq_a < SM2_P_Z)) (PreH37 : (0 <= A_r_eq_a)) (PreH38 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_36_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_a < SM2_P_Z)) (PreH35 : (0 <= B_r_eq_a)) (PreH36 : (A_r_eq_a < SM2_P_Z)) (PreH37 : (0 <= A_r_eq_a)) (PreH38 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_37_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_b < SM2_P_Z)) (PreH35 : (0 <= B_r_eq_b)) (PreH36 : (A_r_eq_b < SM2_P_Z)) (PreH37 : (0 <= A_r_eq_b)) (PreH38 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_38_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_b < SM2_P_Z)) (PreH35 : (0 <= B_r_eq_b)) (PreH36 : (A_r_eq_b < SM2_P_Z)) (PreH37 : (0 <= A_r_eq_b)) (PreH38 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_39_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_b < SM2_P_Z)) (PreH35 : (0 <= B_r_eq_b)) (PreH36 : (A_r_eq_b < SM2_P_Z)) (PreH37 : (0 <= A_r_eq_b)) (PreH38 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_40_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_non_alias < SM2_P_Z)) (PreH41 : (0 <= B_non_alias)) (PreH42 : (A_non_alias < SM2_P_Z)) (PreH43 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_41_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_42_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_43_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_non_alias < SM2_P_Z)) (PreH41 : (0 <= B_non_alias)) (PreH42 : (A_non_alias < SM2_P_Z)) (PreH43 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_44_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_non_alias < SM2_P_Z)) (PreH41 : (0 <= B_non_alias)) (PreH42 : (A_non_alias < SM2_P_Z)) (PreH43 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_45_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_non_alias < SM2_P_Z)) (PreH41 : (0 <= B_non_alias)) (PreH42 : (A_non_alias < SM2_P_Z)) (PreH43 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_46_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_47_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_48_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_49_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_50_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_51_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_mod_p_safety_wit_52_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_4)) (PreH10 : (retval_4 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval_2)) (PreH20 : (retval_2 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH27 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_non_alias < SM2_P_Z)) (PreH46 : (0 <= B_non_alias)) (PreH47 : (A_non_alias < SM2_P_Z)) (PreH48 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_53_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_4)) (PreH10 : (retval_4 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval_2)) (PreH20 : (retval_2 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH27 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_non_alias < SM2_P_Z)) (PreH46 : (0 <= B_non_alias)) (PreH47 : (A_non_alias < SM2_P_Z)) (PreH48 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_54_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_4)) (PreH10 : (retval_4 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval_2)) (PreH20 : (retval_2 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH27 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_non_alias < SM2_P_Z)) (PreH46 : (0 <= B_non_alias)) (PreH47 : (A_non_alias < SM2_P_Z)) (PreH48 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_55_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_4)) (PreH10 : (retval_4 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval_2)) (PreH20 : (retval_2 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH27 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_a < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_a)) (PreH47 : (A_r_eq_a < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_a)) (PreH49 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_56_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_4)) (PreH10 : (retval_4 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval_2)) (PreH20 : (retval_2 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH27 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_a < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_a)) (PreH47 : (A_r_eq_a < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_a)) (PreH49 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_57_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_4)) (PreH10 : (retval_4 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval_2)) (PreH20 : (retval_2 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH27 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_a < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_a)) (PreH47 : (A_r_eq_a < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_a)) (PreH49 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_58_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_4)) (PreH10 : (retval_4 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval_2)) (PreH20 : (retval_2 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH27 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_b < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_b)) (PreH47 : (A_r_eq_b < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_b)) (PreH49 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_59_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_4)) (PreH10 : (retval_4 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval_2)) (PreH20 : (retval_2 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH27 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_b < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_b)) (PreH47 : (A_r_eq_b < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_b)) (PreH49 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_60_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_4)) (PreH10 : (retval_4 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval_2)) (PreH20 : (retval_2 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH27 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_b < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_b)) (PreH47 : (A_r_eq_b < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_b)) (PreH49 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sub_mod_p_safety_wit_61_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (retval_4 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH32 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_non_alias < SM2_P_Z)) (PreH51 : (0 <= B_non_alias)) (PreH52 : (A_non_alias < SM2_P_Z)) (PreH53 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  ((( &( "carry" ) )) # UChar  |-> retval_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_62_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (retval_4 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH32 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_non_alias < SM2_P_Z)) (PreH51 : (0 <= B_non_alias)) (PreH52 : (A_non_alias < SM2_P_Z)) (PreH53 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  ((( &( "carry" ) )) # UChar  |-> retval_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_63_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (retval_4 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH32 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_non_alias < SM2_P_Z)) (PreH51 : (0 <= B_non_alias)) (PreH52 : (A_non_alias < SM2_P_Z)) (PreH53 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  ((( &( "carry" ) )) # UChar  |-> retval_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_64_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (retval_4 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH32 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_a < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_a)) (PreH52 : (A_r_eq_a < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_a)) (PreH54 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  ((( &( "carry" ) )) # UChar  |-> retval_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_65_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (retval_4 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH32 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_a < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_a)) (PreH52 : (A_r_eq_a < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_a)) (PreH54 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  ((( &( "carry" ) )) # UChar  |-> retval_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_66_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (retval_4 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH32 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_a < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_a)) (PreH52 : (A_r_eq_a < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_a)) (PreH54 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  ((( &( "carry" ) )) # UChar  |-> retval_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_67_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (retval_4 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH32 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_b < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_b)) (PreH52 : (A_r_eq_b < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_b)) (PreH54 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  ((( &( "carry" ) )) # UChar  |-> retval_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_68_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (retval_4 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH32 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_b < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_b)) (PreH52 : (A_r_eq_b < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_b)) (PreH54 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  ((( &( "carry" ) )) # UChar  |-> retval_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_69_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (retval_4 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH32 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_b < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_b)) (PreH52 : (A_r_eq_b < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_b)) (PreH54 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  ((( &( "carry" ) )) # UChar  |-> retval_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sub_mod_p_safety_wit_70_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= out_4)) (PreH18 : (out_4 < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (0 <= out)) (PreH33 : (out < U64_MOD)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH37 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_non_alias < SM2_P_Z)) (PreH56 : (0 <= B_non_alias)) (PreH57 : (A_non_alias < SM2_P_Z)) (PreH58 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  ((( &( "carry" ) )) # UChar  |-> retval_7)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_71_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= out_4)) (PreH18 : (out_4 < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (0 <= out)) (PreH33 : (out < U64_MOD)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH37 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_non_alias < SM2_P_Z)) (PreH56 : (0 <= B_non_alias)) (PreH57 : (A_non_alias < SM2_P_Z)) (PreH58 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  ((( &( "carry" ) )) # UChar  |-> retval_7)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_72_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= out_4)) (PreH18 : (out_4 < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (0 <= out)) (PreH33 : (out < U64_MOD)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH37 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_non_alias < SM2_P_Z)) (PreH56 : (0 <= B_non_alias)) (PreH57 : (A_non_alias < SM2_P_Z)) (PreH58 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  ((( &( "carry" ) )) # UChar  |-> retval_7)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_73_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= out_4)) (PreH18 : (out_4 < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (0 <= out)) (PreH33 : (out < U64_MOD)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH37 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_r_eq_a < SM2_P_Z)) (PreH56 : (0 <= B_r_eq_a)) (PreH57 : (A_r_eq_a < SM2_P_Z)) (PreH58 : (0 <= A_r_eq_a)) (PreH59 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  ((( &( "carry" ) )) # UChar  |-> retval_7)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_74_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= out_4)) (PreH18 : (out_4 < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (0 <= out)) (PreH33 : (out < U64_MOD)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH37 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_r_eq_a < SM2_P_Z)) (PreH56 : (0 <= B_r_eq_a)) (PreH57 : (A_r_eq_a < SM2_P_Z)) (PreH58 : (0 <= A_r_eq_a)) (PreH59 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  ((( &( "carry" ) )) # UChar  |-> retval_7)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_75_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= out_4)) (PreH18 : (out_4 < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (0 <= out)) (PreH33 : (out < U64_MOD)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH37 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_r_eq_a < SM2_P_Z)) (PreH56 : (0 <= B_r_eq_a)) (PreH57 : (A_r_eq_a < SM2_P_Z)) (PreH58 : (0 <= A_r_eq_a)) (PreH59 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  ((( &( "carry" ) )) # UChar  |-> retval_7)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_76_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= out_4)) (PreH18 : (out_4 < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (0 <= out)) (PreH33 : (out < U64_MOD)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH37 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_r_eq_b < SM2_P_Z)) (PreH56 : (0 <= B_r_eq_b)) (PreH57 : (A_r_eq_b < SM2_P_Z)) (PreH58 : (0 <= A_r_eq_b)) (PreH59 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  ((( &( "carry" ) )) # UChar  |-> retval_7)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_77_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= out_4)) (PreH18 : (out_4 < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (0 <= out)) (PreH33 : (out < U64_MOD)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH37 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_r_eq_b < SM2_P_Z)) (PreH56 : (0 <= B_r_eq_b)) (PreH57 : (A_r_eq_b < SM2_P_Z)) (PreH58 : (0 <= A_r_eq_b)) (PreH59 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  ((( &( "carry" ) )) # UChar  |-> retval_7)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_safety_wit_78_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= out_4)) (PreH18 : (out_4 < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (0 <= out)) (PreH33 : (out < U64_MOD)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH37 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_r_eq_b < SM2_P_Z)) (PreH56 : (0 <= B_r_eq_b)) (PreH57 : (A_r_eq_b < SM2_P_Z)) (PreH58 : (0 <= A_r_eq_b)) (PreH59 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  ((( &( "carry" ) )) # UChar  |-> retval_7)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_mod_p_entail_wit_1_1_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_non_alias )
  **  (store_fp b_pre B_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  (“ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (store_u256 b_pre B_non_alias )
  **  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  ||
  (“ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (store_u256 b_pre B_r_eq_a )
  **  (store_u256 a_pre A_r_eq_a )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
  ||
  (“ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (store_u256 b_pre B_r_eq_b )
  **  (store_u256 a_pre A_r_eq_b )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
.

Definition sub_mod_p_entail_wit_1_2_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (PreH1 : (result_pre = a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_r_eq_a )
  **  (store_fp b_pre B_r_eq_a )
  **  (store_sm2_p )
|--
  (“ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (store_u256 b_pre B_non_alias )
  **  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  ||
  (“ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (store_u256 b_pre B_r_eq_a )
  **  (store_u256 a_pre A_r_eq_a )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
  ||
  (“ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (store_u256 b_pre B_r_eq_b )
  **  (store_u256 a_pre A_r_eq_b )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
.

Definition sub_mod_p_entail_wit_1_3_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (PreH1 : (result_pre = b_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_r_eq_b )
  **  (store_fp b_pre B_r_eq_b )
  **  (store_sm2_p )
|--
  (“ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (store_u256 b_pre B_non_alias )
  **  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  ||
  (“ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (store_u256 b_pre B_r_eq_a )
  **  (store_u256 a_pre A_r_eq_a )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
  ||
  (“ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (store_u256 b_pre B_r_eq_b )
  **  (store_u256 a_pre A_r_eq_b )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
.

Definition sub_mod_p_entail_wit_2_1_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (PreH1 : (B_non_alias < SM2_P_Z)) (PreH2 : (0 <= B_non_alias)) (PreH3 : (A_non_alias < SM2_P_Z)) (PreH4 : (0 <= A_non_alias)) ,
  (store_u256 b_pre B_non_alias )
  **  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (B_r_eq_a = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
  ||
  (EX (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (B_r_eq_b = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
.

Definition sub_mod_p_entail_wit_2_2_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (PreH1 : (B_r_eq_a < SM2_P_Z)) (PreH2 : (0 <= B_r_eq_a)) (PreH3 : (A_r_eq_a < SM2_P_Z)) (PreH4 : (0 <= A_r_eq_a)) (PreH5 : (result_pre = a_pre)) ,
  (store_u256 b_pre B_r_eq_a )
  **  (store_u256 a_pre A_r_eq_a )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (B_r_eq_a = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
  ||
  (EX (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (B_r_eq_b = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
.

Definition sub_mod_p_entail_wit_2_3_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (PreH1 : (B_r_eq_b < SM2_P_Z)) (PreH2 : (0 <= B_r_eq_b)) (PreH3 : (A_r_eq_b < SM2_P_Z)) (PreH4 : (0 <= A_r_eq_b)) (PreH5 : (result_pre = b_pre)) ,
  (store_u256 b_pre B_r_eq_b )
  **  (store_u256 a_pre A_r_eq_b )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (B_r_eq_a = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
  ||
  (EX (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (B_r_eq_b = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p ))
.

Definition sub_mod_p_entail_wit_3_1_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_non_alias < SM2_P_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_P_Z)) (PreH22 : (0 <= A_non_alias)) ,
  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  (“ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (B_r_eq_a = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (B_r_eq_b = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition sub_mod_p_entail_wit_3_2_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (B_r_eq_a = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (A_r_eq_a = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (B_r_eq_a < SM2_P_Z)) (PreH20 : (0 <= B_r_eq_a)) (PreH21 : (A_r_eq_a < SM2_P_Z)) (PreH22 : (0 <= A_r_eq_a)) (PreH23 : (result_pre = a_pre)) ,
  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 ))
  ||
  (“ (B_r_eq_a = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (B_r_eq_b = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition sub_mod_p_entail_wit_3_3_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH2 : (x3_6 < U64_MOD)) (PreH3 : (0 <= x3_6)) (PreH4 : (x2_6 < U64_MOD)) (PreH5 : (0 <= x2_6)) (PreH6 : (x1_6 < U64_MOD)) (PreH7 : (0 <= x1_6)) (PreH8 : (x0_6 < U64_MOD)) (PreH9 : (0 <= x0_6)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH11 : (x3_5 < U64_MOD)) (PreH12 : (0 <= x3_5)) (PreH13 : (x2_5 < U64_MOD)) (PreH14 : (0 <= x2_5)) (PreH15 : (x1_5 < U64_MOD)) (PreH16 : (0 <= x1_5)) (PreH17 : (x0_5 < U64_MOD)) (PreH18 : (0 <= x0_5)) (PreH19 : (B_r_eq_b < SM2_P_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_P_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (B_r_eq_a = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (B_r_eq_b = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition sub_mod_p_return_wit_1_non_alias := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_P_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_P_Z)) (PreH63 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  (store_fp a_pre A_non_alias )
  **  (store_fp b_pre B_non_alias )
  **  (store_fp result_pre (Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
) \/
(
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_P_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_P_Z)) (PreH63 : (0 <= A_non_alias)) ,
  TT && emp 
|--
  “ (0 <= (Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z)) = (u256_of_limbs (out_5) (out_6) (out_7) (out_8))) ”
  &&  emp
).

Definition sub_mod_p_return_wit_1_non_alias_split_goal_1 := 
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_P_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_P_Z)) (PreH63 : (0 <= A_non_alias)) ,
  (0 <= (Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z)))
.

Definition sub_mod_p_return_wit_1_non_alias_split_goal_2 := 
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_P_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_P_Z)) (PreH63 : (0 <= A_non_alias)) ,
  ((Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z)) < SM2_P_Z)
.

Definition sub_mod_p_return_wit_1_non_alias_split_goal_3 := 
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_P_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_P_Z)) (PreH63 : (0 <= A_non_alias)) ,
  ((Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z)) = (u256_of_limbs (out_5) (out_6) (out_7) (out_8)))
.

Definition sub_mod_p_return_wit_2_r_eq_a := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_a < SM2_P_Z)) (PreH61 : (0 <= B_r_eq_a)) (PreH62 : (A_r_eq_a < SM2_P_Z)) (PreH63 : (0 <= A_r_eq_a)) (PreH64 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (result_pre = a_pre) ”
  &&  (store_fp result_pre (Zmod ((A_r_eq_a - B_r_eq_a )) (SM2_P_Z)) )
  **  (store_fp b_pre B_r_eq_a )
  **  (store_sm2_p )
) \/
(
forall (result_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_a < SM2_P_Z)) (PreH61 : (0 <= B_r_eq_a)) (PreH62 : (A_r_eq_a < SM2_P_Z)) (PreH63 : (0 <= A_r_eq_a)) (PreH64 : (result_pre = a_pre)) ,
  TT && emp 
|--
  “ (0 <= (Zmod ((A_r_eq_a - B_r_eq_a )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((A_r_eq_a - B_r_eq_a )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_r_eq_a - B_r_eq_a )) (SM2_P_Z)) = (u256_of_limbs (out_5) (out_6) (out_7) (out_8))) ”
  &&  emp
).

Definition sub_mod_p_return_wit_2_r_eq_a_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_a < SM2_P_Z)) (PreH61 : (0 <= B_r_eq_a)) (PreH62 : (A_r_eq_a < SM2_P_Z)) (PreH63 : (0 <= A_r_eq_a)) (PreH64 : (result_pre = a_pre)) ,
  (0 <= (Zmod ((A_r_eq_a - B_r_eq_a )) (SM2_P_Z)))
.

Definition sub_mod_p_return_wit_2_r_eq_a_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_a < SM2_P_Z)) (PreH61 : (0 <= B_r_eq_a)) (PreH62 : (A_r_eq_a < SM2_P_Z)) (PreH63 : (0 <= A_r_eq_a)) (PreH64 : (result_pre = a_pre)) ,
  ((Zmod ((A_r_eq_a - B_r_eq_a )) (SM2_P_Z)) < SM2_P_Z)
.

Definition sub_mod_p_return_wit_2_r_eq_a_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_a < SM2_P_Z)) (PreH61 : (0 <= B_r_eq_a)) (PreH62 : (A_r_eq_a < SM2_P_Z)) (PreH63 : (0 <= A_r_eq_a)) (PreH64 : (result_pre = a_pre)) ,
  ((Zmod ((A_r_eq_a - B_r_eq_a )) (SM2_P_Z)) = (u256_of_limbs (out_5) (out_6) (out_7) (out_8)))
.

Definition sub_mod_p_return_wit_3_r_eq_b := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_P_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_P_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (result_pre = b_pre) ”
  &&  (store_fp a_pre A_r_eq_b )
  **  (store_fp result_pre (Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z)) )
  **  (store_sm2_p )
) \/
(
forall (result_pre: Z) (b_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_P_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_P_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  TT && emp 
|--
  “ (0 <= (Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z)) = (u256_of_limbs (out_5) (out_6) (out_7) (out_8))) ”
  &&  emp
).

Definition sub_mod_p_return_wit_3_r_eq_b_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_P_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_P_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  (0 <= (Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z)))
.

Definition sub_mod_p_return_wit_3_r_eq_b_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_P_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_P_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  ((Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z)) < SM2_P_Z)
.

Definition sub_mod_p_return_wit_3_r_eq_b_split_goal_3 := 
forall (result_pre: Z) (b_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (0 <= out_8)) (PreH2 : (out_8 < U64_MOD)) (PreH3 : (0 <= retval_8)) (PreH4 : (retval_8 <= 1)) (PreH5 : (((out_4 + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH6 : (0 <= out_7)) (PreH7 : (out_7 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_6)) (PreH12 : (out_6 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out_5)) (PreH17 : (out_5 < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH21 : (retval_4 = 0)) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_P_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_P_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  ((Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z)) = (u256_of_limbs (out_5) (out_6) (out_7) (out_8)))
.

Definition sub_mod_p_return_wit_4_non_alias := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_non_alias < SM2_P_Z)) (PreH41 : (0 <= B_non_alias)) (PreH42 : (A_non_alias < SM2_P_Z)) (PreH43 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  (store_fp a_pre A_non_alias )
  **  (store_fp b_pre B_non_alias )
  **  (store_fp result_pre (Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
) \/
(
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_non_alias < SM2_P_Z)) (PreH41 : (0 <= B_non_alias)) (PreH42 : (A_non_alias < SM2_P_Z)) (PreH43 : (0 <= A_non_alias)) ,
  TT && emp 
|--
  “ (0 <= (Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z)) = (u256_of_limbs (out) (out_2) (out_3) (out_4))) ”
  &&  emp
).

Definition sub_mod_p_return_wit_4_non_alias_split_goal_1 := 
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_non_alias < SM2_P_Z)) (PreH41 : (0 <= B_non_alias)) (PreH42 : (A_non_alias < SM2_P_Z)) (PreH43 : (0 <= A_non_alias)) ,
  (0 <= (Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z)))
.

Definition sub_mod_p_return_wit_4_non_alias_split_goal_2 := 
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_non_alias < SM2_P_Z)) (PreH41 : (0 <= B_non_alias)) (PreH42 : (A_non_alias < SM2_P_Z)) (PreH43 : (0 <= A_non_alias)) ,
  ((Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z)) < SM2_P_Z)
.

Definition sub_mod_p_return_wit_4_non_alias_split_goal_3 := 
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_non_alias < SM2_P_Z)) (PreH41 : (0 <= B_non_alias)) (PreH42 : (A_non_alias < SM2_P_Z)) (PreH43 : (0 <= A_non_alias)) ,
  ((Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z)) = (u256_of_limbs (out) (out_2) (out_3) (out_4)))
.

Definition sub_mod_p_return_wit_5_r_eq_a := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (result_pre = a_pre) ”
  &&  (store_fp result_pre (Zmod ((A_r_eq_a - B_r_eq_a )) (SM2_P_Z)) )
  **  (store_fp b_pre B_r_eq_a )
  **  (store_sm2_p )
) \/
(
forall (result_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  TT && emp 
|--
  “ (0 <= (Zmod ((A_r_eq_a - B_r_eq_a )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((A_r_eq_a - B_r_eq_a )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_r_eq_a - B_r_eq_a )) (SM2_P_Z)) = (u256_of_limbs (out) (out_2) (out_3) (out_4))) ”
  &&  emp
).

Definition sub_mod_p_return_wit_5_r_eq_a_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  (0 <= (Zmod ((A_r_eq_a - B_r_eq_a )) (SM2_P_Z)))
.

Definition sub_mod_p_return_wit_5_r_eq_a_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  ((Zmod ((A_r_eq_a - B_r_eq_a )) (SM2_P_Z)) < SM2_P_Z)
.

Definition sub_mod_p_return_wit_5_r_eq_a_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  ((Zmod ((A_r_eq_a - B_r_eq_a )) (SM2_P_Z)) = (u256_of_limbs (out) (out_2) (out_3) (out_4)))
.

Definition sub_mod_p_return_wit_6_r_eq_b := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (result_pre = b_pre) ”
  &&  (store_fp a_pre A_r_eq_b )
  **  (store_fp result_pre (Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z)) )
  **  (store_sm2_p )
) \/
(
forall (result_pre: Z) (b_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  TT && emp 
|--
  “ (0 <= (Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z)) = (u256_of_limbs (out) (out_2) (out_3) (out_4))) ”
  &&  emp
).

Definition sub_mod_p_return_wit_6_r_eq_b_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  (0 <= (Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z)))
.

Definition sub_mod_p_return_wit_6_r_eq_b_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  ((Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z)) < SM2_P_Z)
.

Definition sub_mod_p_return_wit_6_r_eq_b_split_goal_3 := 
forall (result_pre: Z) (b_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  ((Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z)) = (u256_of_limbs (out) (out_2) (out_3) (out_4)))
.

Definition sub_mod_p_partial_solve_wit_1_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_non_alias < SM2_P_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_P_Z)) (PreH22 : (0 <= A_non_alias)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x0_2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (B_non_alias < SM2_P_Z)) (PreH36 : (0 <= B_non_alias)) (PreH37 : (A_non_alias < SM2_P_Z)) (PreH38 : (0 <= A_non_alias)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x0_2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0_2)) (64)) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_1_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (B_non_alias < SM2_P_Z)) (PreH36 : (0 <= B_non_alias)) (PreH37 : (A_non_alias < SM2_P_Z)) (PreH38 : (0 <= A_non_alias)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x0_2)) (64))) ”
.

Definition sub_mod_p_partial_solve_wit_1_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (B_non_alias < SM2_P_Z)) (PreH36 : (0 <= B_non_alias)) (PreH37 : (A_non_alias < SM2_P_Z)) (PreH38 : (0 <= A_non_alias)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ ((unsigned_last_nbits ((Z.lnot x0_2)) (64)) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_1_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_non_alias < SM2_P_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_P_Z)) (PreH22 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x0_2)) (64))) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_1_non_alias := sub_mod_p_partial_solve_wit_1_non_alias_pure -> sub_mod_p_partial_solve_wit_1_non_alias_aux.

Definition sub_mod_p_partial_solve_wit_2_r_eq_a_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_a < SM2_P_Z)) (PreH20 : (0 <= B_r_eq_a)) (PreH21 : (A_r_eq_a < SM2_P_Z)) (PreH22 : (0 <= A_r_eq_a)) (PreH23 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x0_2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (B_r_eq_a < SM2_P_Z)) (PreH36 : (0 <= B_r_eq_a)) (PreH37 : (A_r_eq_a < SM2_P_Z)) (PreH38 : (0 <= A_r_eq_a)) (PreH39 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x0_2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0_2)) (64)) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_2_r_eq_a_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (B_r_eq_a < SM2_P_Z)) (PreH36 : (0 <= B_r_eq_a)) (PreH37 : (A_r_eq_a < SM2_P_Z)) (PreH38 : (0 <= A_r_eq_a)) (PreH39 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x0_2)) (64))) ”
.

Definition sub_mod_p_partial_solve_wit_2_r_eq_a_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (B_r_eq_a < SM2_P_Z)) (PreH36 : (0 <= B_r_eq_a)) (PreH37 : (A_r_eq_a < SM2_P_Z)) (PreH38 : (0 <= A_r_eq_a)) (PreH39 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x0_2)) (64)) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_2_r_eq_a_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_a < SM2_P_Z)) (PreH20 : (0 <= B_r_eq_a)) (PreH21 : (A_r_eq_a < SM2_P_Z)) (PreH22 : (0 <= A_r_eq_a)) (PreH23 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x0_2)) (64))) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
.

Definition sub_mod_p_partial_solve_wit_2_r_eq_a := sub_mod_p_partial_solve_wit_2_r_eq_a_pure -> sub_mod_p_partial_solve_wit_2_r_eq_a_aux.

Definition sub_mod_p_partial_solve_wit_3_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_b < SM2_P_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_P_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x0_2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (B_r_eq_b < SM2_P_Z)) (PreH36 : (0 <= B_r_eq_b)) (PreH37 : (A_r_eq_b < SM2_P_Z)) (PreH38 : (0 <= A_r_eq_b)) (PreH39 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x0_2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0_2)) (64)) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_3_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (B_r_eq_b < SM2_P_Z)) (PreH36 : (0 <= B_r_eq_b)) (PreH37 : (A_r_eq_b < SM2_P_Z)) (PreH38 : (0 <= A_r_eq_b)) (PreH39 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x0_2)) (64))) ”
.

Definition sub_mod_p_partial_solve_wit_3_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (B_r_eq_b < SM2_P_Z)) (PreH36 : (0 <= B_r_eq_b)) (PreH37 : (A_r_eq_b < SM2_P_Z)) (PreH38 : (0 <= A_r_eq_b)) (PreH39 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x0_2)) (64)) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_3_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_b < SM2_P_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_P_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x0_2)) (64))) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_3_r_eq_b := sub_mod_p_partial_solve_wit_3_r_eq_b_pure -> sub_mod_p_partial_solve_wit_3_r_eq_b_aux.

Definition sub_mod_p_partial_solve_wit_4_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_non_alias < SM2_P_Z)) (PreH25 : (0 <= B_non_alias)) (PreH26 : (A_non_alias < SM2_P_Z)) (PreH27 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x1_2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (x0 >= 0)) (PreH11 : (x1 >= 0)) (PreH12 : (x2 >= 0)) (PreH13 : (x3 >= 0)) (PreH14 : (x0_2 >= 0)) (PreH15 : (x1_2 >= 0)) (PreH16 : (x2_2 >= 0)) (PreH17 : (x3_2 >= 0)) (PreH18 : (out >= 0)) (PreH19 : (0 <= out)) (PreH20 : (out < U64_MOD)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH24 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) (PreH42 : (B_non_alias < SM2_P_Z)) (PreH43 : (0 <= B_non_alias)) (PreH44 : (A_non_alias < SM2_P_Z)) (PreH45 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x1_2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1_2)) (64)) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (x0 >= 0)) (PreH11 : (x1 >= 0)) (PreH12 : (x2 >= 0)) (PreH13 : (x3 >= 0)) (PreH14 : (x0_2 >= 0)) (PreH15 : (x1_2 >= 0)) (PreH16 : (x2_2 >= 0)) (PreH17 : (x3_2 >= 0)) (PreH18 : (out >= 0)) (PreH19 : (0 <= out)) (PreH20 : (out < U64_MOD)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH24 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) (PreH42 : (B_non_alias < SM2_P_Z)) (PreH43 : (0 <= B_non_alias)) (PreH44 : (A_non_alias < SM2_P_Z)) (PreH45 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x1_2)) (64))) ”
.

Definition sub_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (x0 >= 0)) (PreH11 : (x1 >= 0)) (PreH12 : (x2 >= 0)) (PreH13 : (x3 >= 0)) (PreH14 : (x0_2 >= 0)) (PreH15 : (x1_2 >= 0)) (PreH16 : (x2_2 >= 0)) (PreH17 : (x3_2 >= 0)) (PreH18 : (out >= 0)) (PreH19 : (0 <= out)) (PreH20 : (out < U64_MOD)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH24 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) (PreH42 : (B_non_alias < SM2_P_Z)) (PreH43 : (0 <= B_non_alias)) (PreH44 : (A_non_alias < SM2_P_Z)) (PreH45 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x1_2)) (64)) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_4_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_non_alias < SM2_P_Z)) (PreH25 : (0 <= B_non_alias)) (PreH26 : (A_non_alias < SM2_P_Z)) (PreH27 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x1_2)) (64))) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_4_non_alias := sub_mod_p_partial_solve_wit_4_non_alias_pure -> sub_mod_p_partial_solve_wit_4_non_alias_aux.

Definition sub_mod_p_partial_solve_wit_5_r_eq_a_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_a < SM2_P_Z)) (PreH25 : (0 <= B_r_eq_a)) (PreH26 : (A_r_eq_a < SM2_P_Z)) (PreH27 : (0 <= A_r_eq_a)) (PreH28 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x1_2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x1 <= UINT64_MAX)) (PreH2 : (x2 <= UINT64_MAX)) (PreH3 : (x3 <= UINT64_MAX)) (PreH4 : (x0_2 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out <= UINT64_MAX)) (PreH9 : (x1 >= 0)) (PreH10 : (x2 >= 0)) (PreH11 : (x3 >= 0)) (PreH12 : (x0_2 >= 0)) (PreH13 : (x1_2 >= 0)) (PreH14 : (x2_2 >= 0)) (PreH15 : (x3_2 >= 0)) (PreH16 : (out >= 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x1_2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1_2)) (64)) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_5_r_eq_a_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x1 <= UINT64_MAX)) (PreH2 : (x2 <= UINT64_MAX)) (PreH3 : (x3 <= UINT64_MAX)) (PreH4 : (x0_2 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out <= UINT64_MAX)) (PreH9 : (x1 >= 0)) (PreH10 : (x2 >= 0)) (PreH11 : (x3 >= 0)) (PreH12 : (x0_2 >= 0)) (PreH13 : (x1_2 >= 0)) (PreH14 : (x2_2 >= 0)) (PreH15 : (x3_2 >= 0)) (PreH16 : (out >= 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x1_2)) (64))) ”
.

Definition sub_mod_p_partial_solve_wit_5_r_eq_a_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x1 <= UINT64_MAX)) (PreH2 : (x2 <= UINT64_MAX)) (PreH3 : (x3 <= UINT64_MAX)) (PreH4 : (x0_2 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out <= UINT64_MAX)) (PreH9 : (x1 >= 0)) (PreH10 : (x2 >= 0)) (PreH11 : (x3 >= 0)) (PreH12 : (x0_2 >= 0)) (PreH13 : (x1_2 >= 0)) (PreH14 : (x2_2 >= 0)) (PreH15 : (x3_2 >= 0)) (PreH16 : (out >= 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x1_2)) (64)) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_5_r_eq_a_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_a < SM2_P_Z)) (PreH25 : (0 <= B_r_eq_a)) (PreH26 : (A_r_eq_a < SM2_P_Z)) (PreH27 : (0 <= A_r_eq_a)) (PreH28 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x1_2)) (64))) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
.

Definition sub_mod_p_partial_solve_wit_5_r_eq_a := sub_mod_p_partial_solve_wit_5_r_eq_a_pure -> sub_mod_p_partial_solve_wit_5_r_eq_a_aux.

Definition sub_mod_p_partial_solve_wit_6_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_b < SM2_P_Z)) (PreH25 : (0 <= B_r_eq_b)) (PreH26 : (A_r_eq_b < SM2_P_Z)) (PreH27 : (0 <= A_r_eq_b)) (PreH28 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x1_2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x1_2 >= 0)) (PreH14 : (x2_2 >= 0)) (PreH15 : (x3_2 >= 0)) (PreH16 : (out >= 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x1_2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1_2)) (64)) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_6_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x1_2 >= 0)) (PreH14 : (x2_2 >= 0)) (PreH15 : (x3_2 >= 0)) (PreH16 : (out >= 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x1_2)) (64))) ”
.

Definition sub_mod_p_partial_solve_wit_6_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x1_2 >= 0)) (PreH14 : (x2_2 >= 0)) (PreH15 : (x3_2 >= 0)) (PreH16 : (out >= 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x1_2)) (64)) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_6_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_b < SM2_P_Z)) (PreH25 : (0 <= B_r_eq_b)) (PreH26 : (A_r_eq_b < SM2_P_Z)) (PreH27 : (0 <= A_r_eq_b)) (PreH28 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x1_2)) (64))) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_6_r_eq_b := sub_mod_p_partial_solve_wit_6_r_eq_b_pure -> sub_mod_p_partial_solve_wit_6_r_eq_b_aux.

Definition sub_mod_p_partial_solve_wit_7_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_non_alias < SM2_P_Z)) (PreH30 : (0 <= B_non_alias)) (PreH31 : (A_non_alias < SM2_P_Z)) (PreH32 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x2_2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (x0 >= 0)) (PreH12 : (x1 >= 0)) (PreH13 : (x2 >= 0)) (PreH14 : (x3 >= 0)) (PreH15 : (x0_2 >= 0)) (PreH16 : (x1_2 >= 0)) (PreH17 : (x2_2 >= 0)) (PreH18 : (x3_2 >= 0)) (PreH19 : (out >= 0)) (PreH20 : (out_2 >= 0)) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH31 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_non_alias < SM2_P_Z)) (PreH50 : (0 <= B_non_alias)) (PreH51 : (A_non_alias < SM2_P_Z)) (PreH52 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x2_2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2_2)) (64)) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_7_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (x0 >= 0)) (PreH12 : (x1 >= 0)) (PreH13 : (x2 >= 0)) (PreH14 : (x3 >= 0)) (PreH15 : (x0_2 >= 0)) (PreH16 : (x1_2 >= 0)) (PreH17 : (x2_2 >= 0)) (PreH18 : (x3_2 >= 0)) (PreH19 : (out >= 0)) (PreH20 : (out_2 >= 0)) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH31 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_non_alias < SM2_P_Z)) (PreH50 : (0 <= B_non_alias)) (PreH51 : (A_non_alias < SM2_P_Z)) (PreH52 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x2_2)) (64))) ”
.

Definition sub_mod_p_partial_solve_wit_7_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (x0 >= 0)) (PreH12 : (x1 >= 0)) (PreH13 : (x2 >= 0)) (PreH14 : (x3 >= 0)) (PreH15 : (x0_2 >= 0)) (PreH16 : (x1_2 >= 0)) (PreH17 : (x2_2 >= 0)) (PreH18 : (x3_2 >= 0)) (PreH19 : (out >= 0)) (PreH20 : (out_2 >= 0)) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH31 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_non_alias < SM2_P_Z)) (PreH50 : (0 <= B_non_alias)) (PreH51 : (A_non_alias < SM2_P_Z)) (PreH52 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x2_2)) (64)) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_7_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_non_alias < SM2_P_Z)) (PreH30 : (0 <= B_non_alias)) (PreH31 : (A_non_alias < SM2_P_Z)) (PreH32 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x2_2)) (64))) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "u32" ->ₛ "v") 2 (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_7_non_alias := sub_mod_p_partial_solve_wit_7_non_alias_pure -> sub_mod_p_partial_solve_wit_7_non_alias_aux.

Definition sub_mod_p_partial_solve_wit_8_r_eq_a_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_a < SM2_P_Z)) (PreH30 : (0 <= B_r_eq_a)) (PreH31 : (A_r_eq_a < SM2_P_Z)) (PreH32 : (0 <= A_r_eq_a)) (PreH33 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x2_2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x2 <= UINT64_MAX)) (PreH2 : (x3 <= UINT64_MAX)) (PreH3 : (x0_2 <= UINT64_MAX)) (PreH4 : (x1_2 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (x2 >= 0)) (PreH10 : (x3 >= 0)) (PreH11 : (x0_2 >= 0)) (PreH12 : (x1_2 >= 0)) (PreH13 : (x2_2 >= 0)) (PreH14 : (x3_2 >= 0)) (PreH15 : (out >= 0)) (PreH16 : (out_2 >= 0)) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH27 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_a < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_a)) (PreH47 : (A_r_eq_a < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_a)) (PreH49 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x2_2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2_2)) (64)) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_8_r_eq_a_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x2 <= UINT64_MAX)) (PreH2 : (x3 <= UINT64_MAX)) (PreH3 : (x0_2 <= UINT64_MAX)) (PreH4 : (x1_2 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (x2 >= 0)) (PreH10 : (x3 >= 0)) (PreH11 : (x0_2 >= 0)) (PreH12 : (x1_2 >= 0)) (PreH13 : (x2_2 >= 0)) (PreH14 : (x3_2 >= 0)) (PreH15 : (out >= 0)) (PreH16 : (out_2 >= 0)) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH27 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_a < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_a)) (PreH47 : (A_r_eq_a < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_a)) (PreH49 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x2_2)) (64))) ”
.

Definition sub_mod_p_partial_solve_wit_8_r_eq_a_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x2 <= UINT64_MAX)) (PreH2 : (x3 <= UINT64_MAX)) (PreH3 : (x0_2 <= UINT64_MAX)) (PreH4 : (x1_2 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (x2 >= 0)) (PreH10 : (x3 >= 0)) (PreH11 : (x0_2 >= 0)) (PreH12 : (x1_2 >= 0)) (PreH13 : (x2_2 >= 0)) (PreH14 : (x3_2 >= 0)) (PreH15 : (out >= 0)) (PreH16 : (out_2 >= 0)) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH27 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_a < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_a)) (PreH47 : (A_r_eq_a < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_a)) (PreH49 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x2_2)) (64)) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_8_r_eq_a_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_a < SM2_P_Z)) (PreH30 : (0 <= B_r_eq_a)) (PreH31 : (A_r_eq_a < SM2_P_Z)) (PreH32 : (0 <= A_r_eq_a)) (PreH33 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x2_2)) (64))) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
.

Definition sub_mod_p_partial_solve_wit_8_r_eq_a := sub_mod_p_partial_solve_wit_8_r_eq_a_pure -> sub_mod_p_partial_solve_wit_8_r_eq_a_aux.

Definition sub_mod_p_partial_solve_wit_9_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_b < SM2_P_Z)) (PreH30 : (0 <= B_r_eq_b)) (PreH31 : (A_r_eq_b < SM2_P_Z)) (PreH32 : (0 <= A_r_eq_b)) (PreH33 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x2_2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x2_2 >= 0)) (PreH14 : (x3_2 >= 0)) (PreH15 : (out >= 0)) (PreH16 : (out_2 >= 0)) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH27 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_b < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_b)) (PreH47 : (A_r_eq_b < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_b)) (PreH49 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x2_2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2_2)) (64)) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_9_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x2_2 >= 0)) (PreH14 : (x3_2 >= 0)) (PreH15 : (out >= 0)) (PreH16 : (out_2 >= 0)) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH27 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_b < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_b)) (PreH47 : (A_r_eq_b < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_b)) (PreH49 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x2_2)) (64))) ”
.

Definition sub_mod_p_partial_solve_wit_9_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x2_2 >= 0)) (PreH14 : (x3_2 >= 0)) (PreH15 : (out >= 0)) (PreH16 : (out_2 >= 0)) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH27 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_b < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_b)) (PreH47 : (A_r_eq_b < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_b)) (PreH49 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x2_2)) (64)) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_9_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_b < SM2_P_Z)) (PreH30 : (0 <= B_r_eq_b)) (PreH31 : (A_r_eq_b < SM2_P_Z)) (PreH32 : (0 <= A_r_eq_b)) (PreH33 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x2_2)) (64))) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_9_r_eq_b := sub_mod_p_partial_solve_wit_9_r_eq_b_pure -> sub_mod_p_partial_solve_wit_9_r_eq_b_aux.

Definition sub_mod_p_partial_solve_wit_10_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_non_alias < SM2_P_Z)) (PreH35 : (0 <= B_non_alias)) (PreH36 : (A_non_alias < SM2_P_Z)) (PreH37 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x3_2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (x0 >= 0)) (PreH13 : (x1 >= 0)) (PreH14 : (x2 >= 0)) (PreH15 : (x3 >= 0)) (PreH16 : (x0_2 >= 0)) (PreH17 : (x1_2 >= 0)) (PreH18 : (x2_2 >= 0)) (PreH19 : (x3_2 >= 0)) (PreH20 : (out >= 0)) (PreH21 : (out_2 >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_3)) (PreH31 : (retval_3 <= 1)) (PreH32 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_2)) (PreH36 : (retval_2 <= 1)) (PreH37 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH38 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH39 : (x3_2 < U64_MOD)) (PreH40 : (0 <= x3_2)) (PreH41 : (x2_2 < U64_MOD)) (PreH42 : (0 <= x2_2)) (PreH43 : (x1_2 < U64_MOD)) (PreH44 : (0 <= x1_2)) (PreH45 : (x0_2 < U64_MOD)) (PreH46 : (0 <= x0_2)) (PreH47 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH48 : (x3 < U64_MOD)) (PreH49 : (0 <= x3)) (PreH50 : (x2 < U64_MOD)) (PreH51 : (0 <= x2)) (PreH52 : (x1 < U64_MOD)) (PreH53 : (0 <= x1)) (PreH54 : (x0 < U64_MOD)) (PreH55 : (0 <= x0)) (PreH56 : (B_non_alias < SM2_P_Z)) (PreH57 : (0 <= B_non_alias)) (PreH58 : (A_non_alias < SM2_P_Z)) (PreH59 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x3_2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3_2)) (64)) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (x0 >= 0)) (PreH13 : (x1 >= 0)) (PreH14 : (x2 >= 0)) (PreH15 : (x3 >= 0)) (PreH16 : (x0_2 >= 0)) (PreH17 : (x1_2 >= 0)) (PreH18 : (x2_2 >= 0)) (PreH19 : (x3_2 >= 0)) (PreH20 : (out >= 0)) (PreH21 : (out_2 >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_3)) (PreH31 : (retval_3 <= 1)) (PreH32 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_2)) (PreH36 : (retval_2 <= 1)) (PreH37 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH38 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH39 : (x3_2 < U64_MOD)) (PreH40 : (0 <= x3_2)) (PreH41 : (x2_2 < U64_MOD)) (PreH42 : (0 <= x2_2)) (PreH43 : (x1_2 < U64_MOD)) (PreH44 : (0 <= x1_2)) (PreH45 : (x0_2 < U64_MOD)) (PreH46 : (0 <= x0_2)) (PreH47 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH48 : (x3 < U64_MOD)) (PreH49 : (0 <= x3)) (PreH50 : (x2 < U64_MOD)) (PreH51 : (0 <= x2)) (PreH52 : (x1 < U64_MOD)) (PreH53 : (0 <= x1)) (PreH54 : (x0 < U64_MOD)) (PreH55 : (0 <= x0)) (PreH56 : (B_non_alias < SM2_P_Z)) (PreH57 : (0 <= B_non_alias)) (PreH58 : (A_non_alias < SM2_P_Z)) (PreH59 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x3_2)) (64))) ”
.

Definition sub_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (x0 >= 0)) (PreH13 : (x1 >= 0)) (PreH14 : (x2 >= 0)) (PreH15 : (x3 >= 0)) (PreH16 : (x0_2 >= 0)) (PreH17 : (x1_2 >= 0)) (PreH18 : (x2_2 >= 0)) (PreH19 : (x3_2 >= 0)) (PreH20 : (out >= 0)) (PreH21 : (out_2 >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_3)) (PreH31 : (retval_3 <= 1)) (PreH32 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_2)) (PreH36 : (retval_2 <= 1)) (PreH37 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH38 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH39 : (x3_2 < U64_MOD)) (PreH40 : (0 <= x3_2)) (PreH41 : (x2_2 < U64_MOD)) (PreH42 : (0 <= x2_2)) (PreH43 : (x1_2 < U64_MOD)) (PreH44 : (0 <= x1_2)) (PreH45 : (x0_2 < U64_MOD)) (PreH46 : (0 <= x0_2)) (PreH47 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH48 : (x3 < U64_MOD)) (PreH49 : (0 <= x3)) (PreH50 : (x2 < U64_MOD)) (PreH51 : (0 <= x2)) (PreH52 : (x1 < U64_MOD)) (PreH53 : (0 <= x1)) (PreH54 : (x0 < U64_MOD)) (PreH55 : (0 <= x0)) (PreH56 : (B_non_alias < SM2_P_Z)) (PreH57 : (0 <= B_non_alias)) (PreH58 : (A_non_alias < SM2_P_Z)) (PreH59 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x3_2)) (64)) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_10_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_non_alias < SM2_P_Z)) (PreH35 : (0 <= B_non_alias)) (PreH36 : (A_non_alias < SM2_P_Z)) (PreH37 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x3_2)) (64))) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "u32" ->ₛ "v") 3 ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_10_non_alias := sub_mod_p_partial_solve_wit_10_non_alias_pure -> sub_mod_p_partial_solve_wit_10_non_alias_aux.

Definition sub_mod_p_partial_solve_wit_11_r_eq_a_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_a < SM2_P_Z)) (PreH35 : (0 <= B_r_eq_a)) (PreH36 : (A_r_eq_a < SM2_P_Z)) (PreH37 : (0 <= A_r_eq_a)) (PreH38 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x3_2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x3 <= UINT64_MAX)) (PreH2 : (x0_2 <= UINT64_MAX)) (PreH3 : (x1_2 <= UINT64_MAX)) (PreH4 : (x2_2 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (x3 >= 0)) (PreH10 : (x0_2 >= 0)) (PreH11 : (x1_2 >= 0)) (PreH12 : (x2_2 >= 0)) (PreH13 : (x3_2 >= 0)) (PreH14 : (out >= 0)) (PreH15 : (out_2 >= 0)) (PreH16 : (out_3 >= 0)) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH32 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_a < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_a)) (PreH52 : (A_r_eq_a < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_a)) (PreH54 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x3_2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3_2)) (64)) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_11_r_eq_a_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x3 <= UINT64_MAX)) (PreH2 : (x0_2 <= UINT64_MAX)) (PreH3 : (x1_2 <= UINT64_MAX)) (PreH4 : (x2_2 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (x3 >= 0)) (PreH10 : (x0_2 >= 0)) (PreH11 : (x1_2 >= 0)) (PreH12 : (x2_2 >= 0)) (PreH13 : (x3_2 >= 0)) (PreH14 : (out >= 0)) (PreH15 : (out_2 >= 0)) (PreH16 : (out_3 >= 0)) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH32 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_a < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_a)) (PreH52 : (A_r_eq_a < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_a)) (PreH54 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x3_2)) (64))) ”
.

Definition sub_mod_p_partial_solve_wit_11_r_eq_a_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x3 <= UINT64_MAX)) (PreH2 : (x0_2 <= UINT64_MAX)) (PreH3 : (x1_2 <= UINT64_MAX)) (PreH4 : (x2_2 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (x3 >= 0)) (PreH10 : (x0_2 >= 0)) (PreH11 : (x1_2 >= 0)) (PreH12 : (x2_2 >= 0)) (PreH13 : (x3_2 >= 0)) (PreH14 : (out >= 0)) (PreH15 : (out_2 >= 0)) (PreH16 : (out_3 >= 0)) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH32 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_a < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_a)) (PreH52 : (A_r_eq_a < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_a)) (PreH54 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x3_2)) (64)) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_11_r_eq_a_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_a < SM2_P_Z)) (PreH35 : (0 <= B_r_eq_a)) (PreH36 : (A_r_eq_a < SM2_P_Z)) (PreH37 : (0 <= A_r_eq_a)) (PreH38 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x3_2)) (64))) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition sub_mod_p_partial_solve_wit_11_r_eq_a := sub_mod_p_partial_solve_wit_11_r_eq_a_pure -> sub_mod_p_partial_solve_wit_11_r_eq_a_aux.

Definition sub_mod_p_partial_solve_wit_12_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_b < SM2_P_Z)) (PreH35 : (0 <= B_r_eq_b)) (PreH36 : (A_r_eq_b < SM2_P_Z)) (PreH37 : (0 <= A_r_eq_b)) (PreH38 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x3_2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x3_2 >= 0)) (PreH14 : (out >= 0)) (PreH15 : (out_2 >= 0)) (PreH16 : (out_3 >= 0)) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH32 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_b < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_b)) (PreH52 : (A_r_eq_b < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_b)) (PreH54 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x3_2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3_2)) (64)) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_12_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x3_2 >= 0)) (PreH14 : (out >= 0)) (PreH15 : (out_2 >= 0)) (PreH16 : (out_3 >= 0)) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH32 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_b < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_b)) (PreH52 : (A_r_eq_b < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_b)) (PreH54 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x3_2)) (64))) ”
.

Definition sub_mod_p_partial_solve_wit_12_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x3_2 >= 0)) (PreH14 : (out >= 0)) (PreH15 : (out_2 >= 0)) (PreH16 : (out_3 >= 0)) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH32 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_b < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_b)) (PreH52 : (A_r_eq_b < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_b)) (PreH54 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x3_2)) (64)) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_12_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_b < SM2_P_Z)) (PreH35 : (0 <= B_r_eq_b)) (PreH36 : (A_r_eq_b < SM2_P_Z)) (PreH37 : (0 <= A_r_eq_b)) (PreH38 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3_2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x3_2)) (64))) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_12_r_eq_b := sub_mod_p_partial_solve_wit_12_r_eq_b_pure -> sub_mod_p_partial_solve_wit_12_r_eq_b_aux.

Definition sub_mod_p_partial_solve_wit_13_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_non_alias < SM2_P_Z)) (PreH41 : (0 <= B_non_alias)) (PreH42 : (A_non_alias < SM2_P_Z)) (PreH43 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 0 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_14_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_non_alias < SM2_P_Z)) (PreH41 : (0 <= B_non_alias)) (PreH42 : (A_non_alias < SM2_P_Z)) (PreH43 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_2 >= 0)) (PreH23 : (out_3 >= 0)) (PreH24 : (out_4 >= 0)) (PreH25 : (retval_4 = 0)) (PreH26 : (0 <= out_4)) (PreH27 : (out_4 < U64_MOD)) (PreH28 : (0 <= retval_4)) (PreH29 : (retval_4 <= 1)) (PreH30 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH31 : (0 <= out_3)) (PreH32 : (out_3 < U64_MOD)) (PreH33 : (0 <= retval_3)) (PreH34 : (retval_3 <= 1)) (PreH35 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH36 : (0 <= out_2)) (PreH37 : (out_2 < U64_MOD)) (PreH38 : (0 <= retval_2)) (PreH39 : (retval_2 <= 1)) (PreH40 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH41 : (0 <= out)) (PreH42 : (out < U64_MOD)) (PreH43 : (0 <= retval)) (PreH44 : (retval <= 1)) (PreH45 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH46 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH47 : (x3_2 < U64_MOD)) (PreH48 : (0 <= x3_2)) (PreH49 : (x2_2 < U64_MOD)) (PreH50 : (0 <= x2_2)) (PreH51 : (x1_2 < U64_MOD)) (PreH52 : (0 <= x1_2)) (PreH53 : (x0_2 < U64_MOD)) (PreH54 : (0 <= x0_2)) (PreH55 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH56 : (x3 < U64_MOD)) (PreH57 : (0 <= x3)) (PreH58 : (x2 < U64_MOD)) (PreH59 : (0 <= x2)) (PreH60 : (x1 < U64_MOD)) (PreH61 : (0 <= x1)) (PreH62 : (x0 < U64_MOD)) (PreH63 : (0 <= x0)) (PreH64 : (B_non_alias < SM2_P_Z)) (PreH65 : (0 <= B_non_alias)) (PreH66 : (A_non_alias < SM2_P_Z)) (PreH67 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_14_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_2 >= 0)) (PreH23 : (out_3 >= 0)) (PreH24 : (out_4 >= 0)) (PreH25 : (retval_4 = 0)) (PreH26 : (0 <= out_4)) (PreH27 : (out_4 < U64_MOD)) (PreH28 : (0 <= retval_4)) (PreH29 : (retval_4 <= 1)) (PreH30 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH31 : (0 <= out_3)) (PreH32 : (out_3 < U64_MOD)) (PreH33 : (0 <= retval_3)) (PreH34 : (retval_3 <= 1)) (PreH35 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH36 : (0 <= out_2)) (PreH37 : (out_2 < U64_MOD)) (PreH38 : (0 <= retval_2)) (PreH39 : (retval_2 <= 1)) (PreH40 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH41 : (0 <= out)) (PreH42 : (out < U64_MOD)) (PreH43 : (0 <= retval)) (PreH44 : (retval <= 1)) (PreH45 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH46 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH47 : (x3_2 < U64_MOD)) (PreH48 : (0 <= x3_2)) (PreH49 : (x2_2 < U64_MOD)) (PreH50 : (0 <= x2_2)) (PreH51 : (x1_2 < U64_MOD)) (PreH52 : (0 <= x1_2)) (PreH53 : (x0_2 < U64_MOD)) (PreH54 : (0 <= x0_2)) (PreH55 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH56 : (x3 < U64_MOD)) (PreH57 : (0 <= x3)) (PreH58 : (x2 < U64_MOD)) (PreH59 : (0 <= x2)) (PreH60 : (x1 < U64_MOD)) (PreH61 : (0 <= x1)) (PreH62 : (x0 < U64_MOD)) (PreH63 : (0 <= x0)) (PreH64 : (B_non_alias < SM2_P_Z)) (PreH65 : (0 <= B_non_alias)) (PreH66 : (A_non_alias < SM2_P_Z)) (PreH67 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition sub_mod_p_partial_solve_wit_14_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_2 >= 0)) (PreH23 : (out_3 >= 0)) (PreH24 : (out_4 >= 0)) (PreH25 : (retval_4 = 0)) (PreH26 : (0 <= out_4)) (PreH27 : (out_4 < U64_MOD)) (PreH28 : (0 <= retval_4)) (PreH29 : (retval_4 <= 1)) (PreH30 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH31 : (0 <= out_3)) (PreH32 : (out_3 < U64_MOD)) (PreH33 : (0 <= retval_3)) (PreH34 : (retval_3 <= 1)) (PreH35 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH36 : (0 <= out_2)) (PreH37 : (out_2 < U64_MOD)) (PreH38 : (0 <= retval_2)) (PreH39 : (retval_2 <= 1)) (PreH40 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH41 : (0 <= out)) (PreH42 : (out < U64_MOD)) (PreH43 : (0 <= retval)) (PreH44 : (retval <= 1)) (PreH45 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH46 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH47 : (x3_2 < U64_MOD)) (PreH48 : (0 <= x3_2)) (PreH49 : (x2_2 < U64_MOD)) (PreH50 : (0 <= x2_2)) (PreH51 : (x1_2 < U64_MOD)) (PreH52 : (0 <= x1_2)) (PreH53 : (x0_2 < U64_MOD)) (PreH54 : (0 <= x0_2)) (PreH55 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH56 : (x3 < U64_MOD)) (PreH57 : (0 <= x3)) (PreH58 : (x2 < U64_MOD)) (PreH59 : (0 <= x2)) (PreH60 : (x1 < U64_MOD)) (PreH61 : (0 <= x1)) (PreH62 : (x0 < U64_MOD)) (PreH63 : (0 <= x0)) (PreH64 : (B_non_alias < SM2_P_Z)) (PreH65 : (0 <= B_non_alias)) (PreH66 : (A_non_alias < SM2_P_Z)) (PreH67 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_14_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_non_alias < SM2_P_Z)) (PreH41 : (0 <= B_non_alias)) (PreH42 : (A_non_alias < SM2_P_Z)) (PreH43 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_14_non_alias := sub_mod_p_partial_solve_wit_14_non_alias_pure -> sub_mod_p_partial_solve_wit_14_non_alias_aux.

Definition sub_mod_p_partial_solve_wit_15_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 0 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition sub_mod_p_partial_solve_wit_16_r_eq_a_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_2 <= UINT64_MAX)) (PreH7 : (out_3 <= UINT64_MAX)) (PreH8 : (out_4 <= UINT64_MAX)) (PreH9 : (x0_2 >= 0)) (PreH10 : (x1_2 >= 0)) (PreH11 : (x2_2 >= 0)) (PreH12 : (x3_2 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_2 >= 0)) (PreH15 : (out_3 >= 0)) (PreH16 : (out_4 >= 0)) (PreH17 : (retval_4 = 0)) (PreH18 : (0 <= out_4)) (PreH19 : (out_4 < U64_MOD)) (PreH20 : (0 <= retval_4)) (PreH21 : (retval_4 <= 1)) (PreH22 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval_3)) (PreH26 : (retval_3 <= 1)) (PreH27 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_2)) (PreH31 : (retval_2 <= 1)) (PreH32 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval)) (PreH36 : (retval <= 1)) (PreH37 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH38 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH39 : (x3_2 < U64_MOD)) (PreH40 : (0 <= x3_2)) (PreH41 : (x2_2 < U64_MOD)) (PreH42 : (0 <= x2_2)) (PreH43 : (x1_2 < U64_MOD)) (PreH44 : (0 <= x1_2)) (PreH45 : (x0_2 < U64_MOD)) (PreH46 : (0 <= x0_2)) (PreH47 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH48 : (x3 < U64_MOD)) (PreH49 : (0 <= x3)) (PreH50 : (x2 < U64_MOD)) (PreH51 : (0 <= x2)) (PreH52 : (x1 < U64_MOD)) (PreH53 : (0 <= x1)) (PreH54 : (x0 < U64_MOD)) (PreH55 : (0 <= x0)) (PreH56 : (B_r_eq_a < SM2_P_Z)) (PreH57 : (0 <= B_r_eq_a)) (PreH58 : (A_r_eq_a < SM2_P_Z)) (PreH59 : (0 <= A_r_eq_a)) (PreH60 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_16_r_eq_a_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_2 <= UINT64_MAX)) (PreH7 : (out_3 <= UINT64_MAX)) (PreH8 : (out_4 <= UINT64_MAX)) (PreH9 : (x0_2 >= 0)) (PreH10 : (x1_2 >= 0)) (PreH11 : (x2_2 >= 0)) (PreH12 : (x3_2 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_2 >= 0)) (PreH15 : (out_3 >= 0)) (PreH16 : (out_4 >= 0)) (PreH17 : (retval_4 = 0)) (PreH18 : (0 <= out_4)) (PreH19 : (out_4 < U64_MOD)) (PreH20 : (0 <= retval_4)) (PreH21 : (retval_4 <= 1)) (PreH22 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval_3)) (PreH26 : (retval_3 <= 1)) (PreH27 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_2)) (PreH31 : (retval_2 <= 1)) (PreH32 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval)) (PreH36 : (retval <= 1)) (PreH37 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH38 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH39 : (x3_2 < U64_MOD)) (PreH40 : (0 <= x3_2)) (PreH41 : (x2_2 < U64_MOD)) (PreH42 : (0 <= x2_2)) (PreH43 : (x1_2 < U64_MOD)) (PreH44 : (0 <= x1_2)) (PreH45 : (x0_2 < U64_MOD)) (PreH46 : (0 <= x0_2)) (PreH47 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH48 : (x3 < U64_MOD)) (PreH49 : (0 <= x3)) (PreH50 : (x2 < U64_MOD)) (PreH51 : (0 <= x2)) (PreH52 : (x1 < U64_MOD)) (PreH53 : (0 <= x1)) (PreH54 : (x0 < U64_MOD)) (PreH55 : (0 <= x0)) (PreH56 : (B_r_eq_a < SM2_P_Z)) (PreH57 : (0 <= B_r_eq_a)) (PreH58 : (A_r_eq_a < SM2_P_Z)) (PreH59 : (0 <= A_r_eq_a)) (PreH60 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition sub_mod_p_partial_solve_wit_16_r_eq_a_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_2 <= UINT64_MAX)) (PreH7 : (out_3 <= UINT64_MAX)) (PreH8 : (out_4 <= UINT64_MAX)) (PreH9 : (x0_2 >= 0)) (PreH10 : (x1_2 >= 0)) (PreH11 : (x2_2 >= 0)) (PreH12 : (x3_2 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_2 >= 0)) (PreH15 : (out_3 >= 0)) (PreH16 : (out_4 >= 0)) (PreH17 : (retval_4 = 0)) (PreH18 : (0 <= out_4)) (PreH19 : (out_4 < U64_MOD)) (PreH20 : (0 <= retval_4)) (PreH21 : (retval_4 <= 1)) (PreH22 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval_3)) (PreH26 : (retval_3 <= 1)) (PreH27 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_2)) (PreH31 : (retval_2 <= 1)) (PreH32 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval)) (PreH36 : (retval <= 1)) (PreH37 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH38 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH39 : (x3_2 < U64_MOD)) (PreH40 : (0 <= x3_2)) (PreH41 : (x2_2 < U64_MOD)) (PreH42 : (0 <= x2_2)) (PreH43 : (x1_2 < U64_MOD)) (PreH44 : (0 <= x1_2)) (PreH45 : (x0_2 < U64_MOD)) (PreH46 : (0 <= x0_2)) (PreH47 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH48 : (x3 < U64_MOD)) (PreH49 : (0 <= x3)) (PreH50 : (x2 < U64_MOD)) (PreH51 : (0 <= x2)) (PreH52 : (x1 < U64_MOD)) (PreH53 : (0 <= x1)) (PreH54 : (x0 < U64_MOD)) (PreH55 : (0 <= x0)) (PreH56 : (B_r_eq_a < SM2_P_Z)) (PreH57 : (0 <= B_r_eq_a)) (PreH58 : (A_r_eq_a < SM2_P_Z)) (PreH59 : (0 <= A_r_eq_a)) (PreH60 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_16_r_eq_a_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_a < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_a)) (PreH42 : (A_r_eq_a < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_a)) (PreH44 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition sub_mod_p_partial_solve_wit_16_r_eq_a := sub_mod_p_partial_solve_wit_16_r_eq_a_pure -> sub_mod_p_partial_solve_wit_16_r_eq_a_aux.

Definition sub_mod_p_partial_solve_wit_17_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 0 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_18_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_2 <= UINT64_MAX)) (PreH7 : (out_3 <= UINT64_MAX)) (PreH8 : (out_4 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_2 >= 0)) (PreH15 : (out_3 >= 0)) (PreH16 : (out_4 >= 0)) (PreH17 : (retval_4 = 0)) (PreH18 : (0 <= out_4)) (PreH19 : (out_4 < U64_MOD)) (PreH20 : (0 <= retval_4)) (PreH21 : (retval_4 <= 1)) (PreH22 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval_3)) (PreH26 : (retval_3 <= 1)) (PreH27 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_2)) (PreH31 : (retval_2 <= 1)) (PreH32 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval)) (PreH36 : (retval <= 1)) (PreH37 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH38 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH39 : (x3_2 < U64_MOD)) (PreH40 : (0 <= x3_2)) (PreH41 : (x2_2 < U64_MOD)) (PreH42 : (0 <= x2_2)) (PreH43 : (x1_2 < U64_MOD)) (PreH44 : (0 <= x1_2)) (PreH45 : (x0_2 < U64_MOD)) (PreH46 : (0 <= x0_2)) (PreH47 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH48 : (x3 < U64_MOD)) (PreH49 : (0 <= x3)) (PreH50 : (x2 < U64_MOD)) (PreH51 : (0 <= x2)) (PreH52 : (x1 < U64_MOD)) (PreH53 : (0 <= x1)) (PreH54 : (x0 < U64_MOD)) (PreH55 : (0 <= x0)) (PreH56 : (B_r_eq_b < SM2_P_Z)) (PreH57 : (0 <= B_r_eq_b)) (PreH58 : (A_r_eq_b < SM2_P_Z)) (PreH59 : (0 <= A_r_eq_b)) (PreH60 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_18_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_2 <= UINT64_MAX)) (PreH7 : (out_3 <= UINT64_MAX)) (PreH8 : (out_4 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_2 >= 0)) (PreH15 : (out_3 >= 0)) (PreH16 : (out_4 >= 0)) (PreH17 : (retval_4 = 0)) (PreH18 : (0 <= out_4)) (PreH19 : (out_4 < U64_MOD)) (PreH20 : (0 <= retval_4)) (PreH21 : (retval_4 <= 1)) (PreH22 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval_3)) (PreH26 : (retval_3 <= 1)) (PreH27 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_2)) (PreH31 : (retval_2 <= 1)) (PreH32 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval)) (PreH36 : (retval <= 1)) (PreH37 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH38 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH39 : (x3_2 < U64_MOD)) (PreH40 : (0 <= x3_2)) (PreH41 : (x2_2 < U64_MOD)) (PreH42 : (0 <= x2_2)) (PreH43 : (x1_2 < U64_MOD)) (PreH44 : (0 <= x1_2)) (PreH45 : (x0_2 < U64_MOD)) (PreH46 : (0 <= x0_2)) (PreH47 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH48 : (x3 < U64_MOD)) (PreH49 : (0 <= x3)) (PreH50 : (x2 < U64_MOD)) (PreH51 : (0 <= x2)) (PreH52 : (x1 < U64_MOD)) (PreH53 : (0 <= x1)) (PreH54 : (x0 < U64_MOD)) (PreH55 : (0 <= x0)) (PreH56 : (B_r_eq_b < SM2_P_Z)) (PreH57 : (0 <= B_r_eq_b)) (PreH58 : (A_r_eq_b < SM2_P_Z)) (PreH59 : (0 <= A_r_eq_b)) (PreH60 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition sub_mod_p_partial_solve_wit_18_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_2 <= UINT64_MAX)) (PreH7 : (out_3 <= UINT64_MAX)) (PreH8 : (out_4 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_2 >= 0)) (PreH15 : (out_3 >= 0)) (PreH16 : (out_4 >= 0)) (PreH17 : (retval_4 = 0)) (PreH18 : (0 <= out_4)) (PreH19 : (out_4 < U64_MOD)) (PreH20 : (0 <= retval_4)) (PreH21 : (retval_4 <= 1)) (PreH22 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval_3)) (PreH26 : (retval_3 <= 1)) (PreH27 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_2)) (PreH31 : (retval_2 <= 1)) (PreH32 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval)) (PreH36 : (retval <= 1)) (PreH37 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH38 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH39 : (x3_2 < U64_MOD)) (PreH40 : (0 <= x3_2)) (PreH41 : (x2_2 < U64_MOD)) (PreH42 : (0 <= x2_2)) (PreH43 : (x1_2 < U64_MOD)) (PreH44 : (0 <= x1_2)) (PreH45 : (x0_2 < U64_MOD)) (PreH46 : (0 <= x0_2)) (PreH47 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH48 : (x3 < U64_MOD)) (PreH49 : (0 <= x3)) (PreH50 : (x2 < U64_MOD)) (PreH51 : (0 <= x2)) (PreH52 : (x1 < U64_MOD)) (PreH53 : (0 <= x1)) (PreH54 : (x0 < U64_MOD)) (PreH55 : (0 <= x0)) (PreH56 : (B_r_eq_b < SM2_P_Z)) (PreH57 : (0 <= B_r_eq_b)) (PreH58 : (A_r_eq_b < SM2_P_Z)) (PreH59 : (0 <= A_r_eq_b)) (PreH60 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_18_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (B_r_eq_b < SM2_P_Z)) (PreH41 : (0 <= B_r_eq_b)) (PreH42 : (A_r_eq_b < SM2_P_Z)) (PreH43 : (0 <= A_r_eq_b)) (PreH44 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_18_r_eq_b := sub_mod_p_partial_solve_wit_18_r_eq_b_pure -> sub_mod_p_partial_solve_wit_18_r_eq_b_aux.

Definition sub_mod_p_partial_solve_wit_19_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_4)) (PreH10 : (retval_4 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval_2)) (PreH20 : (retval_2 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH27 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_non_alias < SM2_P_Z)) (PreH46 : (0 <= B_non_alias)) (PreH47 : (A_non_alias < SM2_P_Z)) (PreH48 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 1 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_20_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH6 : (retval_5 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_5)) (PreH10 : (retval_5 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_non_alias < SM2_P_Z)) (PreH46 : (0 <= B_non_alias)) (PreH47 : (A_non_alias < SM2_P_Z)) (PreH48 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_3 <= UINT64_MAX)) (PreH11 : (out_4 <= UINT64_MAX)) (PreH12 : (out_5 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (out_4 >= 0)) (PreH24 : (out_5 >= 0)) (PreH25 : (0 <= out_5)) (PreH26 : (out_5 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH30 : (retval_5 = 0)) (PreH31 : (0 <= out_4)) (PreH32 : (out_4 < U64_MOD)) (PreH33 : (0 <= retval_5)) (PreH34 : (retval_5 <= 1)) (PreH35 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH36 : (0 <= out_3)) (PreH37 : (out_3 < U64_MOD)) (PreH38 : (0 <= retval_4)) (PreH39 : (retval_4 <= 1)) (PreH40 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH41 : (0 <= out)) (PreH42 : (out < U64_MOD)) (PreH43 : (0 <= retval_3)) (PreH44 : (retval_3 <= 1)) (PreH45 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH46 : (0 <= out_2)) (PreH47 : (out_2 < U64_MOD)) (PreH48 : (0 <= retval_2)) (PreH49 : (retval_2 <= 1)) (PreH50 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH51 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH52 : (x3_2 < U64_MOD)) (PreH53 : (0 <= x3_2)) (PreH54 : (x2_2 < U64_MOD)) (PreH55 : (0 <= x2_2)) (PreH56 : (x1_2 < U64_MOD)) (PreH57 : (0 <= x1_2)) (PreH58 : (x0_2 < U64_MOD)) (PreH59 : (0 <= x0_2)) (PreH60 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH61 : (x3 < U64_MOD)) (PreH62 : (0 <= x3)) (PreH63 : (x2 < U64_MOD)) (PreH64 : (0 <= x2)) (PreH65 : (x1 < U64_MOD)) (PreH66 : (0 <= x1)) (PreH67 : (x0 < U64_MOD)) (PreH68 : (0 <= x0)) (PreH69 : (B_non_alias < SM2_P_Z)) (PreH70 : (0 <= B_non_alias)) (PreH71 : (A_non_alias < SM2_P_Z)) (PreH72 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_20_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_3 <= UINT64_MAX)) (PreH11 : (out_4 <= UINT64_MAX)) (PreH12 : (out_5 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (out_4 >= 0)) (PreH24 : (out_5 >= 0)) (PreH25 : (0 <= out_5)) (PreH26 : (out_5 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH30 : (retval_5 = 0)) (PreH31 : (0 <= out_4)) (PreH32 : (out_4 < U64_MOD)) (PreH33 : (0 <= retval_5)) (PreH34 : (retval_5 <= 1)) (PreH35 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH36 : (0 <= out_3)) (PreH37 : (out_3 < U64_MOD)) (PreH38 : (0 <= retval_4)) (PreH39 : (retval_4 <= 1)) (PreH40 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH41 : (0 <= out)) (PreH42 : (out < U64_MOD)) (PreH43 : (0 <= retval_3)) (PreH44 : (retval_3 <= 1)) (PreH45 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH46 : (0 <= out_2)) (PreH47 : (out_2 < U64_MOD)) (PreH48 : (0 <= retval_2)) (PreH49 : (retval_2 <= 1)) (PreH50 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH51 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH52 : (x3_2 < U64_MOD)) (PreH53 : (0 <= x3_2)) (PreH54 : (x2_2 < U64_MOD)) (PreH55 : (0 <= x2_2)) (PreH56 : (x1_2 < U64_MOD)) (PreH57 : (0 <= x1_2)) (PreH58 : (x0_2 < U64_MOD)) (PreH59 : (0 <= x0_2)) (PreH60 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH61 : (x3 < U64_MOD)) (PreH62 : (0 <= x3)) (PreH63 : (x2 < U64_MOD)) (PreH64 : (0 <= x2)) (PreH65 : (x1 < U64_MOD)) (PreH66 : (0 <= x1)) (PreH67 : (x0 < U64_MOD)) (PreH68 : (0 <= x0)) (PreH69 : (B_non_alias < SM2_P_Z)) (PreH70 : (0 <= B_non_alias)) (PreH71 : (A_non_alias < SM2_P_Z)) (PreH72 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition sub_mod_p_partial_solve_wit_20_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_3 <= UINT64_MAX)) (PreH11 : (out_4 <= UINT64_MAX)) (PreH12 : (out_5 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (out_4 >= 0)) (PreH24 : (out_5 >= 0)) (PreH25 : (0 <= out_5)) (PreH26 : (out_5 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH30 : (retval_5 = 0)) (PreH31 : (0 <= out_4)) (PreH32 : (out_4 < U64_MOD)) (PreH33 : (0 <= retval_5)) (PreH34 : (retval_5 <= 1)) (PreH35 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH36 : (0 <= out_3)) (PreH37 : (out_3 < U64_MOD)) (PreH38 : (0 <= retval_4)) (PreH39 : (retval_4 <= 1)) (PreH40 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH41 : (0 <= out)) (PreH42 : (out < U64_MOD)) (PreH43 : (0 <= retval_3)) (PreH44 : (retval_3 <= 1)) (PreH45 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH46 : (0 <= out_2)) (PreH47 : (out_2 < U64_MOD)) (PreH48 : (0 <= retval_2)) (PreH49 : (retval_2 <= 1)) (PreH50 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH51 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH52 : (x3_2 < U64_MOD)) (PreH53 : (0 <= x3_2)) (PreH54 : (x2_2 < U64_MOD)) (PreH55 : (0 <= x2_2)) (PreH56 : (x1_2 < U64_MOD)) (PreH57 : (0 <= x1_2)) (PreH58 : (x0_2 < U64_MOD)) (PreH59 : (0 <= x0_2)) (PreH60 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH61 : (x3 < U64_MOD)) (PreH62 : (0 <= x3)) (PreH63 : (x2 < U64_MOD)) (PreH64 : (0 <= x2)) (PreH65 : (x1 < U64_MOD)) (PreH66 : (0 <= x1)) (PreH67 : (x0 < U64_MOD)) (PreH68 : (0 <= x0)) (PreH69 : (B_non_alias < SM2_P_Z)) (PreH70 : (0 <= B_non_alias)) (PreH71 : (A_non_alias < SM2_P_Z)) (PreH72 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_20_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH6 : (retval_5 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_5)) (PreH10 : (retval_5 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_non_alias < SM2_P_Z)) (PreH46 : (0 <= B_non_alias)) (PreH47 : (A_non_alias < SM2_P_Z)) (PreH48 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) )) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_20_non_alias := sub_mod_p_partial_solve_wit_20_non_alias_pure -> sub_mod_p_partial_solve_wit_20_non_alias_aux.

Definition sub_mod_p_partial_solve_wit_21_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_4)) (PreH10 : (retval_4 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval_2)) (PreH20 : (retval_2 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH27 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_a < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_a)) (PreH47 : (A_r_eq_a < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_a)) (PreH49 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 1 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition sub_mod_p_partial_solve_wit_22_r_eq_a_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH6 : (retval_5 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_5)) (PreH10 : (retval_5 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_a < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_a)) (PreH47 : (A_r_eq_a < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_a)) (PreH49 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_3 <= UINT64_MAX)) (PreH7 : (out_4 <= UINT64_MAX)) (PreH8 : (out_5 <= UINT64_MAX)) (PreH9 : (x0_2 >= 0)) (PreH10 : (x1_2 >= 0)) (PreH11 : (x2_2 >= 0)) (PreH12 : (x3_2 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_3 >= 0)) (PreH15 : (out_4 >= 0)) (PreH16 : (out_5 >= 0)) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH22 : (retval_5 = 0)) (PreH23 : (0 <= out_4)) (PreH24 : (out_4 < U64_MOD)) (PreH25 : (0 <= retval_5)) (PreH26 : (retval_5 <= 1)) (PreH27 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH28 : (0 <= out_3)) (PreH29 : (out_3 < U64_MOD)) (PreH30 : (0 <= retval_4)) (PreH31 : (retval_4 <= 1)) (PreH32 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_3)) (PreH36 : (retval_3 <= 1)) (PreH37 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH38 : (0 <= out_2)) (PreH39 : (out_2 < U64_MOD)) (PreH40 : (0 <= retval_2)) (PreH41 : (retval_2 <= 1)) (PreH42 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH43 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH44 : (x3_2 < U64_MOD)) (PreH45 : (0 <= x3_2)) (PreH46 : (x2_2 < U64_MOD)) (PreH47 : (0 <= x2_2)) (PreH48 : (x1_2 < U64_MOD)) (PreH49 : (0 <= x1_2)) (PreH50 : (x0_2 < U64_MOD)) (PreH51 : (0 <= x0_2)) (PreH52 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH53 : (x3 < U64_MOD)) (PreH54 : (0 <= x3)) (PreH55 : (x2 < U64_MOD)) (PreH56 : (0 <= x2)) (PreH57 : (x1 < U64_MOD)) (PreH58 : (0 <= x1)) (PreH59 : (x0 < U64_MOD)) (PreH60 : (0 <= x0)) (PreH61 : (B_r_eq_a < SM2_P_Z)) (PreH62 : (0 <= B_r_eq_a)) (PreH63 : (A_r_eq_a < SM2_P_Z)) (PreH64 : (0 <= A_r_eq_a)) (PreH65 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_22_r_eq_a_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_3 <= UINT64_MAX)) (PreH7 : (out_4 <= UINT64_MAX)) (PreH8 : (out_5 <= UINT64_MAX)) (PreH9 : (x0_2 >= 0)) (PreH10 : (x1_2 >= 0)) (PreH11 : (x2_2 >= 0)) (PreH12 : (x3_2 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_3 >= 0)) (PreH15 : (out_4 >= 0)) (PreH16 : (out_5 >= 0)) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH22 : (retval_5 = 0)) (PreH23 : (0 <= out_4)) (PreH24 : (out_4 < U64_MOD)) (PreH25 : (0 <= retval_5)) (PreH26 : (retval_5 <= 1)) (PreH27 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH28 : (0 <= out_3)) (PreH29 : (out_3 < U64_MOD)) (PreH30 : (0 <= retval_4)) (PreH31 : (retval_4 <= 1)) (PreH32 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_3)) (PreH36 : (retval_3 <= 1)) (PreH37 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH38 : (0 <= out_2)) (PreH39 : (out_2 < U64_MOD)) (PreH40 : (0 <= retval_2)) (PreH41 : (retval_2 <= 1)) (PreH42 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH43 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH44 : (x3_2 < U64_MOD)) (PreH45 : (0 <= x3_2)) (PreH46 : (x2_2 < U64_MOD)) (PreH47 : (0 <= x2_2)) (PreH48 : (x1_2 < U64_MOD)) (PreH49 : (0 <= x1_2)) (PreH50 : (x0_2 < U64_MOD)) (PreH51 : (0 <= x0_2)) (PreH52 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH53 : (x3 < U64_MOD)) (PreH54 : (0 <= x3)) (PreH55 : (x2 < U64_MOD)) (PreH56 : (0 <= x2)) (PreH57 : (x1 < U64_MOD)) (PreH58 : (0 <= x1)) (PreH59 : (x0 < U64_MOD)) (PreH60 : (0 <= x0)) (PreH61 : (B_r_eq_a < SM2_P_Z)) (PreH62 : (0 <= B_r_eq_a)) (PreH63 : (A_r_eq_a < SM2_P_Z)) (PreH64 : (0 <= A_r_eq_a)) (PreH65 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition sub_mod_p_partial_solve_wit_22_r_eq_a_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_3 <= UINT64_MAX)) (PreH7 : (out_4 <= UINT64_MAX)) (PreH8 : (out_5 <= UINT64_MAX)) (PreH9 : (x0_2 >= 0)) (PreH10 : (x1_2 >= 0)) (PreH11 : (x2_2 >= 0)) (PreH12 : (x3_2 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_3 >= 0)) (PreH15 : (out_4 >= 0)) (PreH16 : (out_5 >= 0)) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH22 : (retval_5 = 0)) (PreH23 : (0 <= out_4)) (PreH24 : (out_4 < U64_MOD)) (PreH25 : (0 <= retval_5)) (PreH26 : (retval_5 <= 1)) (PreH27 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH28 : (0 <= out_3)) (PreH29 : (out_3 < U64_MOD)) (PreH30 : (0 <= retval_4)) (PreH31 : (retval_4 <= 1)) (PreH32 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_3)) (PreH36 : (retval_3 <= 1)) (PreH37 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH38 : (0 <= out_2)) (PreH39 : (out_2 < U64_MOD)) (PreH40 : (0 <= retval_2)) (PreH41 : (retval_2 <= 1)) (PreH42 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH43 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH44 : (x3_2 < U64_MOD)) (PreH45 : (0 <= x3_2)) (PreH46 : (x2_2 < U64_MOD)) (PreH47 : (0 <= x2_2)) (PreH48 : (x1_2 < U64_MOD)) (PreH49 : (0 <= x1_2)) (PreH50 : (x0_2 < U64_MOD)) (PreH51 : (0 <= x0_2)) (PreH52 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH53 : (x3 < U64_MOD)) (PreH54 : (0 <= x3)) (PreH55 : (x2 < U64_MOD)) (PreH56 : (0 <= x2)) (PreH57 : (x1 < U64_MOD)) (PreH58 : (0 <= x1)) (PreH59 : (x0 < U64_MOD)) (PreH60 : (0 <= x0)) (PreH61 : (B_r_eq_a < SM2_P_Z)) (PreH62 : (0 <= B_r_eq_a)) (PreH63 : (A_r_eq_a < SM2_P_Z)) (PreH64 : (0 <= A_r_eq_a)) (PreH65 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_22_r_eq_a_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH6 : (retval_5 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_5)) (PreH10 : (retval_5 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_a < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_a)) (PreH47 : (A_r_eq_a < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_a)) (PreH49 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) )) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition sub_mod_p_partial_solve_wit_22_r_eq_a := sub_mod_p_partial_solve_wit_22_r_eq_a_pure -> sub_mod_p_partial_solve_wit_22_r_eq_a_aux.

Definition sub_mod_p_partial_solve_wit_23_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_4)) (PreH10 : (retval_4 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval_2)) (PreH20 : (retval_2 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH27 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_b < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_b)) (PreH47 : (A_r_eq_b < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_b)) (PreH49 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 1 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_24_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH6 : (retval_5 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_5)) (PreH10 : (retval_5 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_b < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_b)) (PreH47 : (A_r_eq_b < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_b)) (PreH49 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_3 <= UINT64_MAX)) (PreH7 : (out_4 <= UINT64_MAX)) (PreH8 : (out_5 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_3 >= 0)) (PreH15 : (out_4 >= 0)) (PreH16 : (out_5 >= 0)) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH22 : (retval_5 = 0)) (PreH23 : (0 <= out_4)) (PreH24 : (out_4 < U64_MOD)) (PreH25 : (0 <= retval_5)) (PreH26 : (retval_5 <= 1)) (PreH27 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH28 : (0 <= out_3)) (PreH29 : (out_3 < U64_MOD)) (PreH30 : (0 <= retval_4)) (PreH31 : (retval_4 <= 1)) (PreH32 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_3)) (PreH36 : (retval_3 <= 1)) (PreH37 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH38 : (0 <= out_2)) (PreH39 : (out_2 < U64_MOD)) (PreH40 : (0 <= retval_2)) (PreH41 : (retval_2 <= 1)) (PreH42 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH43 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH44 : (x3_2 < U64_MOD)) (PreH45 : (0 <= x3_2)) (PreH46 : (x2_2 < U64_MOD)) (PreH47 : (0 <= x2_2)) (PreH48 : (x1_2 < U64_MOD)) (PreH49 : (0 <= x1_2)) (PreH50 : (x0_2 < U64_MOD)) (PreH51 : (0 <= x0_2)) (PreH52 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH53 : (x3 < U64_MOD)) (PreH54 : (0 <= x3)) (PreH55 : (x2 < U64_MOD)) (PreH56 : (0 <= x2)) (PreH57 : (x1 < U64_MOD)) (PreH58 : (0 <= x1)) (PreH59 : (x0 < U64_MOD)) (PreH60 : (0 <= x0)) (PreH61 : (B_r_eq_b < SM2_P_Z)) (PreH62 : (0 <= B_r_eq_b)) (PreH63 : (A_r_eq_b < SM2_P_Z)) (PreH64 : (0 <= A_r_eq_b)) (PreH65 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_24_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_3 <= UINT64_MAX)) (PreH7 : (out_4 <= UINT64_MAX)) (PreH8 : (out_5 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_3 >= 0)) (PreH15 : (out_4 >= 0)) (PreH16 : (out_5 >= 0)) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH22 : (retval_5 = 0)) (PreH23 : (0 <= out_4)) (PreH24 : (out_4 < U64_MOD)) (PreH25 : (0 <= retval_5)) (PreH26 : (retval_5 <= 1)) (PreH27 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH28 : (0 <= out_3)) (PreH29 : (out_3 < U64_MOD)) (PreH30 : (0 <= retval_4)) (PreH31 : (retval_4 <= 1)) (PreH32 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_3)) (PreH36 : (retval_3 <= 1)) (PreH37 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH38 : (0 <= out_2)) (PreH39 : (out_2 < U64_MOD)) (PreH40 : (0 <= retval_2)) (PreH41 : (retval_2 <= 1)) (PreH42 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH43 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH44 : (x3_2 < U64_MOD)) (PreH45 : (0 <= x3_2)) (PreH46 : (x2_2 < U64_MOD)) (PreH47 : (0 <= x2_2)) (PreH48 : (x1_2 < U64_MOD)) (PreH49 : (0 <= x1_2)) (PreH50 : (x0_2 < U64_MOD)) (PreH51 : (0 <= x0_2)) (PreH52 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH53 : (x3 < U64_MOD)) (PreH54 : (0 <= x3)) (PreH55 : (x2 < U64_MOD)) (PreH56 : (0 <= x2)) (PreH57 : (x1 < U64_MOD)) (PreH58 : (0 <= x1)) (PreH59 : (x0 < U64_MOD)) (PreH60 : (0 <= x0)) (PreH61 : (B_r_eq_b < SM2_P_Z)) (PreH62 : (0 <= B_r_eq_b)) (PreH63 : (A_r_eq_b < SM2_P_Z)) (PreH64 : (0 <= A_r_eq_b)) (PreH65 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition sub_mod_p_partial_solve_wit_24_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_3 <= UINT64_MAX)) (PreH7 : (out_4 <= UINT64_MAX)) (PreH8 : (out_5 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_3 >= 0)) (PreH15 : (out_4 >= 0)) (PreH16 : (out_5 >= 0)) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH22 : (retval_5 = 0)) (PreH23 : (0 <= out_4)) (PreH24 : (out_4 < U64_MOD)) (PreH25 : (0 <= retval_5)) (PreH26 : (retval_5 <= 1)) (PreH27 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH28 : (0 <= out_3)) (PreH29 : (out_3 < U64_MOD)) (PreH30 : (0 <= retval_4)) (PreH31 : (retval_4 <= 1)) (PreH32 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_3)) (PreH36 : (retval_3 <= 1)) (PreH37 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH38 : (0 <= out_2)) (PreH39 : (out_2 < U64_MOD)) (PreH40 : (0 <= retval_2)) (PreH41 : (retval_2 <= 1)) (PreH42 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH43 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH44 : (x3_2 < U64_MOD)) (PreH45 : (0 <= x3_2)) (PreH46 : (x2_2 < U64_MOD)) (PreH47 : (0 <= x2_2)) (PreH48 : (x1_2 < U64_MOD)) (PreH49 : (0 <= x1_2)) (PreH50 : (x0_2 < U64_MOD)) (PreH51 : (0 <= x0_2)) (PreH52 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH53 : (x3 < U64_MOD)) (PreH54 : (0 <= x3)) (PreH55 : (x2 < U64_MOD)) (PreH56 : (0 <= x2)) (PreH57 : (x1 < U64_MOD)) (PreH58 : (0 <= x1)) (PreH59 : (x0 < U64_MOD)) (PreH60 : (0 <= x0)) (PreH61 : (B_r_eq_b < SM2_P_Z)) (PreH62 : (0 <= B_r_eq_b)) (PreH63 : (A_r_eq_b < SM2_P_Z)) (PreH64 : (0 <= A_r_eq_b)) (PreH65 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_24_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) ))) (PreH6 : (retval_5 = 0)) (PreH7 : (0 <= out_4)) (PreH8 : (out_4 < U64_MOD)) (PreH9 : (0 <= retval_5)) (PreH10 : (retval_5 <= 1)) (PreH11 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH12 : (0 <= out_3)) (PreH13 : (out_3 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (B_r_eq_b < SM2_P_Z)) (PreH46 : (0 <= B_r_eq_b)) (PreH47 : (A_r_eq_b < SM2_P_Z)) (PreH48 : (0 <= A_r_eq_b)) (PreH49 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval * U64_MOD ) )) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_24_r_eq_b := sub_mod_p_partial_solve_wit_24_r_eq_b_pure -> sub_mod_p_partial_solve_wit_24_r_eq_b_aux.

Definition sub_mod_p_partial_solve_wit_25_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (retval_4 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH32 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_non_alias < SM2_P_Z)) (PreH51 : (0 <= B_non_alias)) (PreH52 : (A_non_alias < SM2_P_Z)) (PreH53 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 2 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_26_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH11 : (retval_5 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_5)) (PreH15 : (retval_5 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_non_alias < SM2_P_Z)) (PreH51 : (0 <= B_non_alias)) (PreH52 : (A_non_alias < SM2_P_Z)) (PreH53 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_4 <= UINT64_MAX)) (PreH11 : (out_5 <= UINT64_MAX)) (PreH12 : (out_6 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_4 >= 0)) (PreH23 : (out_5 >= 0)) (PreH24 : (out_6 >= 0)) (PreH25 : (0 <= out_6)) (PreH26 : (out_6 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_5)) (PreH31 : (out_5 < U64_MOD)) (PreH32 : (0 <= retval_6)) (PreH33 : (retval_6 <= 1)) (PreH34 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH35 : (retval_5 = 0)) (PreH36 : (0 <= out_4)) (PreH37 : (out_4 < U64_MOD)) (PreH38 : (0 <= retval_5)) (PreH39 : (retval_5 <= 1)) (PreH40 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH41 : (0 <= out)) (PreH42 : (out < U64_MOD)) (PreH43 : (0 <= retval_4)) (PreH44 : (retval_4 <= 1)) (PreH45 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH46 : (0 <= out_3)) (PreH47 : (out_3 < U64_MOD)) (PreH48 : (0 <= retval_3)) (PreH49 : (retval_3 <= 1)) (PreH50 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH51 : (0 <= out_2)) (PreH52 : (out_2 < U64_MOD)) (PreH53 : (0 <= retval_2)) (PreH54 : (retval_2 <= 1)) (PreH55 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH56 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH57 : (x3_2 < U64_MOD)) (PreH58 : (0 <= x3_2)) (PreH59 : (x2_2 < U64_MOD)) (PreH60 : (0 <= x2_2)) (PreH61 : (x1_2 < U64_MOD)) (PreH62 : (0 <= x1_2)) (PreH63 : (x0_2 < U64_MOD)) (PreH64 : (0 <= x0_2)) (PreH65 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH66 : (x3 < U64_MOD)) (PreH67 : (0 <= x3)) (PreH68 : (x2 < U64_MOD)) (PreH69 : (0 <= x2)) (PreH70 : (x1 < U64_MOD)) (PreH71 : (0 <= x1)) (PreH72 : (x0 < U64_MOD)) (PreH73 : (0 <= x0)) (PreH74 : (B_non_alias < SM2_P_Z)) (PreH75 : (0 <= B_non_alias)) (PreH76 : (A_non_alias < SM2_P_Z)) (PreH77 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_26_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_4 <= UINT64_MAX)) (PreH11 : (out_5 <= UINT64_MAX)) (PreH12 : (out_6 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_4 >= 0)) (PreH23 : (out_5 >= 0)) (PreH24 : (out_6 >= 0)) (PreH25 : (0 <= out_6)) (PreH26 : (out_6 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_5)) (PreH31 : (out_5 < U64_MOD)) (PreH32 : (0 <= retval_6)) (PreH33 : (retval_6 <= 1)) (PreH34 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH35 : (retval_5 = 0)) (PreH36 : (0 <= out_4)) (PreH37 : (out_4 < U64_MOD)) (PreH38 : (0 <= retval_5)) (PreH39 : (retval_5 <= 1)) (PreH40 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH41 : (0 <= out)) (PreH42 : (out < U64_MOD)) (PreH43 : (0 <= retval_4)) (PreH44 : (retval_4 <= 1)) (PreH45 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH46 : (0 <= out_3)) (PreH47 : (out_3 < U64_MOD)) (PreH48 : (0 <= retval_3)) (PreH49 : (retval_3 <= 1)) (PreH50 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH51 : (0 <= out_2)) (PreH52 : (out_2 < U64_MOD)) (PreH53 : (0 <= retval_2)) (PreH54 : (retval_2 <= 1)) (PreH55 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH56 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH57 : (x3_2 < U64_MOD)) (PreH58 : (0 <= x3_2)) (PreH59 : (x2_2 < U64_MOD)) (PreH60 : (0 <= x2_2)) (PreH61 : (x1_2 < U64_MOD)) (PreH62 : (0 <= x1_2)) (PreH63 : (x0_2 < U64_MOD)) (PreH64 : (0 <= x0_2)) (PreH65 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH66 : (x3 < U64_MOD)) (PreH67 : (0 <= x3)) (PreH68 : (x2 < U64_MOD)) (PreH69 : (0 <= x2)) (PreH70 : (x1 < U64_MOD)) (PreH71 : (0 <= x1)) (PreH72 : (x0 < U64_MOD)) (PreH73 : (0 <= x0)) (PreH74 : (B_non_alias < SM2_P_Z)) (PreH75 : (0 <= B_non_alias)) (PreH76 : (A_non_alias < SM2_P_Z)) (PreH77 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition sub_mod_p_partial_solve_wit_26_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_4 <= UINT64_MAX)) (PreH11 : (out_5 <= UINT64_MAX)) (PreH12 : (out_6 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_4 >= 0)) (PreH23 : (out_5 >= 0)) (PreH24 : (out_6 >= 0)) (PreH25 : (0 <= out_6)) (PreH26 : (out_6 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_5)) (PreH31 : (out_5 < U64_MOD)) (PreH32 : (0 <= retval_6)) (PreH33 : (retval_6 <= 1)) (PreH34 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH35 : (retval_5 = 0)) (PreH36 : (0 <= out_4)) (PreH37 : (out_4 < U64_MOD)) (PreH38 : (0 <= retval_5)) (PreH39 : (retval_5 <= 1)) (PreH40 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH41 : (0 <= out)) (PreH42 : (out < U64_MOD)) (PreH43 : (0 <= retval_4)) (PreH44 : (retval_4 <= 1)) (PreH45 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH46 : (0 <= out_3)) (PreH47 : (out_3 < U64_MOD)) (PreH48 : (0 <= retval_3)) (PreH49 : (retval_3 <= 1)) (PreH50 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH51 : (0 <= out_2)) (PreH52 : (out_2 < U64_MOD)) (PreH53 : (0 <= retval_2)) (PreH54 : (retval_2 <= 1)) (PreH55 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH56 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH57 : (x3_2 < U64_MOD)) (PreH58 : (0 <= x3_2)) (PreH59 : (x2_2 < U64_MOD)) (PreH60 : (0 <= x2_2)) (PreH61 : (x1_2 < U64_MOD)) (PreH62 : (0 <= x1_2)) (PreH63 : (x0_2 < U64_MOD)) (PreH64 : (0 <= x0_2)) (PreH65 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH66 : (x3 < U64_MOD)) (PreH67 : (0 <= x3)) (PreH68 : (x2 < U64_MOD)) (PreH69 : (0 <= x2)) (PreH70 : (x1 < U64_MOD)) (PreH71 : (0 <= x1)) (PreH72 : (x0 < U64_MOD)) (PreH73 : (0 <= x0)) (PreH74 : (B_non_alias < SM2_P_Z)) (PreH75 : (0 <= B_non_alias)) (PreH76 : (A_non_alias < SM2_P_Z)) (PreH77 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_26_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH11 : (retval_5 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_5)) (PreH15 : (retval_5 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_non_alias < SM2_P_Z)) (PreH51 : (0 <= B_non_alias)) (PreH52 : (A_non_alias < SM2_P_Z)) (PreH53 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_26_non_alias := sub_mod_p_partial_solve_wit_26_non_alias_pure -> sub_mod_p_partial_solve_wit_26_non_alias_aux.

Definition sub_mod_p_partial_solve_wit_27_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (retval_4 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH32 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_a < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_a)) (PreH52 : (A_r_eq_a < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_a)) (PreH54 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 2 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition sub_mod_p_partial_solve_wit_28_r_eq_a_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH11 : (retval_5 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_5)) (PreH15 : (retval_5 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_a < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_a)) (PreH52 : (A_r_eq_a < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_a)) (PreH54 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_4 <= UINT64_MAX)) (PreH7 : (out_5 <= UINT64_MAX)) (PreH8 : (out_6 <= UINT64_MAX)) (PreH9 : (x0_2 >= 0)) (PreH10 : (x1_2 >= 0)) (PreH11 : (x2_2 >= 0)) (PreH12 : (x3_2 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_4 >= 0)) (PreH15 : (out_5 >= 0)) (PreH16 : (out_6 >= 0)) (PreH17 : (0 <= out_6)) (PreH18 : (out_6 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_5)) (PreH23 : (out_5 < U64_MOD)) (PreH24 : (0 <= retval_6)) (PreH25 : (retval_6 <= 1)) (PreH26 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH27 : (retval_5 = 0)) (PreH28 : (0 <= out_4)) (PreH29 : (out_4 < U64_MOD)) (PreH30 : (0 <= retval_5)) (PreH31 : (retval_5 <= 1)) (PreH32 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_4)) (PreH36 : (retval_4 <= 1)) (PreH37 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH38 : (0 <= out_3)) (PreH39 : (out_3 < U64_MOD)) (PreH40 : (0 <= retval_3)) (PreH41 : (retval_3 <= 1)) (PreH42 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH43 : (0 <= out_2)) (PreH44 : (out_2 < U64_MOD)) (PreH45 : (0 <= retval_2)) (PreH46 : (retval_2 <= 1)) (PreH47 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH48 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH49 : (x3_2 < U64_MOD)) (PreH50 : (0 <= x3_2)) (PreH51 : (x2_2 < U64_MOD)) (PreH52 : (0 <= x2_2)) (PreH53 : (x1_2 < U64_MOD)) (PreH54 : (0 <= x1_2)) (PreH55 : (x0_2 < U64_MOD)) (PreH56 : (0 <= x0_2)) (PreH57 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH58 : (x3 < U64_MOD)) (PreH59 : (0 <= x3)) (PreH60 : (x2 < U64_MOD)) (PreH61 : (0 <= x2)) (PreH62 : (x1 < U64_MOD)) (PreH63 : (0 <= x1)) (PreH64 : (x0 < U64_MOD)) (PreH65 : (0 <= x0)) (PreH66 : (B_r_eq_a < SM2_P_Z)) (PreH67 : (0 <= B_r_eq_a)) (PreH68 : (A_r_eq_a < SM2_P_Z)) (PreH69 : (0 <= A_r_eq_a)) (PreH70 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_28_r_eq_a_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_4 <= UINT64_MAX)) (PreH7 : (out_5 <= UINT64_MAX)) (PreH8 : (out_6 <= UINT64_MAX)) (PreH9 : (x0_2 >= 0)) (PreH10 : (x1_2 >= 0)) (PreH11 : (x2_2 >= 0)) (PreH12 : (x3_2 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_4 >= 0)) (PreH15 : (out_5 >= 0)) (PreH16 : (out_6 >= 0)) (PreH17 : (0 <= out_6)) (PreH18 : (out_6 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_5)) (PreH23 : (out_5 < U64_MOD)) (PreH24 : (0 <= retval_6)) (PreH25 : (retval_6 <= 1)) (PreH26 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH27 : (retval_5 = 0)) (PreH28 : (0 <= out_4)) (PreH29 : (out_4 < U64_MOD)) (PreH30 : (0 <= retval_5)) (PreH31 : (retval_5 <= 1)) (PreH32 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_4)) (PreH36 : (retval_4 <= 1)) (PreH37 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH38 : (0 <= out_3)) (PreH39 : (out_3 < U64_MOD)) (PreH40 : (0 <= retval_3)) (PreH41 : (retval_3 <= 1)) (PreH42 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH43 : (0 <= out_2)) (PreH44 : (out_2 < U64_MOD)) (PreH45 : (0 <= retval_2)) (PreH46 : (retval_2 <= 1)) (PreH47 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH48 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH49 : (x3_2 < U64_MOD)) (PreH50 : (0 <= x3_2)) (PreH51 : (x2_2 < U64_MOD)) (PreH52 : (0 <= x2_2)) (PreH53 : (x1_2 < U64_MOD)) (PreH54 : (0 <= x1_2)) (PreH55 : (x0_2 < U64_MOD)) (PreH56 : (0 <= x0_2)) (PreH57 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH58 : (x3 < U64_MOD)) (PreH59 : (0 <= x3)) (PreH60 : (x2 < U64_MOD)) (PreH61 : (0 <= x2)) (PreH62 : (x1 < U64_MOD)) (PreH63 : (0 <= x1)) (PreH64 : (x0 < U64_MOD)) (PreH65 : (0 <= x0)) (PreH66 : (B_r_eq_a < SM2_P_Z)) (PreH67 : (0 <= B_r_eq_a)) (PreH68 : (A_r_eq_a < SM2_P_Z)) (PreH69 : (0 <= A_r_eq_a)) (PreH70 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition sub_mod_p_partial_solve_wit_28_r_eq_a_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_4 <= UINT64_MAX)) (PreH7 : (out_5 <= UINT64_MAX)) (PreH8 : (out_6 <= UINT64_MAX)) (PreH9 : (x0_2 >= 0)) (PreH10 : (x1_2 >= 0)) (PreH11 : (x2_2 >= 0)) (PreH12 : (x3_2 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_4 >= 0)) (PreH15 : (out_5 >= 0)) (PreH16 : (out_6 >= 0)) (PreH17 : (0 <= out_6)) (PreH18 : (out_6 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_5)) (PreH23 : (out_5 < U64_MOD)) (PreH24 : (0 <= retval_6)) (PreH25 : (retval_6 <= 1)) (PreH26 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH27 : (retval_5 = 0)) (PreH28 : (0 <= out_4)) (PreH29 : (out_4 < U64_MOD)) (PreH30 : (0 <= retval_5)) (PreH31 : (retval_5 <= 1)) (PreH32 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_4)) (PreH36 : (retval_4 <= 1)) (PreH37 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH38 : (0 <= out_3)) (PreH39 : (out_3 < U64_MOD)) (PreH40 : (0 <= retval_3)) (PreH41 : (retval_3 <= 1)) (PreH42 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH43 : (0 <= out_2)) (PreH44 : (out_2 < U64_MOD)) (PreH45 : (0 <= retval_2)) (PreH46 : (retval_2 <= 1)) (PreH47 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH48 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH49 : (x3_2 < U64_MOD)) (PreH50 : (0 <= x3_2)) (PreH51 : (x2_2 < U64_MOD)) (PreH52 : (0 <= x2_2)) (PreH53 : (x1_2 < U64_MOD)) (PreH54 : (0 <= x1_2)) (PreH55 : (x0_2 < U64_MOD)) (PreH56 : (0 <= x0_2)) (PreH57 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH58 : (x3 < U64_MOD)) (PreH59 : (0 <= x3)) (PreH60 : (x2 < U64_MOD)) (PreH61 : (0 <= x2)) (PreH62 : (x1 < U64_MOD)) (PreH63 : (0 <= x1)) (PreH64 : (x0 < U64_MOD)) (PreH65 : (0 <= x0)) (PreH66 : (B_r_eq_a < SM2_P_Z)) (PreH67 : (0 <= B_r_eq_a)) (PreH68 : (A_r_eq_a < SM2_P_Z)) (PreH69 : (0 <= A_r_eq_a)) (PreH70 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_28_r_eq_a_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH11 : (retval_5 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_5)) (PreH15 : (retval_5 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_a < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_a)) (PreH52 : (A_r_eq_a < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_a)) (PreH54 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition sub_mod_p_partial_solve_wit_28_r_eq_a := sub_mod_p_partial_solve_wit_28_r_eq_a_pure -> sub_mod_p_partial_solve_wit_28_r_eq_a_aux.

Definition sub_mod_p_partial_solve_wit_29_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (retval_4 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_4)) (PreH15 : (retval_4 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval_3)) (PreH20 : (retval_3 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH32 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_b < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_b)) (PreH52 : (A_r_eq_b < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_b)) (PreH54 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 2 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_30_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH11 : (retval_5 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_5)) (PreH15 : (retval_5 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_b < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_b)) (PreH52 : (A_r_eq_b < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_b)) (PreH54 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_4 <= UINT64_MAX)) (PreH7 : (out_5 <= UINT64_MAX)) (PreH8 : (out_6 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_4 >= 0)) (PreH15 : (out_5 >= 0)) (PreH16 : (out_6 >= 0)) (PreH17 : (0 <= out_6)) (PreH18 : (out_6 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_5)) (PreH23 : (out_5 < U64_MOD)) (PreH24 : (0 <= retval_6)) (PreH25 : (retval_6 <= 1)) (PreH26 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH27 : (retval_5 = 0)) (PreH28 : (0 <= out_4)) (PreH29 : (out_4 < U64_MOD)) (PreH30 : (0 <= retval_5)) (PreH31 : (retval_5 <= 1)) (PreH32 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_4)) (PreH36 : (retval_4 <= 1)) (PreH37 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH38 : (0 <= out_3)) (PreH39 : (out_3 < U64_MOD)) (PreH40 : (0 <= retval_3)) (PreH41 : (retval_3 <= 1)) (PreH42 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH43 : (0 <= out_2)) (PreH44 : (out_2 < U64_MOD)) (PreH45 : (0 <= retval_2)) (PreH46 : (retval_2 <= 1)) (PreH47 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH48 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH49 : (x3_2 < U64_MOD)) (PreH50 : (0 <= x3_2)) (PreH51 : (x2_2 < U64_MOD)) (PreH52 : (0 <= x2_2)) (PreH53 : (x1_2 < U64_MOD)) (PreH54 : (0 <= x1_2)) (PreH55 : (x0_2 < U64_MOD)) (PreH56 : (0 <= x0_2)) (PreH57 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH58 : (x3 < U64_MOD)) (PreH59 : (0 <= x3)) (PreH60 : (x2 < U64_MOD)) (PreH61 : (0 <= x2)) (PreH62 : (x1 < U64_MOD)) (PreH63 : (0 <= x1)) (PreH64 : (x0 < U64_MOD)) (PreH65 : (0 <= x0)) (PreH66 : (B_r_eq_b < SM2_P_Z)) (PreH67 : (0 <= B_r_eq_b)) (PreH68 : (A_r_eq_b < SM2_P_Z)) (PreH69 : (0 <= A_r_eq_b)) (PreH70 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_30_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_4 <= UINT64_MAX)) (PreH7 : (out_5 <= UINT64_MAX)) (PreH8 : (out_6 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_4 >= 0)) (PreH15 : (out_5 >= 0)) (PreH16 : (out_6 >= 0)) (PreH17 : (0 <= out_6)) (PreH18 : (out_6 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_5)) (PreH23 : (out_5 < U64_MOD)) (PreH24 : (0 <= retval_6)) (PreH25 : (retval_6 <= 1)) (PreH26 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH27 : (retval_5 = 0)) (PreH28 : (0 <= out_4)) (PreH29 : (out_4 < U64_MOD)) (PreH30 : (0 <= retval_5)) (PreH31 : (retval_5 <= 1)) (PreH32 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_4)) (PreH36 : (retval_4 <= 1)) (PreH37 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH38 : (0 <= out_3)) (PreH39 : (out_3 < U64_MOD)) (PreH40 : (0 <= retval_3)) (PreH41 : (retval_3 <= 1)) (PreH42 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH43 : (0 <= out_2)) (PreH44 : (out_2 < U64_MOD)) (PreH45 : (0 <= retval_2)) (PreH46 : (retval_2 <= 1)) (PreH47 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH48 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH49 : (x3_2 < U64_MOD)) (PreH50 : (0 <= x3_2)) (PreH51 : (x2_2 < U64_MOD)) (PreH52 : (0 <= x2_2)) (PreH53 : (x1_2 < U64_MOD)) (PreH54 : (0 <= x1_2)) (PreH55 : (x0_2 < U64_MOD)) (PreH56 : (0 <= x0_2)) (PreH57 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH58 : (x3 < U64_MOD)) (PreH59 : (0 <= x3)) (PreH60 : (x2 < U64_MOD)) (PreH61 : (0 <= x2)) (PreH62 : (x1 < U64_MOD)) (PreH63 : (0 <= x1)) (PreH64 : (x0 < U64_MOD)) (PreH65 : (0 <= x0)) (PreH66 : (B_r_eq_b < SM2_P_Z)) (PreH67 : (0 <= B_r_eq_b)) (PreH68 : (A_r_eq_b < SM2_P_Z)) (PreH69 : (0 <= A_r_eq_b)) (PreH70 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition sub_mod_p_partial_solve_wit_30_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_4 <= UINT64_MAX)) (PreH7 : (out_5 <= UINT64_MAX)) (PreH8 : (out_6 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_4 >= 0)) (PreH15 : (out_5 >= 0)) (PreH16 : (out_6 >= 0)) (PreH17 : (0 <= out_6)) (PreH18 : (out_6 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_5)) (PreH23 : (out_5 < U64_MOD)) (PreH24 : (0 <= retval_6)) (PreH25 : (retval_6 <= 1)) (PreH26 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH27 : (retval_5 = 0)) (PreH28 : (0 <= out_4)) (PreH29 : (out_4 < U64_MOD)) (PreH30 : (0 <= retval_5)) (PreH31 : (retval_5 <= 1)) (PreH32 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_4)) (PreH36 : (retval_4 <= 1)) (PreH37 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH38 : (0 <= out_3)) (PreH39 : (out_3 < U64_MOD)) (PreH40 : (0 <= retval_3)) (PreH41 : (retval_3 <= 1)) (PreH42 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH43 : (0 <= out_2)) (PreH44 : (out_2 < U64_MOD)) (PreH45 : (0 <= retval_2)) (PreH46 : (retval_2 <= 1)) (PreH47 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH48 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH49 : (x3_2 < U64_MOD)) (PreH50 : (0 <= x3_2)) (PreH51 : (x2_2 < U64_MOD)) (PreH52 : (0 <= x2_2)) (PreH53 : (x1_2 < U64_MOD)) (PreH54 : (0 <= x1_2)) (PreH55 : (x0_2 < U64_MOD)) (PreH56 : (0 <= x0_2)) (PreH57 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH58 : (x3 < U64_MOD)) (PreH59 : (0 <= x3)) (PreH60 : (x2 < U64_MOD)) (PreH61 : (0 <= x2)) (PreH62 : (x1 < U64_MOD)) (PreH63 : (0 <= x1)) (PreH64 : (x0 < U64_MOD)) (PreH65 : (0 <= x0)) (PreH66 : (B_r_eq_b < SM2_P_Z)) (PreH67 : (0 <= B_r_eq_b)) (PreH68 : (A_r_eq_b < SM2_P_Z)) (PreH69 : (0 <= A_r_eq_b)) (PreH70 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_30_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH11 : (retval_5 = 0)) (PreH12 : (0 <= out_4)) (PreH13 : (out_4 < U64_MOD)) (PreH14 : (0 <= retval_5)) (PreH15 : (retval_5 <= 1)) (PreH16 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (B_r_eq_b < SM2_P_Z)) (PreH51 : (0 <= B_r_eq_b)) (PreH52 : (A_r_eq_b < SM2_P_Z)) (PreH53 : (0 <= A_r_eq_b)) (PreH54 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_30_r_eq_b := sub_mod_p_partial_solve_wit_30_r_eq_b_pure -> sub_mod_p_partial_solve_wit_30_r_eq_b_aux.

Definition sub_mod_p_partial_solve_wit_31_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= out_4)) (PreH18 : (out_4 < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (0 <= out)) (PreH33 : (out < U64_MOD)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH37 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_non_alias < SM2_P_Z)) (PreH56 : (0 <= B_non_alias)) (PreH57 : (A_non_alias < SM2_P_Z)) (PreH58 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_7) ” 
  &&  “ (out_7 < U64_MOD) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) )) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 3 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_32_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH16 : (retval_5 = 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_non_alias < SM2_P_Z)) (PreH56 : (0 <= B_non_alias)) (PreH57 : (A_non_alias < SM2_P_Z)) (PreH58 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_5 <= UINT64_MAX)) (PreH11 : (out_6 <= UINT64_MAX)) (PreH12 : (out_7 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_5 >= 0)) (PreH23 : (out_6 >= 0)) (PreH24 : (out_7 >= 0)) (PreH25 : (0 <= out_7)) (PreH26 : (out_7 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_6)) (PreH31 : (out_6 < U64_MOD)) (PreH32 : (0 <= retval_7)) (PreH33 : (retval_7 <= 1)) (PreH34 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH35 : (0 <= out_5)) (PreH36 : (out_5 < U64_MOD)) (PreH37 : (0 <= retval_6)) (PreH38 : (retval_6 <= 1)) (PreH39 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH40 : (retval_5 = 0)) (PreH41 : (0 <= out)) (PreH42 : (out < U64_MOD)) (PreH43 : (0 <= retval_5)) (PreH44 : (retval_5 <= 1)) (PreH45 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH46 : (0 <= out_4)) (PreH47 : (out_4 < U64_MOD)) (PreH48 : (0 <= retval_4)) (PreH49 : (retval_4 <= 1)) (PreH50 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH51 : (0 <= out_3)) (PreH52 : (out_3 < U64_MOD)) (PreH53 : (0 <= retval_3)) (PreH54 : (retval_3 <= 1)) (PreH55 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH56 : (0 <= out_2)) (PreH57 : (out_2 < U64_MOD)) (PreH58 : (0 <= retval_2)) (PreH59 : (retval_2 <= 1)) (PreH60 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH61 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH62 : (x3_2 < U64_MOD)) (PreH63 : (0 <= x3_2)) (PreH64 : (x2_2 < U64_MOD)) (PreH65 : (0 <= x2_2)) (PreH66 : (x1_2 < U64_MOD)) (PreH67 : (0 <= x1_2)) (PreH68 : (x0_2 < U64_MOD)) (PreH69 : (0 <= x0_2)) (PreH70 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH71 : (x3 < U64_MOD)) (PreH72 : (0 <= x3)) (PreH73 : (x2 < U64_MOD)) (PreH74 : (0 <= x2)) (PreH75 : (x1 < U64_MOD)) (PreH76 : (0 <= x1)) (PreH77 : (x0 < U64_MOD)) (PreH78 : (0 <= x0)) (PreH79 : (B_non_alias < SM2_P_Z)) (PreH80 : (0 <= B_non_alias)) (PreH81 : (A_non_alias < SM2_P_Z)) (PreH82 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_32_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_5 <= UINT64_MAX)) (PreH11 : (out_6 <= UINT64_MAX)) (PreH12 : (out_7 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_5 >= 0)) (PreH23 : (out_6 >= 0)) (PreH24 : (out_7 >= 0)) (PreH25 : (0 <= out_7)) (PreH26 : (out_7 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_6)) (PreH31 : (out_6 < U64_MOD)) (PreH32 : (0 <= retval_7)) (PreH33 : (retval_7 <= 1)) (PreH34 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH35 : (0 <= out_5)) (PreH36 : (out_5 < U64_MOD)) (PreH37 : (0 <= retval_6)) (PreH38 : (retval_6 <= 1)) (PreH39 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH40 : (retval_5 = 0)) (PreH41 : (0 <= out)) (PreH42 : (out < U64_MOD)) (PreH43 : (0 <= retval_5)) (PreH44 : (retval_5 <= 1)) (PreH45 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH46 : (0 <= out_4)) (PreH47 : (out_4 < U64_MOD)) (PreH48 : (0 <= retval_4)) (PreH49 : (retval_4 <= 1)) (PreH50 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH51 : (0 <= out_3)) (PreH52 : (out_3 < U64_MOD)) (PreH53 : (0 <= retval_3)) (PreH54 : (retval_3 <= 1)) (PreH55 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH56 : (0 <= out_2)) (PreH57 : (out_2 < U64_MOD)) (PreH58 : (0 <= retval_2)) (PreH59 : (retval_2 <= 1)) (PreH60 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH61 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH62 : (x3_2 < U64_MOD)) (PreH63 : (0 <= x3_2)) (PreH64 : (x2_2 < U64_MOD)) (PreH65 : (0 <= x2_2)) (PreH66 : (x1_2 < U64_MOD)) (PreH67 : (0 <= x1_2)) (PreH68 : (x0_2 < U64_MOD)) (PreH69 : (0 <= x0_2)) (PreH70 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH71 : (x3 < U64_MOD)) (PreH72 : (0 <= x3)) (PreH73 : (x2 < U64_MOD)) (PreH74 : (0 <= x2)) (PreH75 : (x1 < U64_MOD)) (PreH76 : (0 <= x1)) (PreH77 : (x0 < U64_MOD)) (PreH78 : (0 <= x0)) (PreH79 : (B_non_alias < SM2_P_Z)) (PreH80 : (0 <= B_non_alias)) (PreH81 : (A_non_alias < SM2_P_Z)) (PreH82 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition sub_mod_p_partial_solve_wit_32_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_5 <= UINT64_MAX)) (PreH11 : (out_6 <= UINT64_MAX)) (PreH12 : (out_7 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_5 >= 0)) (PreH23 : (out_6 >= 0)) (PreH24 : (out_7 >= 0)) (PreH25 : (0 <= out_7)) (PreH26 : (out_7 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_6)) (PreH31 : (out_6 < U64_MOD)) (PreH32 : (0 <= retval_7)) (PreH33 : (retval_7 <= 1)) (PreH34 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH35 : (0 <= out_5)) (PreH36 : (out_5 < U64_MOD)) (PreH37 : (0 <= retval_6)) (PreH38 : (retval_6 <= 1)) (PreH39 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH40 : (retval_5 = 0)) (PreH41 : (0 <= out)) (PreH42 : (out < U64_MOD)) (PreH43 : (0 <= retval_5)) (PreH44 : (retval_5 <= 1)) (PreH45 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH46 : (0 <= out_4)) (PreH47 : (out_4 < U64_MOD)) (PreH48 : (0 <= retval_4)) (PreH49 : (retval_4 <= 1)) (PreH50 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH51 : (0 <= out_3)) (PreH52 : (out_3 < U64_MOD)) (PreH53 : (0 <= retval_3)) (PreH54 : (retval_3 <= 1)) (PreH55 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH56 : (0 <= out_2)) (PreH57 : (out_2 < U64_MOD)) (PreH58 : (0 <= retval_2)) (PreH59 : (retval_2 <= 1)) (PreH60 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH61 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH62 : (x3_2 < U64_MOD)) (PreH63 : (0 <= x3_2)) (PreH64 : (x2_2 < U64_MOD)) (PreH65 : (0 <= x2_2)) (PreH66 : (x1_2 < U64_MOD)) (PreH67 : (0 <= x1_2)) (PreH68 : (x0_2 < U64_MOD)) (PreH69 : (0 <= x0_2)) (PreH70 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH71 : (x3 < U64_MOD)) (PreH72 : (0 <= x3)) (PreH73 : (x2 < U64_MOD)) (PreH74 : (0 <= x2)) (PreH75 : (x1 < U64_MOD)) (PreH76 : (0 <= x1)) (PreH77 : (x0 < U64_MOD)) (PreH78 : (0 <= x0)) (PreH79 : (B_non_alias < SM2_P_Z)) (PreH80 : (0 <= B_non_alias)) (PreH81 : (A_non_alias < SM2_P_Z)) (PreH82 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_32_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH16 : (retval_5 = 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_non_alias < SM2_P_Z)) (PreH56 : (0 <= B_non_alias)) (PreH57 : (A_non_alias < SM2_P_Z)) (PreH58 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ (0 <= out_7) ” 
  &&  “ (out_7 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
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
  &&  “ (B_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_32_non_alias := sub_mod_p_partial_solve_wit_32_non_alias_pure -> sub_mod_p_partial_solve_wit_32_non_alias_aux.

Definition sub_mod_p_partial_solve_wit_33_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= out_4)) (PreH18 : (out_4 < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (0 <= out)) (PreH33 : (out < U64_MOD)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH37 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_r_eq_a < SM2_P_Z)) (PreH56 : (0 <= B_r_eq_a)) (PreH57 : (A_r_eq_a < SM2_P_Z)) (PreH58 : (0 <= A_r_eq_a)) (PreH59 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (0 <= out_7) ” 
  &&  “ (out_7 < U64_MOD) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) )) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 3 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition sub_mod_p_partial_solve_wit_34_r_eq_a_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH16 : (retval_5 = 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_r_eq_a < SM2_P_Z)) (PreH56 : (0 <= B_r_eq_a)) (PreH57 : (A_r_eq_a < SM2_P_Z)) (PreH58 : (0 <= A_r_eq_a)) (PreH59 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_5 <= UINT64_MAX)) (PreH7 : (out_6 <= UINT64_MAX)) (PreH8 : (out_7 <= UINT64_MAX)) (PreH9 : (x0_2 >= 0)) (PreH10 : (x1_2 >= 0)) (PreH11 : (x2_2 >= 0)) (PreH12 : (x3_2 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_5 >= 0)) (PreH15 : (out_6 >= 0)) (PreH16 : (out_7 >= 0)) (PreH17 : (0 <= out_7)) (PreH18 : (out_7 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_6)) (PreH23 : (out_6 < U64_MOD)) (PreH24 : (0 <= retval_7)) (PreH25 : (retval_7 <= 1)) (PreH26 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH27 : (0 <= out_5)) (PreH28 : (out_5 < U64_MOD)) (PreH29 : (0 <= retval_6)) (PreH30 : (retval_6 <= 1)) (PreH31 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH32 : (retval_5 = 0)) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_5)) (PreH36 : (retval_5 <= 1)) (PreH37 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH38 : (0 <= out_4)) (PreH39 : (out_4 < U64_MOD)) (PreH40 : (0 <= retval_4)) (PreH41 : (retval_4 <= 1)) (PreH42 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH43 : (0 <= out_3)) (PreH44 : (out_3 < U64_MOD)) (PreH45 : (0 <= retval_3)) (PreH46 : (retval_3 <= 1)) (PreH47 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH48 : (0 <= out_2)) (PreH49 : (out_2 < U64_MOD)) (PreH50 : (0 <= retval_2)) (PreH51 : (retval_2 <= 1)) (PreH52 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH53 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH54 : (x3_2 < U64_MOD)) (PreH55 : (0 <= x3_2)) (PreH56 : (x2_2 < U64_MOD)) (PreH57 : (0 <= x2_2)) (PreH58 : (x1_2 < U64_MOD)) (PreH59 : (0 <= x1_2)) (PreH60 : (x0_2 < U64_MOD)) (PreH61 : (0 <= x0_2)) (PreH62 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH63 : (x3 < U64_MOD)) (PreH64 : (0 <= x3)) (PreH65 : (x2 < U64_MOD)) (PreH66 : (0 <= x2)) (PreH67 : (x1 < U64_MOD)) (PreH68 : (0 <= x1)) (PreH69 : (x0 < U64_MOD)) (PreH70 : (0 <= x0)) (PreH71 : (B_r_eq_a < SM2_P_Z)) (PreH72 : (0 <= B_r_eq_a)) (PreH73 : (A_r_eq_a < SM2_P_Z)) (PreH74 : (0 <= A_r_eq_a)) (PreH75 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_34_r_eq_a_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_5 <= UINT64_MAX)) (PreH7 : (out_6 <= UINT64_MAX)) (PreH8 : (out_7 <= UINT64_MAX)) (PreH9 : (x0_2 >= 0)) (PreH10 : (x1_2 >= 0)) (PreH11 : (x2_2 >= 0)) (PreH12 : (x3_2 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_5 >= 0)) (PreH15 : (out_6 >= 0)) (PreH16 : (out_7 >= 0)) (PreH17 : (0 <= out_7)) (PreH18 : (out_7 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_6)) (PreH23 : (out_6 < U64_MOD)) (PreH24 : (0 <= retval_7)) (PreH25 : (retval_7 <= 1)) (PreH26 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH27 : (0 <= out_5)) (PreH28 : (out_5 < U64_MOD)) (PreH29 : (0 <= retval_6)) (PreH30 : (retval_6 <= 1)) (PreH31 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH32 : (retval_5 = 0)) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_5)) (PreH36 : (retval_5 <= 1)) (PreH37 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH38 : (0 <= out_4)) (PreH39 : (out_4 < U64_MOD)) (PreH40 : (0 <= retval_4)) (PreH41 : (retval_4 <= 1)) (PreH42 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH43 : (0 <= out_3)) (PreH44 : (out_3 < U64_MOD)) (PreH45 : (0 <= retval_3)) (PreH46 : (retval_3 <= 1)) (PreH47 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH48 : (0 <= out_2)) (PreH49 : (out_2 < U64_MOD)) (PreH50 : (0 <= retval_2)) (PreH51 : (retval_2 <= 1)) (PreH52 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH53 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH54 : (x3_2 < U64_MOD)) (PreH55 : (0 <= x3_2)) (PreH56 : (x2_2 < U64_MOD)) (PreH57 : (0 <= x2_2)) (PreH58 : (x1_2 < U64_MOD)) (PreH59 : (0 <= x1_2)) (PreH60 : (x0_2 < U64_MOD)) (PreH61 : (0 <= x0_2)) (PreH62 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH63 : (x3 < U64_MOD)) (PreH64 : (0 <= x3)) (PreH65 : (x2 < U64_MOD)) (PreH66 : (0 <= x2)) (PreH67 : (x1 < U64_MOD)) (PreH68 : (0 <= x1)) (PreH69 : (x0 < U64_MOD)) (PreH70 : (0 <= x0)) (PreH71 : (B_r_eq_a < SM2_P_Z)) (PreH72 : (0 <= B_r_eq_a)) (PreH73 : (A_r_eq_a < SM2_P_Z)) (PreH74 : (0 <= A_r_eq_a)) (PreH75 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition sub_mod_p_partial_solve_wit_34_r_eq_a_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0_2 <= UINT64_MAX)) (PreH2 : (x1_2 <= UINT64_MAX)) (PreH3 : (x2_2 <= UINT64_MAX)) (PreH4 : (x3_2 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_5 <= UINT64_MAX)) (PreH7 : (out_6 <= UINT64_MAX)) (PreH8 : (out_7 <= UINT64_MAX)) (PreH9 : (x0_2 >= 0)) (PreH10 : (x1_2 >= 0)) (PreH11 : (x2_2 >= 0)) (PreH12 : (x3_2 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_5 >= 0)) (PreH15 : (out_6 >= 0)) (PreH16 : (out_7 >= 0)) (PreH17 : (0 <= out_7)) (PreH18 : (out_7 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_6)) (PreH23 : (out_6 < U64_MOD)) (PreH24 : (0 <= retval_7)) (PreH25 : (retval_7 <= 1)) (PreH26 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH27 : (0 <= out_5)) (PreH28 : (out_5 < U64_MOD)) (PreH29 : (0 <= retval_6)) (PreH30 : (retval_6 <= 1)) (PreH31 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH32 : (retval_5 = 0)) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_5)) (PreH36 : (retval_5 <= 1)) (PreH37 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH38 : (0 <= out_4)) (PreH39 : (out_4 < U64_MOD)) (PreH40 : (0 <= retval_4)) (PreH41 : (retval_4 <= 1)) (PreH42 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH43 : (0 <= out_3)) (PreH44 : (out_3 < U64_MOD)) (PreH45 : (0 <= retval_3)) (PreH46 : (retval_3 <= 1)) (PreH47 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH48 : (0 <= out_2)) (PreH49 : (out_2 < U64_MOD)) (PreH50 : (0 <= retval_2)) (PreH51 : (retval_2 <= 1)) (PreH52 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH53 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH54 : (x3_2 < U64_MOD)) (PreH55 : (0 <= x3_2)) (PreH56 : (x2_2 < U64_MOD)) (PreH57 : (0 <= x2_2)) (PreH58 : (x1_2 < U64_MOD)) (PreH59 : (0 <= x1_2)) (PreH60 : (x0_2 < U64_MOD)) (PreH61 : (0 <= x0_2)) (PreH62 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH63 : (x3 < U64_MOD)) (PreH64 : (0 <= x3)) (PreH65 : (x2 < U64_MOD)) (PreH66 : (0 <= x2)) (PreH67 : (x1 < U64_MOD)) (PreH68 : (0 <= x1)) (PreH69 : (x0 < U64_MOD)) (PreH70 : (0 <= x0)) (PreH71 : (B_r_eq_a < SM2_P_Z)) (PreH72 : (0 <= B_r_eq_a)) (PreH73 : (A_r_eq_a < SM2_P_Z)) (PreH74 : (0 <= A_r_eq_a)) (PreH75 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_34_r_eq_a_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH16 : (retval_5 = 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_r_eq_a < SM2_P_Z)) (PreH56 : (0 <= B_r_eq_a)) (PreH57 : (A_r_eq_a < SM2_P_Z)) (PreH58 : (0 <= A_r_eq_a)) (PreH59 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ (0 <= out_7) ” 
  &&  “ (out_7 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_a) ” 
  &&  “ (A_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_a) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition sub_mod_p_partial_solve_wit_34_r_eq_a := sub_mod_p_partial_solve_wit_34_r_eq_a_pure -> sub_mod_p_partial_solve_wit_34_r_eq_a_aux.

Definition sub_mod_p_partial_solve_wit_35_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= out_4)) (PreH18 : (out_4 < U64_MOD)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH22 : (0 <= out_3)) (PreH23 : (out_3 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out_2)) (PreH28 : (out_2 < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH32 : (0 <= out)) (PreH33 : (out < U64_MOD)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH37 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_r_eq_b < SM2_P_Z)) (PreH56 : (0 <= B_r_eq_b)) (PreH57 : (A_r_eq_b < SM2_P_Z)) (PreH58 : (0 <= A_r_eq_b)) (PreH59 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_7) ” 
  &&  “ (out_7 < U64_MOD) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (((out_3 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) )) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 3 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_36_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH16 : (retval_5 = 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_r_eq_b < SM2_P_Z)) (PreH56 : (0 <= B_r_eq_b)) (PreH57 : (A_r_eq_b < SM2_P_Z)) (PreH58 : (0 <= A_r_eq_b)) (PreH59 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_5 <= UINT64_MAX)) (PreH7 : (out_6 <= UINT64_MAX)) (PreH8 : (out_7 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_5 >= 0)) (PreH15 : (out_6 >= 0)) (PreH16 : (out_7 >= 0)) (PreH17 : (0 <= out_7)) (PreH18 : (out_7 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_6)) (PreH23 : (out_6 < U64_MOD)) (PreH24 : (0 <= retval_7)) (PreH25 : (retval_7 <= 1)) (PreH26 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH27 : (0 <= out_5)) (PreH28 : (out_5 < U64_MOD)) (PreH29 : (0 <= retval_6)) (PreH30 : (retval_6 <= 1)) (PreH31 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH32 : (retval_5 = 0)) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_5)) (PreH36 : (retval_5 <= 1)) (PreH37 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH38 : (0 <= out_4)) (PreH39 : (out_4 < U64_MOD)) (PreH40 : (0 <= retval_4)) (PreH41 : (retval_4 <= 1)) (PreH42 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH43 : (0 <= out_3)) (PreH44 : (out_3 < U64_MOD)) (PreH45 : (0 <= retval_3)) (PreH46 : (retval_3 <= 1)) (PreH47 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH48 : (0 <= out_2)) (PreH49 : (out_2 < U64_MOD)) (PreH50 : (0 <= retval_2)) (PreH51 : (retval_2 <= 1)) (PreH52 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH53 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH54 : (x3_2 < U64_MOD)) (PreH55 : (0 <= x3_2)) (PreH56 : (x2_2 < U64_MOD)) (PreH57 : (0 <= x2_2)) (PreH58 : (x1_2 < U64_MOD)) (PreH59 : (0 <= x1_2)) (PreH60 : (x0_2 < U64_MOD)) (PreH61 : (0 <= x0_2)) (PreH62 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH63 : (x3 < U64_MOD)) (PreH64 : (0 <= x3)) (PreH65 : (x2 < U64_MOD)) (PreH66 : (0 <= x2)) (PreH67 : (x1 < U64_MOD)) (PreH68 : (0 <= x1)) (PreH69 : (x0 < U64_MOD)) (PreH70 : (0 <= x0)) (PreH71 : (B_r_eq_b < SM2_P_Z)) (PreH72 : (0 <= B_r_eq_b)) (PreH73 : (A_r_eq_b < SM2_P_Z)) (PreH74 : (0 <= A_r_eq_b)) (PreH75 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition sub_mod_p_partial_solve_wit_36_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_5 <= UINT64_MAX)) (PreH7 : (out_6 <= UINT64_MAX)) (PreH8 : (out_7 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_5 >= 0)) (PreH15 : (out_6 >= 0)) (PreH16 : (out_7 >= 0)) (PreH17 : (0 <= out_7)) (PreH18 : (out_7 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_6)) (PreH23 : (out_6 < U64_MOD)) (PreH24 : (0 <= retval_7)) (PreH25 : (retval_7 <= 1)) (PreH26 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH27 : (0 <= out_5)) (PreH28 : (out_5 < U64_MOD)) (PreH29 : (0 <= retval_6)) (PreH30 : (retval_6 <= 1)) (PreH31 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH32 : (retval_5 = 0)) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_5)) (PreH36 : (retval_5 <= 1)) (PreH37 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH38 : (0 <= out_4)) (PreH39 : (out_4 < U64_MOD)) (PreH40 : (0 <= retval_4)) (PreH41 : (retval_4 <= 1)) (PreH42 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH43 : (0 <= out_3)) (PreH44 : (out_3 < U64_MOD)) (PreH45 : (0 <= retval_3)) (PreH46 : (retval_3 <= 1)) (PreH47 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH48 : (0 <= out_2)) (PreH49 : (out_2 < U64_MOD)) (PreH50 : (0 <= retval_2)) (PreH51 : (retval_2 <= 1)) (PreH52 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH53 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH54 : (x3_2 < U64_MOD)) (PreH55 : (0 <= x3_2)) (PreH56 : (x2_2 < U64_MOD)) (PreH57 : (0 <= x2_2)) (PreH58 : (x1_2 < U64_MOD)) (PreH59 : (0 <= x1_2)) (PreH60 : (x0_2 < U64_MOD)) (PreH61 : (0 <= x0_2)) (PreH62 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH63 : (x3 < U64_MOD)) (PreH64 : (0 <= x3)) (PreH65 : (x2 < U64_MOD)) (PreH66 : (0 <= x2)) (PreH67 : (x1 < U64_MOD)) (PreH68 : (0 <= x1)) (PreH69 : (x0 < U64_MOD)) (PreH70 : (0 <= x0)) (PreH71 : (B_r_eq_b < SM2_P_Z)) (PreH72 : (0 <= B_r_eq_b)) (PreH73 : (A_r_eq_b < SM2_P_Z)) (PreH74 : (0 <= A_r_eq_b)) (PreH75 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition sub_mod_p_partial_solve_wit_36_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (out <= UINT64_MAX)) (PreH6 : (out_5 <= UINT64_MAX)) (PreH7 : (out_6 <= UINT64_MAX)) (PreH8 : (out_7 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (out >= 0)) (PreH14 : (out_5 >= 0)) (PreH15 : (out_6 >= 0)) (PreH16 : (out_7 >= 0)) (PreH17 : (0 <= out_7)) (PreH18 : (out_7 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_6)) (PreH23 : (out_6 < U64_MOD)) (PreH24 : (0 <= retval_7)) (PreH25 : (retval_7 <= 1)) (PreH26 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH27 : (0 <= out_5)) (PreH28 : (out_5 < U64_MOD)) (PreH29 : (0 <= retval_6)) (PreH30 : (retval_6 <= 1)) (PreH31 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH32 : (retval_5 = 0)) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_5)) (PreH36 : (retval_5 <= 1)) (PreH37 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH38 : (0 <= out_4)) (PreH39 : (out_4 < U64_MOD)) (PreH40 : (0 <= retval_4)) (PreH41 : (retval_4 <= 1)) (PreH42 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH43 : (0 <= out_3)) (PreH44 : (out_3 < U64_MOD)) (PreH45 : (0 <= retval_3)) (PreH46 : (retval_3 <= 1)) (PreH47 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH48 : (0 <= out_2)) (PreH49 : (out_2 < U64_MOD)) (PreH50 : (0 <= retval_2)) (PreH51 : (retval_2 <= 1)) (PreH52 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH53 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH54 : (x3_2 < U64_MOD)) (PreH55 : (0 <= x3_2)) (PreH56 : (x2_2 < U64_MOD)) (PreH57 : (0 <= x2_2)) (PreH58 : (x1_2 < U64_MOD)) (PreH59 : (0 <= x1_2)) (PreH60 : (x0_2 < U64_MOD)) (PreH61 : (0 <= x0_2)) (PreH62 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH63 : (x3 < U64_MOD)) (PreH64 : (0 <= x3)) (PreH65 : (x2 < U64_MOD)) (PreH66 : (0 <= x2)) (PreH67 : (x1 < U64_MOD)) (PreH68 : (0 <= x1)) (PreH69 : (x0 < U64_MOD)) (PreH70 : (0 <= x0)) (PreH71 : (B_r_eq_b < SM2_P_Z)) (PreH72 : (0 <= B_r_eq_b)) (PreH73 : (A_r_eq_b < SM2_P_Z)) (PreH74 : (0 <= A_r_eq_b)) (PreH75 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition sub_mod_p_partial_solve_wit_36_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH16 : (retval_5 = 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH38 : (x3_2 < U64_MOD)) (PreH39 : (0 <= x3_2)) (PreH40 : (x2_2 < U64_MOD)) (PreH41 : (0 <= x2_2)) (PreH42 : (x1_2 < U64_MOD)) (PreH43 : (0 <= x1_2)) (PreH44 : (x0_2 < U64_MOD)) (PreH45 : (0 <= x0_2)) (PreH46 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH47 : (x3 < U64_MOD)) (PreH48 : (0 <= x3)) (PreH49 : (x2 < U64_MOD)) (PreH50 : (0 <= x2)) (PreH51 : (x1 < U64_MOD)) (PreH52 : (0 <= x1)) (PreH53 : (x0 < U64_MOD)) (PreH54 : (0 <= x0)) (PreH55 : (B_r_eq_b < SM2_P_Z)) (PreH56 : (0 <= B_r_eq_b)) (PreH57 : (A_r_eq_b < SM2_P_Z)) (PreH58 : (0 <= A_r_eq_b)) (PreH59 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ (0 <= out_7) ” 
  &&  “ (out_7 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_4 + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (((out_3 + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out_5 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + (unsigned_last_nbits ((Z.lnot x3_2)) (64)) ) + retval_4 ) = (out + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + (unsigned_last_nbits ((Z.lnot x2_2)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + (unsigned_last_nbits ((Z.lnot x1_2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + (unsigned_last_nbits ((Z.lnot x0_2)) (64)) ) + 1 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition sub_mod_p_partial_solve_wit_36_r_eq_b := sub_mod_p_partial_solve_wit_36_r_eq_b_pure -> sub_mod_p_partial_solve_wit_36_r_eq_b_aux.

Definition sub_mod_p_derive_mont_r_eq_b_by_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_mont_r_eq_b: Z) (A_mont_r_eq_b: Z) ,
  “ (result_pre = b_pre) ” 
  &&  “ (0 <= A_mont_r_eq_b) ” 
  &&  “ (A_mont_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_mont_r_eq_b) ” 
  &&  “ (B_mont_r_eq_b < SM2_P_Z) ”
  &&  (store_fp a_pre (mont_p (A_mont_r_eq_b)) )
  **  (store_fp b_pre (mont_p (B_mont_r_eq_b)) )
  **  (store_sm2_p )
|--
EX (A_r_eq_b: Z) (B_r_eq_b: Z) ,
  (“ (result_pre = b_pre) ”
  &&  (store_fp a_pre A_r_eq_b )
  **  (store_fp b_pre B_r_eq_b )
  **  (store_sm2_p ))
  **
  ((“ (result_pre = b_pre) ”
  &&  (store_fp a_pre A_r_eq_b )
  **  (store_fp result_pre (Zmod ((A_r_eq_b - B_r_eq_b )) (SM2_P_Z)) )
  **  (store_sm2_p ))
  -*
  (“ (result_pre = b_pre) ”
  &&  (store_fp a_pre (mont_p (A_mont_r_eq_b)) )
  **  (store_fp result_pre (mont_p ((A_mont_r_eq_b - B_mont_r_eq_b ))) )
  **  (store_sm2_p )))
.

Definition sub_mod_p_derive_mont_non_alias_by_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_mont_non_alias: Z) (A_mont_non_alias: Z) ,
  “ (0 <= A_mont_non_alias) ” 
  &&  “ (A_mont_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_mont_non_alias) ” 
  &&  “ (B_mont_non_alias < SM2_P_Z) ”
  &&  (store_fp a_pre (mont_p (A_mont_non_alias)) )
  **  (store_fp b_pre (mont_p (B_mont_non_alias)) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
EX (A_non_alias: Z) (B_non_alias: Z) ,
  ((store_fp a_pre A_non_alias )
  **  (store_fp b_pre B_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  **
  (((store_fp a_pre A_non_alias )
  **  (store_fp b_pre B_non_alias )
  **  (store_fp result_pre (Zmod ((A_non_alias - B_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p ))
  -*
  ((store_fp a_pre (mont_p (A_mont_non_alias)) )
  **  (store_fp b_pre (mont_p (B_mont_non_alias)) )
  **  (store_fp result_pre (mont_p ((A_mont_non_alias - B_mont_non_alias ))) )
  **  (store_sm2_p )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_sub_mod_p_safety_wit_1_non_alias : sub_mod_p_safety_wit_1_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_2_r_eq_a : sub_mod_p_safety_wit_2_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_3_r_eq_b : sub_mod_p_safety_wit_3_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_4_non_alias : sub_mod_p_safety_wit_4_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_5_non_alias : sub_mod_p_safety_wit_5_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_6_non_alias : sub_mod_p_safety_wit_6_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_7_r_eq_a : sub_mod_p_safety_wit_7_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_8_r_eq_a : sub_mod_p_safety_wit_8_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_9_r_eq_a : sub_mod_p_safety_wit_9_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_10_r_eq_b : sub_mod_p_safety_wit_10_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_11_r_eq_b : sub_mod_p_safety_wit_11_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_12_r_eq_b : sub_mod_p_safety_wit_12_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_13_non_alias : sub_mod_p_safety_wit_13_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_14_non_alias : sub_mod_p_safety_wit_14_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_15_non_alias : sub_mod_p_safety_wit_15_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_16_r_eq_a : sub_mod_p_safety_wit_16_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_17_r_eq_a : sub_mod_p_safety_wit_17_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_18_r_eq_a : sub_mod_p_safety_wit_18_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_19_r_eq_b : sub_mod_p_safety_wit_19_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_20_r_eq_b : sub_mod_p_safety_wit_20_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_21_r_eq_b : sub_mod_p_safety_wit_21_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_22_non_alias : sub_mod_p_safety_wit_22_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_23_non_alias : sub_mod_p_safety_wit_23_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_24_non_alias : sub_mod_p_safety_wit_24_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_25_r_eq_a : sub_mod_p_safety_wit_25_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_26_r_eq_a : sub_mod_p_safety_wit_26_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_27_r_eq_a : sub_mod_p_safety_wit_27_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_28_r_eq_b : sub_mod_p_safety_wit_28_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_29_r_eq_b : sub_mod_p_safety_wit_29_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_30_r_eq_b : sub_mod_p_safety_wit_30_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_31_non_alias : sub_mod_p_safety_wit_31_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_32_non_alias : sub_mod_p_safety_wit_32_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_33_non_alias : sub_mod_p_safety_wit_33_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_34_r_eq_a : sub_mod_p_safety_wit_34_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_35_r_eq_a : sub_mod_p_safety_wit_35_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_36_r_eq_a : sub_mod_p_safety_wit_36_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_37_r_eq_b : sub_mod_p_safety_wit_37_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_38_r_eq_b : sub_mod_p_safety_wit_38_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_39_r_eq_b : sub_mod_p_safety_wit_39_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_40_non_alias : sub_mod_p_safety_wit_40_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_41_r_eq_a : sub_mod_p_safety_wit_41_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_42_r_eq_b : sub_mod_p_safety_wit_42_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_43_non_alias : sub_mod_p_safety_wit_43_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_44_non_alias : sub_mod_p_safety_wit_44_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_45_non_alias : sub_mod_p_safety_wit_45_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_46_r_eq_a : sub_mod_p_safety_wit_46_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_47_r_eq_a : sub_mod_p_safety_wit_47_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_48_r_eq_a : sub_mod_p_safety_wit_48_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_49_r_eq_b : sub_mod_p_safety_wit_49_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_50_r_eq_b : sub_mod_p_safety_wit_50_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_51_r_eq_b : sub_mod_p_safety_wit_51_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_52_non_alias : sub_mod_p_safety_wit_52_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_53_non_alias : sub_mod_p_safety_wit_53_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_54_non_alias : sub_mod_p_safety_wit_54_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_55_r_eq_a : sub_mod_p_safety_wit_55_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_56_r_eq_a : sub_mod_p_safety_wit_56_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_57_r_eq_a : sub_mod_p_safety_wit_57_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_58_r_eq_b : sub_mod_p_safety_wit_58_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_59_r_eq_b : sub_mod_p_safety_wit_59_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_60_r_eq_b : sub_mod_p_safety_wit_60_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_61_non_alias : sub_mod_p_safety_wit_61_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_62_non_alias : sub_mod_p_safety_wit_62_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_63_non_alias : sub_mod_p_safety_wit_63_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_64_r_eq_a : sub_mod_p_safety_wit_64_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_65_r_eq_a : sub_mod_p_safety_wit_65_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_66_r_eq_a : sub_mod_p_safety_wit_66_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_67_r_eq_b : sub_mod_p_safety_wit_67_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_68_r_eq_b : sub_mod_p_safety_wit_68_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_69_r_eq_b : sub_mod_p_safety_wit_69_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_70_non_alias : sub_mod_p_safety_wit_70_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_71_non_alias : sub_mod_p_safety_wit_71_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_72_non_alias : sub_mod_p_safety_wit_72_non_alias.
Axiom proof_of_sub_mod_p_safety_wit_73_r_eq_a : sub_mod_p_safety_wit_73_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_74_r_eq_a : sub_mod_p_safety_wit_74_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_75_r_eq_a : sub_mod_p_safety_wit_75_r_eq_a.
Axiom proof_of_sub_mod_p_safety_wit_76_r_eq_b : sub_mod_p_safety_wit_76_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_77_r_eq_b : sub_mod_p_safety_wit_77_r_eq_b.
Axiom proof_of_sub_mod_p_safety_wit_78_r_eq_b : sub_mod_p_safety_wit_78_r_eq_b.
Axiom proof_of_sub_mod_p_entail_wit_1_1_non_alias : sub_mod_p_entail_wit_1_1_non_alias.
Axiom proof_of_sub_mod_p_entail_wit_1_2_r_eq_a : sub_mod_p_entail_wit_1_2_r_eq_a.
Axiom proof_of_sub_mod_p_entail_wit_1_3_r_eq_b : sub_mod_p_entail_wit_1_3_r_eq_b.
Axiom proof_of_sub_mod_p_entail_wit_2_1_non_alias : sub_mod_p_entail_wit_2_1_non_alias.
Axiom proof_of_sub_mod_p_entail_wit_2_2_r_eq_a : sub_mod_p_entail_wit_2_2_r_eq_a.
Axiom proof_of_sub_mod_p_entail_wit_2_3_r_eq_b : sub_mod_p_entail_wit_2_3_r_eq_b.
Axiom proof_of_sub_mod_p_entail_wit_3_1_non_alias : sub_mod_p_entail_wit_3_1_non_alias.
Axiom proof_of_sub_mod_p_entail_wit_3_2_r_eq_a : sub_mod_p_entail_wit_3_2_r_eq_a.
Axiom proof_of_sub_mod_p_entail_wit_3_3_r_eq_b : sub_mod_p_entail_wit_3_3_r_eq_b.
Axiom proof_of_sub_mod_p_return_wit_1_non_alias : sub_mod_p_return_wit_1_non_alias.
Axiom proof_of_sub_mod_p_return_wit_2_r_eq_a : sub_mod_p_return_wit_2_r_eq_a.
Axiom proof_of_sub_mod_p_return_wit_3_r_eq_b : sub_mod_p_return_wit_3_r_eq_b.
Axiom proof_of_sub_mod_p_return_wit_4_non_alias : sub_mod_p_return_wit_4_non_alias.
Axiom proof_of_sub_mod_p_return_wit_5_r_eq_a : sub_mod_p_return_wit_5_r_eq_a.
Axiom proof_of_sub_mod_p_return_wit_6_r_eq_b : sub_mod_p_return_wit_6_r_eq_b.
Axiom proof_of_sub_mod_p_partial_solve_wit_1_non_alias_pure : sub_mod_p_partial_solve_wit_1_non_alias_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_1_non_alias : sub_mod_p_partial_solve_wit_1_non_alias.
Axiom proof_of_sub_mod_p_partial_solve_wit_2_r_eq_a_pure : sub_mod_p_partial_solve_wit_2_r_eq_a_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_2_r_eq_a : sub_mod_p_partial_solve_wit_2_r_eq_a.
Axiom proof_of_sub_mod_p_partial_solve_wit_3_r_eq_b_pure : sub_mod_p_partial_solve_wit_3_r_eq_b_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_3_r_eq_b : sub_mod_p_partial_solve_wit_3_r_eq_b.
Axiom proof_of_sub_mod_p_partial_solve_wit_4_non_alias_pure : sub_mod_p_partial_solve_wit_4_non_alias_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_4_non_alias : sub_mod_p_partial_solve_wit_4_non_alias.
Axiom proof_of_sub_mod_p_partial_solve_wit_5_r_eq_a_pure : sub_mod_p_partial_solve_wit_5_r_eq_a_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_5_r_eq_a : sub_mod_p_partial_solve_wit_5_r_eq_a.
Axiom proof_of_sub_mod_p_partial_solve_wit_6_r_eq_b_pure : sub_mod_p_partial_solve_wit_6_r_eq_b_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_6_r_eq_b : sub_mod_p_partial_solve_wit_6_r_eq_b.
Axiom proof_of_sub_mod_p_partial_solve_wit_7_non_alias_pure : sub_mod_p_partial_solve_wit_7_non_alias_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_7_non_alias : sub_mod_p_partial_solve_wit_7_non_alias.
Axiom proof_of_sub_mod_p_partial_solve_wit_8_r_eq_a_pure : sub_mod_p_partial_solve_wit_8_r_eq_a_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_8_r_eq_a : sub_mod_p_partial_solve_wit_8_r_eq_a.
Axiom proof_of_sub_mod_p_partial_solve_wit_9_r_eq_b_pure : sub_mod_p_partial_solve_wit_9_r_eq_b_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_9_r_eq_b : sub_mod_p_partial_solve_wit_9_r_eq_b.
Axiom proof_of_sub_mod_p_partial_solve_wit_10_non_alias_pure : sub_mod_p_partial_solve_wit_10_non_alias_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_10_non_alias : sub_mod_p_partial_solve_wit_10_non_alias.
Axiom proof_of_sub_mod_p_partial_solve_wit_11_r_eq_a_pure : sub_mod_p_partial_solve_wit_11_r_eq_a_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_11_r_eq_a : sub_mod_p_partial_solve_wit_11_r_eq_a.
Axiom proof_of_sub_mod_p_partial_solve_wit_12_r_eq_b_pure : sub_mod_p_partial_solve_wit_12_r_eq_b_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_12_r_eq_b : sub_mod_p_partial_solve_wit_12_r_eq_b.
Axiom proof_of_sub_mod_p_partial_solve_wit_13_non_alias : sub_mod_p_partial_solve_wit_13_non_alias.
Axiom proof_of_sub_mod_p_partial_solve_wit_14_non_alias_pure : sub_mod_p_partial_solve_wit_14_non_alias_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_14_non_alias : sub_mod_p_partial_solve_wit_14_non_alias.
Axiom proof_of_sub_mod_p_partial_solve_wit_15_r_eq_a : sub_mod_p_partial_solve_wit_15_r_eq_a.
Axiom proof_of_sub_mod_p_partial_solve_wit_16_r_eq_a_pure : sub_mod_p_partial_solve_wit_16_r_eq_a_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_16_r_eq_a : sub_mod_p_partial_solve_wit_16_r_eq_a.
Axiom proof_of_sub_mod_p_partial_solve_wit_17_r_eq_b : sub_mod_p_partial_solve_wit_17_r_eq_b.
Axiom proof_of_sub_mod_p_partial_solve_wit_18_r_eq_b_pure : sub_mod_p_partial_solve_wit_18_r_eq_b_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_18_r_eq_b : sub_mod_p_partial_solve_wit_18_r_eq_b.
Axiom proof_of_sub_mod_p_partial_solve_wit_19_non_alias : sub_mod_p_partial_solve_wit_19_non_alias.
Axiom proof_of_sub_mod_p_partial_solve_wit_20_non_alias_pure : sub_mod_p_partial_solve_wit_20_non_alias_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_20_non_alias : sub_mod_p_partial_solve_wit_20_non_alias.
Axiom proof_of_sub_mod_p_partial_solve_wit_21_r_eq_a : sub_mod_p_partial_solve_wit_21_r_eq_a.
Axiom proof_of_sub_mod_p_partial_solve_wit_22_r_eq_a_pure : sub_mod_p_partial_solve_wit_22_r_eq_a_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_22_r_eq_a : sub_mod_p_partial_solve_wit_22_r_eq_a.
Axiom proof_of_sub_mod_p_partial_solve_wit_23_r_eq_b : sub_mod_p_partial_solve_wit_23_r_eq_b.
Axiom proof_of_sub_mod_p_partial_solve_wit_24_r_eq_b_pure : sub_mod_p_partial_solve_wit_24_r_eq_b_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_24_r_eq_b : sub_mod_p_partial_solve_wit_24_r_eq_b.
Axiom proof_of_sub_mod_p_partial_solve_wit_25_non_alias : sub_mod_p_partial_solve_wit_25_non_alias.
Axiom proof_of_sub_mod_p_partial_solve_wit_26_non_alias_pure : sub_mod_p_partial_solve_wit_26_non_alias_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_26_non_alias : sub_mod_p_partial_solve_wit_26_non_alias.
Axiom proof_of_sub_mod_p_partial_solve_wit_27_r_eq_a : sub_mod_p_partial_solve_wit_27_r_eq_a.
Axiom proof_of_sub_mod_p_partial_solve_wit_28_r_eq_a_pure : sub_mod_p_partial_solve_wit_28_r_eq_a_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_28_r_eq_a : sub_mod_p_partial_solve_wit_28_r_eq_a.
Axiom proof_of_sub_mod_p_partial_solve_wit_29_r_eq_b : sub_mod_p_partial_solve_wit_29_r_eq_b.
Axiom proof_of_sub_mod_p_partial_solve_wit_30_r_eq_b_pure : sub_mod_p_partial_solve_wit_30_r_eq_b_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_30_r_eq_b : sub_mod_p_partial_solve_wit_30_r_eq_b.
Axiom proof_of_sub_mod_p_partial_solve_wit_31_non_alias : sub_mod_p_partial_solve_wit_31_non_alias.
Axiom proof_of_sub_mod_p_partial_solve_wit_32_non_alias_pure : sub_mod_p_partial_solve_wit_32_non_alias_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_32_non_alias : sub_mod_p_partial_solve_wit_32_non_alias.
Axiom proof_of_sub_mod_p_partial_solve_wit_33_r_eq_a : sub_mod_p_partial_solve_wit_33_r_eq_a.
Axiom proof_of_sub_mod_p_partial_solve_wit_34_r_eq_a_pure : sub_mod_p_partial_solve_wit_34_r_eq_a_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_34_r_eq_a : sub_mod_p_partial_solve_wit_34_r_eq_a.
Axiom proof_of_sub_mod_p_partial_solve_wit_35_r_eq_b : sub_mod_p_partial_solve_wit_35_r_eq_b.
Axiom proof_of_sub_mod_p_partial_solve_wit_36_r_eq_b_pure : sub_mod_p_partial_solve_wit_36_r_eq_b_pure.
Axiom proof_of_sub_mod_p_partial_solve_wit_36_r_eq_b : sub_mod_p_partial_solve_wit_36_r_eq_b.
Axiom proof_of_sub_mod_p_derive_mont_r_eq_b_by_r_eq_b : sub_mod_p_derive_mont_r_eq_b_by_r_eq_b.
Axiom proof_of_sub_mod_p_derive_mont_non_alias_by_non_alias : sub_mod_p_derive_mont_non_alias_by_non_alias.

End VC_Correct.
