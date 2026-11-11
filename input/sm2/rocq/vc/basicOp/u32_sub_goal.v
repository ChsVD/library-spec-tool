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
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.

(*----- Function u32_sub -----*)

Definition u32_sub_safety_wit_1_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_sub_safety_wit_2_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_sub_safety_wit_3_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_sub_safety_wit_4_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u32_sub_safety_wit_5_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u32_sub_safety_wit_6_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u32_sub_safety_wit_7_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u32_sub_safety_wit_8_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u32_sub_safety_wit_9_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u32_sub_safety_wit_10_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u32_sub_safety_wit_11_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u32_sub_safety_wit_12_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u32_sub_safety_wit_13_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_sub_safety_wit_14_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_sub_safety_wit_15_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_sub_safety_wit_16_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_sub_safety_wit_17_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_sub_safety_wit_18_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_sub_safety_wit_19_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_sub_safety_wit_20_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_sub_safety_wit_21_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_sub_safety_wit_22_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_sub_safety_wit_23_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_sub_safety_wit_24_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_sub_safety_wit_25_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_sub_safety_wit_26_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_sub_safety_wit_27_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_sub_safety_wit_28_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_sub_safety_wit_29_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_sub_safety_wit_30_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_sub_safety_wit_31_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_sub_safety_wit_32_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_sub_safety_wit_33_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_sub_safety_wit_34_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_sub_safety_wit_35_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_sub_safety_wit_36_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_sub_safety_wit_37_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_sub_safety_wit_38_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_sub_safety_wit_39_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_sub_entail_wit_1_1_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (PreH1 : (result_pre = b_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_r_eq_b )
  **  (store_u256 b_pre B_r_eq_b )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (A_r_eq_a = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 ))
.

Definition u32_sub_entail_wit_1_2_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (PreH1 : (result_pre = a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_r_eq_a )
  **  (store_u256 b_pre B_r_eq_a )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (A_r_eq_a = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 ))
.

Definition u32_sub_entail_wit_1_3_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (store_u256 b_pre B_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (A_r_eq_a = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 ))
.

Definition u32_sub_return_wit_1_r_eq_b := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3_2 + (unsigned_last_nbits ((Z.lnot x3)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
|--
  EX (borrow: Z)  (S: Z) ,
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((A_r_eq_b - B_r_eq_b ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (store_u256 a_pre A_r_eq_b )
  **  (store_u256 result_pre S )
) \/
(
forall (result_pre: Z) (b_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3_2 + (unsigned_last_nbits ((Z.lnot x3)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (result_pre = b_pre)) ,
  TT && emp 
|--
  EX (borrow: Z) ,
  “ (0 <= (u256_of_limbs (out) (out_2) (out_3) (out_4))) ” 
  &&  “ ((u256_of_limbs (out) (out_2) (out_3) (out_4)) < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs (x0) (x1) (x2) (x3)) ) = ((u256_of_limbs (out) (out_2) (out_3) (out_4)) - (borrow * U256_MOD ) )) ”
  &&  emp
).

Definition u32_sub_return_wit_2_r_eq_a := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3_2 + (unsigned_last_nbits ((Z.lnot x3)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  EX (borrow: Z)  (S: Z) ,
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((A_r_eq_a - B_r_eq_a ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (store_u256 result_pre S )
  **  (store_u256 b_pre B_r_eq_a )
) \/
(
forall (result_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3_2 + (unsigned_last_nbits ((Z.lnot x3)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (result_pre = a_pre)) ,
  TT && emp 
|--
  EX (borrow: Z) ,
  “ (0 <= (u256_of_limbs (out) (out_2) (out_3) (out_4))) ” 
  &&  “ ((u256_of_limbs (out) (out_2) (out_3) (out_4)) < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs (x0) (x1) (x2) (x3)) ) = ((u256_of_limbs (out) (out_2) (out_3) (out_4)) - (borrow * U256_MOD ) )) ”
  &&  emp
).

Definition u32_sub_return_wit_3_non_alias := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3_2 + (unsigned_last_nbits ((Z.lnot x3)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  EX (borrow: Z)  (S: Z) ,
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((A_non_alias - B_non_alias ) = (S - (borrow * U256_MOD ) )) ”
  &&  (store_u256 a_pre A_non_alias )
  **  (store_u256 b_pre B_non_alias )
  **  (store_u256 result_pre S )
) \/
(
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3_2 + (unsigned_last_nbits ((Z.lnot x3)) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) ,
  TT && emp 
|--
  EX (borrow: Z) ,
  “ (0 <= (u256_of_limbs (out) (out_2) (out_3) (out_4))) ” 
  &&  “ ((u256_of_limbs (out) (out_2) (out_3) (out_4)) < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs (x0) (x1) (x2) (x3)) ) = ((u256_of_limbs (out) (out_2) (out_3) (out_4)) - (borrow * U256_MOD ) )) ”
  &&  emp
).

Definition u32_sub_partial_solve_wit_1_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x0)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x0)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0)) (64)) < U64_MOD) ”
).

Definition u32_sub_partial_solve_wit_1_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x0)) (64))) ”
.

Definition u32_sub_partial_solve_wit_1_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x0)) (64)) < U64_MOD) ”
.

Definition u32_sub_partial_solve_wit_1_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = b_pre)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x0)) (64))) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
.

Definition u32_sub_partial_solve_wit_1_r_eq_b := u32_sub_partial_solve_wit_1_r_eq_b_pure -> u32_sub_partial_solve_wit_1_r_eq_b_aux.

Definition u32_sub_partial_solve_wit_2_r_eq_a_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x0)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x0)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0)) (64)) < U64_MOD) ”
).

Definition u32_sub_partial_solve_wit_2_r_eq_a_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x0)) (64))) ”
.

Definition u32_sub_partial_solve_wit_2_r_eq_a_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) (PreH35 : (result_pre = a_pre)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x0)) (64)) < U64_MOD) ”
.

Definition u32_sub_partial_solve_wit_2_r_eq_a_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (result_pre = a_pre)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x0)) (64))) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition u32_sub_partial_solve_wit_2_r_eq_a := u32_sub_partial_solve_wit_2_r_eq_a_pure -> u32_sub_partial_solve_wit_2_r_eq_a_aux.

Definition u32_sub_partial_solve_wit_3_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x0)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x0)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0)) (64)) < U64_MOD) ”
).

Definition u32_sub_partial_solve_wit_3_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x0)) (64))) ”
.

Definition u32_sub_partial_solve_wit_3_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0_2 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH18 : (x3_2 < U64_MOD)) (PreH19 : (0 <= x3_2)) (PreH20 : (x2_2 < U64_MOD)) (PreH21 : (0 <= x2_2)) (PreH22 : (x1_2 < U64_MOD)) (PreH23 : (0 <= x1_2)) (PreH24 : (x0_2 < U64_MOD)) (PreH25 : (0 <= x0_2)) (PreH26 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH27 : (x3 < U64_MOD)) (PreH28 : (0 <= x3)) (PreH29 : (x2 < U64_MOD)) (PreH30 : (0 <= x2)) (PreH31 : (x1 < U64_MOD)) (PreH32 : (0 <= x1)) (PreH33 : (x0 < U64_MOD)) (PreH34 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> 1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ ((unsigned_last_nbits ((Z.lnot x0)) (64)) < U64_MOD) ”
.

Definition u32_sub_partial_solve_wit_3_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x0)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x0)) (64))) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition u32_sub_partial_solve_wit_3_non_alias := u32_sub_partial_solve_wit_3_non_alias_pure -> u32_sub_partial_solve_wit_3_non_alias_aux.

Definition u32_sub_partial_solve_wit_4_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x1)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x1 <= UINT64_MAX)) (PreH2 : (x2 <= UINT64_MAX)) (PreH3 : (x3 <= UINT64_MAX)) (PreH4 : (x0_2 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out <= UINT64_MAX)) (PreH9 : (x1 >= 0)) (PreH10 : (x2 >= 0)) (PreH11 : (x3 >= 0)) (PreH12 : (x0_2 >= 0)) (PreH13 : (x1_2 >= 0)) (PreH14 : (x2_2 >= 0)) (PreH15 : (x3_2 >= 0)) (PreH16 : (out >= 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x1)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1)) (64)) < U64_MOD) ”
).

Definition u32_sub_partial_solve_wit_4_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x1 <= UINT64_MAX)) (PreH2 : (x2 <= UINT64_MAX)) (PreH3 : (x3 <= UINT64_MAX)) (PreH4 : (x0_2 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out <= UINT64_MAX)) (PreH9 : (x1 >= 0)) (PreH10 : (x2 >= 0)) (PreH11 : (x3 >= 0)) (PreH12 : (x0_2 >= 0)) (PreH13 : (x1_2 >= 0)) (PreH14 : (x2_2 >= 0)) (PreH15 : (x3_2 >= 0)) (PreH16 : (out >= 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x1)) (64))) ”
.

Definition u32_sub_partial_solve_wit_4_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x1 <= UINT64_MAX)) (PreH2 : (x2 <= UINT64_MAX)) (PreH3 : (x3 <= UINT64_MAX)) (PreH4 : (x0_2 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out <= UINT64_MAX)) (PreH9 : (x1 >= 0)) (PreH10 : (x2 >= 0)) (PreH11 : (x3 >= 0)) (PreH12 : (x0_2 >= 0)) (PreH13 : (x1_2 >= 0)) (PreH14 : (x2_2 >= 0)) (PreH15 : (x3_2 >= 0)) (PreH16 : (out >= 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x1)) (64)) < U64_MOD) ”
.

Definition u32_sub_partial_solve_wit_4_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x1)) (64))) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
.

Definition u32_sub_partial_solve_wit_4_r_eq_b := u32_sub_partial_solve_wit_4_r_eq_b_pure -> u32_sub_partial_solve_wit_4_r_eq_b_aux.

Definition u32_sub_partial_solve_wit_5_r_eq_a_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x1)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x1_2 >= 0)) (PreH14 : (x2_2 >= 0)) (PreH15 : (x3_2 >= 0)) (PreH16 : (out >= 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x1)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1)) (64)) < U64_MOD) ”
).

Definition u32_sub_partial_solve_wit_5_r_eq_a_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x1_2 >= 0)) (PreH14 : (x2_2 >= 0)) (PreH15 : (x3_2 >= 0)) (PreH16 : (out >= 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x1)) (64))) ”
.

Definition u32_sub_partial_solve_wit_5_r_eq_a_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x1_2 >= 0)) (PreH14 : (x2_2 >= 0)) (PreH15 : (x3_2 >= 0)) (PreH16 : (out >= 0)) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x1)) (64)) < U64_MOD) ”
.

Definition u32_sub_partial_solve_wit_5_r_eq_a_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x1)) (64))) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition u32_sub_partial_solve_wit_5_r_eq_a := u32_sub_partial_solve_wit_5_r_eq_a_pure -> u32_sub_partial_solve_wit_5_r_eq_a_aux.

Definition u32_sub_partial_solve_wit_6_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x1)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (x0 >= 0)) (PreH11 : (x1 >= 0)) (PreH12 : (x2 >= 0)) (PreH13 : (x3 >= 0)) (PreH14 : (x0_2 >= 0)) (PreH15 : (x1_2 >= 0)) (PreH16 : (x2_2 >= 0)) (PreH17 : (x3_2 >= 0)) (PreH18 : (out >= 0)) (PreH19 : (0 <= out)) (PreH20 : (out < U64_MOD)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH24 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x1)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1)) (64)) < U64_MOD) ”
).

Definition u32_sub_partial_solve_wit_6_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (x0 >= 0)) (PreH11 : (x1 >= 0)) (PreH12 : (x2 >= 0)) (PreH13 : (x3 >= 0)) (PreH14 : (x0_2 >= 0)) (PreH15 : (x1_2 >= 0)) (PreH16 : (x2_2 >= 0)) (PreH17 : (x3_2 >= 0)) (PreH18 : (out >= 0)) (PreH19 : (0 <= out)) (PreH20 : (out < U64_MOD)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH24 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x1)) (64))) ”
.

Definition u32_sub_partial_solve_wit_6_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (x0 >= 0)) (PreH11 : (x1 >= 0)) (PreH12 : (x2 >= 0)) (PreH13 : (x3 >= 0)) (PreH14 : (x0_2 >= 0)) (PreH15 : (x1_2 >= 0)) (PreH16 : (x2_2 >= 0)) (PreH17 : (x3_2 >= 0)) (PreH18 : (out >= 0)) (PreH19 : (0 <= out)) (PreH20 : (out < U64_MOD)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH24 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x1)) (64)) < U64_MOD) ”
.

Definition u32_sub_partial_solve_wit_6_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x1)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x1)) (64))) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition u32_sub_partial_solve_wit_6_non_alias := u32_sub_partial_solve_wit_6_non_alias_pure -> u32_sub_partial_solve_wit_6_non_alias_aux.

Definition u32_sub_partial_solve_wit_7_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x2 <= UINT64_MAX)) (PreH2 : (x3 <= UINT64_MAX)) (PreH3 : (x0_2 <= UINT64_MAX)) (PreH4 : (x1_2 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (x2 >= 0)) (PreH10 : (x3 >= 0)) (PreH11 : (x0_2 >= 0)) (PreH12 : (x1_2 >= 0)) (PreH13 : (x2_2 >= 0)) (PreH14 : (x3_2 >= 0)) (PreH15 : (out >= 0)) (PreH16 : (out_2 >= 0)) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH27 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2)) (64)) < U64_MOD) ”
).

Definition u32_sub_partial_solve_wit_7_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x2 <= UINT64_MAX)) (PreH2 : (x3 <= UINT64_MAX)) (PreH3 : (x0_2 <= UINT64_MAX)) (PreH4 : (x1_2 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (x2 >= 0)) (PreH10 : (x3 >= 0)) (PreH11 : (x0_2 >= 0)) (PreH12 : (x1_2 >= 0)) (PreH13 : (x2_2 >= 0)) (PreH14 : (x3_2 >= 0)) (PreH15 : (out >= 0)) (PreH16 : (out_2 >= 0)) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH27 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x2)) (64))) ”
.

Definition u32_sub_partial_solve_wit_7_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x2 <= UINT64_MAX)) (PreH2 : (x3 <= UINT64_MAX)) (PreH3 : (x0_2 <= UINT64_MAX)) (PreH4 : (x1_2 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (x2 >= 0)) (PreH10 : (x3 >= 0)) (PreH11 : (x0_2 >= 0)) (PreH12 : (x1_2 >= 0)) (PreH13 : (x2_2 >= 0)) (PreH14 : (x3_2 >= 0)) (PreH15 : (out >= 0)) (PreH16 : (out_2 >= 0)) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH27 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x2)) (64)) < U64_MOD) ”
.

Definition u32_sub_partial_solve_wit_7_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x2)) (64))) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
.

Definition u32_sub_partial_solve_wit_7_r_eq_b := u32_sub_partial_solve_wit_7_r_eq_b_pure -> u32_sub_partial_solve_wit_7_r_eq_b_aux.

Definition u32_sub_partial_solve_wit_8_r_eq_a_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x2_2 >= 0)) (PreH14 : (x3_2 >= 0)) (PreH15 : (out >= 0)) (PreH16 : (out_2 >= 0)) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH27 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2)) (64)) < U64_MOD) ”
).

Definition u32_sub_partial_solve_wit_8_r_eq_a_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x2_2 >= 0)) (PreH14 : (x3_2 >= 0)) (PreH15 : (out >= 0)) (PreH16 : (out_2 >= 0)) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH27 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x2)) (64))) ”
.

Definition u32_sub_partial_solve_wit_8_r_eq_a_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x2_2 >= 0)) (PreH14 : (x3_2 >= 0)) (PreH15 : (out >= 0)) (PreH16 : (out_2 >= 0)) (PreH17 : (0 <= out_2)) (PreH18 : (out_2 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out)) (PreH23 : (out < U64_MOD)) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 1)) (PreH26 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH27 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH28 : (x3_2 < U64_MOD)) (PreH29 : (0 <= x3_2)) (PreH30 : (x2_2 < U64_MOD)) (PreH31 : (0 <= x2_2)) (PreH32 : (x1_2 < U64_MOD)) (PreH33 : (0 <= x1_2)) (PreH34 : (x0_2 < U64_MOD)) (PreH35 : (0 <= x0_2)) (PreH36 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH37 : (x3 < U64_MOD)) (PreH38 : (0 <= x3)) (PreH39 : (x2 < U64_MOD)) (PreH40 : (0 <= x2)) (PreH41 : (x1 < U64_MOD)) (PreH42 : (0 <= x1)) (PreH43 : (x0 < U64_MOD)) (PreH44 : (0 <= x0)) (PreH45 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x2)) (64)) < U64_MOD) ”
.

Definition u32_sub_partial_solve_wit_8_r_eq_a_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x2)) (64))) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition u32_sub_partial_solve_wit_8_r_eq_a := u32_sub_partial_solve_wit_8_r_eq_a_pure -> u32_sub_partial_solve_wit_8_r_eq_a_aux.

Definition u32_sub_partial_solve_wit_9_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x2)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (x0 >= 0)) (PreH12 : (x1 >= 0)) (PreH13 : (x2 >= 0)) (PreH14 : (x3 >= 0)) (PreH15 : (x0_2 >= 0)) (PreH16 : (x1_2 >= 0)) (PreH17 : (x2_2 >= 0)) (PreH18 : (x3_2 >= 0)) (PreH19 : (out >= 0)) (PreH20 : (out_2 >= 0)) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH31 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x2)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2)) (64)) < U64_MOD) ”
).

Definition u32_sub_partial_solve_wit_9_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (x0 >= 0)) (PreH12 : (x1 >= 0)) (PreH13 : (x2 >= 0)) (PreH14 : (x3 >= 0)) (PreH15 : (x0_2 >= 0)) (PreH16 : (x1_2 >= 0)) (PreH17 : (x2_2 >= 0)) (PreH18 : (x3_2 >= 0)) (PreH19 : (out >= 0)) (PreH20 : (out_2 >= 0)) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH31 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x2)) (64))) ”
.

Definition u32_sub_partial_solve_wit_9_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (x0 >= 0)) (PreH12 : (x1 >= 0)) (PreH13 : (x2 >= 0)) (PreH14 : (x3 >= 0)) (PreH15 : (x0_2 >= 0)) (PreH16 : (x1_2 >= 0)) (PreH17 : (x2_2 >= 0)) (PreH18 : (x3_2 >= 0)) (PreH19 : (out >= 0)) (PreH20 : (out_2 >= 0)) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH31 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x2)) (64)) < U64_MOD) ”
.

Definition u32_sub_partial_solve_wit_9_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x2)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x2)) (64))) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "u32" ->ₛ "v") 2 (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition u32_sub_partial_solve_wit_9_non_alias := u32_sub_partial_solve_wit_9_non_alias_pure -> u32_sub_partial_solve_wit_9_non_alias_aux.

Definition u32_sub_partial_solve_wit_10_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x3)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x3 <= UINT64_MAX)) (PreH2 : (x0_2 <= UINT64_MAX)) (PreH3 : (x1_2 <= UINT64_MAX)) (PreH4 : (x2_2 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (x3 >= 0)) (PreH10 : (x0_2 >= 0)) (PreH11 : (x1_2 >= 0)) (PreH12 : (x2_2 >= 0)) (PreH13 : (x3_2 >= 0)) (PreH14 : (out >= 0)) (PreH15 : (out_2 >= 0)) (PreH16 : (out_3 >= 0)) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH32 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x3)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3)) (64)) < U64_MOD) ”
).

Definition u32_sub_partial_solve_wit_10_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x3 <= UINT64_MAX)) (PreH2 : (x0_2 <= UINT64_MAX)) (PreH3 : (x1_2 <= UINT64_MAX)) (PreH4 : (x2_2 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (x3 >= 0)) (PreH10 : (x0_2 >= 0)) (PreH11 : (x1_2 >= 0)) (PreH12 : (x2_2 >= 0)) (PreH13 : (x3_2 >= 0)) (PreH14 : (out >= 0)) (PreH15 : (out_2 >= 0)) (PreH16 : (out_3 >= 0)) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH32 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x3)) (64))) ”
.

Definition u32_sub_partial_solve_wit_10_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x3 <= UINT64_MAX)) (PreH2 : (x0_2 <= UINT64_MAX)) (PreH3 : (x1_2 <= UINT64_MAX)) (PreH4 : (x2_2 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (x3 >= 0)) (PreH10 : (x0_2 >= 0)) (PreH11 : (x1_2 >= 0)) (PreH12 : (x2_2 >= 0)) (PreH13 : (x3_2 >= 0)) (PreH14 : (out >= 0)) (PreH15 : (out_2 >= 0)) (PreH16 : (out_3 >= 0)) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH32 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x3)) (64)) < U64_MOD) ”
.

Definition u32_sub_partial_solve_wit_10_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x3)) (64))) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
.

Definition u32_sub_partial_solve_wit_10_r_eq_b := u32_sub_partial_solve_wit_10_r_eq_b_pure -> u32_sub_partial_solve_wit_10_r_eq_b_aux.

Definition u32_sub_partial_solve_wit_11_r_eq_a_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x3)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x3_2 >= 0)) (PreH14 : (out >= 0)) (PreH15 : (out_2 >= 0)) (PreH16 : (out_3 >= 0)) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH32 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x3)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3)) (64)) < U64_MOD) ”
).

Definition u32_sub_partial_solve_wit_11_r_eq_a_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x3_2 >= 0)) (PreH14 : (out >= 0)) (PreH15 : (out_2 >= 0)) (PreH16 : (out_3 >= 0)) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH32 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x3)) (64))) ”
.

Definition u32_sub_partial_solve_wit_11_r_eq_a_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x3_2 >= 0)) (PreH14 : (out >= 0)) (PreH15 : (out_2 >= 0)) (PreH16 : (out_3 >= 0)) (PreH17 : (0 <= out_3)) (PreH18 : (out_3 < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH22 : (0 <= out_2)) (PreH23 : (out_2 < U64_MOD)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH27 : (0 <= out)) (PreH28 : (out < U64_MOD)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH32 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH33 : (x3_2 < U64_MOD)) (PreH34 : (0 <= x3_2)) (PreH35 : (x2_2 < U64_MOD)) (PreH36 : (0 <= x2_2)) (PreH37 : (x1_2 < U64_MOD)) (PreH38 : (0 <= x1_2)) (PreH39 : (x0_2 < U64_MOD)) (PreH40 : (0 <= x0_2)) (PreH41 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH42 : (x3 < U64_MOD)) (PreH43 : (0 <= x3)) (PreH44 : (x2 < U64_MOD)) (PreH45 : (0 <= x2)) (PreH46 : (x1 < U64_MOD)) (PreH47 : (0 <= x1)) (PreH48 : (x0 < U64_MOD)) (PreH49 : (0 <= x0)) (PreH50 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x3)) (64)) < U64_MOD) ”
.

Definition u32_sub_partial_solve_wit_11_r_eq_a_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (result_pre = a_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x3)) (64))) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (A_r_eq_a = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_r_eq_a = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition u32_sub_partial_solve_wit_11_r_eq_a := u32_sub_partial_solve_wit_11_r_eq_a_pure -> u32_sub_partial_solve_wit_11_r_eq_a_aux.

Definition u32_sub_partial_solve_wit_12_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x3)) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (x0 >= 0)) (PreH13 : (x1 >= 0)) (PreH14 : (x2 >= 0)) (PreH15 : (x3 >= 0)) (PreH16 : (x0_2 >= 0)) (PreH17 : (x1_2 >= 0)) (PreH18 : (x2_2 >= 0)) (PreH19 : (x3_2 >= 0)) (PreH20 : (out >= 0)) (PreH21 : (out_2 >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_3)) (PreH31 : (retval_3 <= 1)) (PreH32 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_2)) (PreH36 : (retval_2 <= 1)) (PreH37 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH38 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH39 : (x3_2 < U64_MOD)) (PreH40 : (0 <= x3_2)) (PreH41 : (x2_2 < U64_MOD)) (PreH42 : (0 <= x2_2)) (PreH43 : (x1_2 < U64_MOD)) (PreH44 : (0 <= x1_2)) (PreH45 : (x0_2 < U64_MOD)) (PreH46 : (0 <= x0_2)) (PreH47 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH48 : (x3 < U64_MOD)) (PreH49 : (0 <= x3)) (PreH50 : (x2 < U64_MOD)) (PreH51 : (0 <= x2)) (PreH52 : (x1 < U64_MOD)) (PreH53 : (0 <= x1)) (PreH54 : (x0 < U64_MOD)) (PreH55 : (0 <= x0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x3)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3)) (64)) < U64_MOD) ”
).

Definition u32_sub_partial_solve_wit_12_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (x0 >= 0)) (PreH13 : (x1 >= 0)) (PreH14 : (x2 >= 0)) (PreH15 : (x3 >= 0)) (PreH16 : (x0_2 >= 0)) (PreH17 : (x1_2 >= 0)) (PreH18 : (x2_2 >= 0)) (PreH19 : (x3_2 >= 0)) (PreH20 : (out >= 0)) (PreH21 : (out_2 >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_3)) (PreH31 : (retval_3 <= 1)) (PreH32 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_2)) (PreH36 : (retval_2 <= 1)) (PreH37 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH38 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH39 : (x3_2 < U64_MOD)) (PreH40 : (0 <= x3_2)) (PreH41 : (x2_2 < U64_MOD)) (PreH42 : (0 <= x2_2)) (PreH43 : (x1_2 < U64_MOD)) (PreH44 : (0 <= x1_2)) (PreH45 : (x0_2 < U64_MOD)) (PreH46 : (0 <= x0_2)) (PreH47 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH48 : (x3 < U64_MOD)) (PreH49 : (0 <= x3)) (PreH50 : (x2 < U64_MOD)) (PreH51 : (0 <= x2)) (PreH52 : (x1 < U64_MOD)) (PreH53 : (0 <= x1)) (PreH54 : (x0 < U64_MOD)) (PreH55 : (0 <= x0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot x3)) (64))) ”
.

Definition u32_sub_partial_solve_wit_12_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (x0 >= 0)) (PreH13 : (x1 >= 0)) (PreH14 : (x2 >= 0)) (PreH15 : (x3 >= 0)) (PreH16 : (x0_2 >= 0)) (PreH17 : (x1_2 >= 0)) (PreH18 : (x2_2 >= 0)) (PreH19 : (x3_2 >= 0)) (PreH20 : (out >= 0)) (PreH21 : (out_2 >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_3)) (PreH31 : (retval_3 <= 1)) (PreH32 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_2)) (PreH36 : (retval_2 <= 1)) (PreH37 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH38 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH39 : (x3_2 < U64_MOD)) (PreH40 : (0 <= x3_2)) (PreH41 : (x2_2 < U64_MOD)) (PreH42 : (0 <= x2_2)) (PreH43 : (x1_2 < U64_MOD)) (PreH44 : (0 <= x1_2)) (PreH45 : (x0_2 < U64_MOD)) (PreH46 : (0 <= x0_2)) (PreH47 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH48 : (x3 < U64_MOD)) (PreH49 : (0 <= x3)) (PreH50 : (x2 < U64_MOD)) (PreH51 : (0 <= x2)) (PreH52 : (x1 < U64_MOD)) (PreH53 : (0 <= x1)) (PreH54 : (x0 < U64_MOD)) (PreH55 : (0 <= x0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot x3)) (64)) < U64_MOD) ”
.

Definition u32_sub_partial_solve_wit_12_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot x3)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot x3)) (64))) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x2_2 + (unsigned_last_nbits ((Z.lnot x2)) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1_2 + (unsigned_last_nbits ((Z.lnot x1)) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0_2 + (unsigned_last_nbits ((Z.lnot x0)) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "u32" ->ₛ "v") 3 ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition u32_sub_partial_solve_wit_12_non_alias := u32_sub_partial_solve_wit_12_non_alias_pure -> u32_sub_partial_solve_wit_12_non_alias_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.

Axiom proof_of_u32_sub_safety_wit_1_r_eq_b : u32_sub_safety_wit_1_r_eq_b.
Axiom proof_of_u32_sub_safety_wit_2_r_eq_a : u32_sub_safety_wit_2_r_eq_a.
Axiom proof_of_u32_sub_safety_wit_3_non_alias : u32_sub_safety_wit_3_non_alias.
Axiom proof_of_u32_sub_safety_wit_4_r_eq_b : u32_sub_safety_wit_4_r_eq_b.
Axiom proof_of_u32_sub_safety_wit_5_r_eq_b : u32_sub_safety_wit_5_r_eq_b.
Axiom proof_of_u32_sub_safety_wit_6_r_eq_b : u32_sub_safety_wit_6_r_eq_b.
Axiom proof_of_u32_sub_safety_wit_7_r_eq_a : u32_sub_safety_wit_7_r_eq_a.
Axiom proof_of_u32_sub_safety_wit_8_r_eq_a : u32_sub_safety_wit_8_r_eq_a.
Axiom proof_of_u32_sub_safety_wit_9_r_eq_a : u32_sub_safety_wit_9_r_eq_a.
Axiom proof_of_u32_sub_safety_wit_10_non_alias : u32_sub_safety_wit_10_non_alias.
Axiom proof_of_u32_sub_safety_wit_11_non_alias : u32_sub_safety_wit_11_non_alias.
Axiom proof_of_u32_sub_safety_wit_12_non_alias : u32_sub_safety_wit_12_non_alias.
Axiom proof_of_u32_sub_safety_wit_13_r_eq_b : u32_sub_safety_wit_13_r_eq_b.
Axiom proof_of_u32_sub_safety_wit_14_r_eq_b : u32_sub_safety_wit_14_r_eq_b.
Axiom proof_of_u32_sub_safety_wit_15_r_eq_b : u32_sub_safety_wit_15_r_eq_b.
Axiom proof_of_u32_sub_safety_wit_16_r_eq_a : u32_sub_safety_wit_16_r_eq_a.
Axiom proof_of_u32_sub_safety_wit_17_r_eq_a : u32_sub_safety_wit_17_r_eq_a.
Axiom proof_of_u32_sub_safety_wit_18_r_eq_a : u32_sub_safety_wit_18_r_eq_a.
Axiom proof_of_u32_sub_safety_wit_19_non_alias : u32_sub_safety_wit_19_non_alias.
Axiom proof_of_u32_sub_safety_wit_20_non_alias : u32_sub_safety_wit_20_non_alias.
Axiom proof_of_u32_sub_safety_wit_21_non_alias : u32_sub_safety_wit_21_non_alias.
Axiom proof_of_u32_sub_safety_wit_22_r_eq_b : u32_sub_safety_wit_22_r_eq_b.
Axiom proof_of_u32_sub_safety_wit_23_r_eq_b : u32_sub_safety_wit_23_r_eq_b.
Axiom proof_of_u32_sub_safety_wit_24_r_eq_b : u32_sub_safety_wit_24_r_eq_b.
Axiom proof_of_u32_sub_safety_wit_25_r_eq_a : u32_sub_safety_wit_25_r_eq_a.
Axiom proof_of_u32_sub_safety_wit_26_r_eq_a : u32_sub_safety_wit_26_r_eq_a.
Axiom proof_of_u32_sub_safety_wit_27_r_eq_a : u32_sub_safety_wit_27_r_eq_a.
Axiom proof_of_u32_sub_safety_wit_28_non_alias : u32_sub_safety_wit_28_non_alias.
Axiom proof_of_u32_sub_safety_wit_29_non_alias : u32_sub_safety_wit_29_non_alias.
Axiom proof_of_u32_sub_safety_wit_30_non_alias : u32_sub_safety_wit_30_non_alias.
Axiom proof_of_u32_sub_safety_wit_31_r_eq_b : u32_sub_safety_wit_31_r_eq_b.
Axiom proof_of_u32_sub_safety_wit_32_r_eq_b : u32_sub_safety_wit_32_r_eq_b.
Axiom proof_of_u32_sub_safety_wit_33_r_eq_b : u32_sub_safety_wit_33_r_eq_b.
Axiom proof_of_u32_sub_safety_wit_34_r_eq_a : u32_sub_safety_wit_34_r_eq_a.
Axiom proof_of_u32_sub_safety_wit_35_r_eq_a : u32_sub_safety_wit_35_r_eq_a.
Axiom proof_of_u32_sub_safety_wit_36_r_eq_a : u32_sub_safety_wit_36_r_eq_a.
Axiom proof_of_u32_sub_safety_wit_37_non_alias : u32_sub_safety_wit_37_non_alias.
Axiom proof_of_u32_sub_safety_wit_38_non_alias : u32_sub_safety_wit_38_non_alias.
Axiom proof_of_u32_sub_safety_wit_39_non_alias : u32_sub_safety_wit_39_non_alias.
Axiom proof_of_u32_sub_entail_wit_1_1_r_eq_b : u32_sub_entail_wit_1_1_r_eq_b.
Axiom proof_of_u32_sub_entail_wit_1_2_r_eq_a : u32_sub_entail_wit_1_2_r_eq_a.
Axiom proof_of_u32_sub_entail_wit_1_3_non_alias : u32_sub_entail_wit_1_3_non_alias.
Axiom proof_of_u32_sub_return_wit_1_r_eq_b : u32_sub_return_wit_1_r_eq_b.
Axiom proof_of_u32_sub_return_wit_2_r_eq_a : u32_sub_return_wit_2_r_eq_a.
Axiom proof_of_u32_sub_return_wit_3_non_alias : u32_sub_return_wit_3_non_alias.
Axiom proof_of_u32_sub_partial_solve_wit_1_r_eq_b_pure : u32_sub_partial_solve_wit_1_r_eq_b_pure.
Axiom proof_of_u32_sub_partial_solve_wit_1_r_eq_b : u32_sub_partial_solve_wit_1_r_eq_b.
Axiom proof_of_u32_sub_partial_solve_wit_2_r_eq_a_pure : u32_sub_partial_solve_wit_2_r_eq_a_pure.
Axiom proof_of_u32_sub_partial_solve_wit_2_r_eq_a : u32_sub_partial_solve_wit_2_r_eq_a.
Axiom proof_of_u32_sub_partial_solve_wit_3_non_alias_pure : u32_sub_partial_solve_wit_3_non_alias_pure.
Axiom proof_of_u32_sub_partial_solve_wit_3_non_alias : u32_sub_partial_solve_wit_3_non_alias.
Axiom proof_of_u32_sub_partial_solve_wit_4_r_eq_b_pure : u32_sub_partial_solve_wit_4_r_eq_b_pure.
Axiom proof_of_u32_sub_partial_solve_wit_4_r_eq_b : u32_sub_partial_solve_wit_4_r_eq_b.
Axiom proof_of_u32_sub_partial_solve_wit_5_r_eq_a_pure : u32_sub_partial_solve_wit_5_r_eq_a_pure.
Axiom proof_of_u32_sub_partial_solve_wit_5_r_eq_a : u32_sub_partial_solve_wit_5_r_eq_a.
Axiom proof_of_u32_sub_partial_solve_wit_6_non_alias_pure : u32_sub_partial_solve_wit_6_non_alias_pure.
Axiom proof_of_u32_sub_partial_solve_wit_6_non_alias : u32_sub_partial_solve_wit_6_non_alias.
Axiom proof_of_u32_sub_partial_solve_wit_7_r_eq_b_pure : u32_sub_partial_solve_wit_7_r_eq_b_pure.
Axiom proof_of_u32_sub_partial_solve_wit_7_r_eq_b : u32_sub_partial_solve_wit_7_r_eq_b.
Axiom proof_of_u32_sub_partial_solve_wit_8_r_eq_a_pure : u32_sub_partial_solve_wit_8_r_eq_a_pure.
Axiom proof_of_u32_sub_partial_solve_wit_8_r_eq_a : u32_sub_partial_solve_wit_8_r_eq_a.
Axiom proof_of_u32_sub_partial_solve_wit_9_non_alias_pure : u32_sub_partial_solve_wit_9_non_alias_pure.
Axiom proof_of_u32_sub_partial_solve_wit_9_non_alias : u32_sub_partial_solve_wit_9_non_alias.
Axiom proof_of_u32_sub_partial_solve_wit_10_r_eq_b_pure : u32_sub_partial_solve_wit_10_r_eq_b_pure.
Axiom proof_of_u32_sub_partial_solve_wit_10_r_eq_b : u32_sub_partial_solve_wit_10_r_eq_b.
Axiom proof_of_u32_sub_partial_solve_wit_11_r_eq_a_pure : u32_sub_partial_solve_wit_11_r_eq_a_pure.
Axiom proof_of_u32_sub_partial_solve_wit_11_r_eq_a : u32_sub_partial_solve_wit_11_r_eq_a.
Axiom proof_of_u32_sub_partial_solve_wit_12_non_alias_pure : u32_sub_partial_solve_wit_12_non_alias_pure.
Axiom proof_of_u32_sub_partial_solve_wit_12_non_alias : u32_sub_partial_solve_wit_12_non_alias.

End VC_Correct.
