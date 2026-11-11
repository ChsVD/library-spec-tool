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

(*----- Function u32_ge -----*)

Definition u32_ge_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_ge_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_ge_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x3_2 <> x3)) (PreH2 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_ge_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x3_2 <> x3)) (PreH2 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_ge_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x3_2 = x3)) (PreH2 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_ge_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x3_2 = x3)) (PreH2 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_ge_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x2_2 <> x2)) (PreH2 : (x3_2 = x3)) (PreH3 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0_2 < U64_MOD)) (PreH11 : (0 <= x0_2)) (PreH12 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_ge_safety_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x2_2 <> x2)) (PreH2 : (x3_2 = x3)) (PreH3 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0_2 < U64_MOD)) (PreH11 : (0 <= x0_2)) (PreH12 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_ge_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x2_2 = x2)) (PreH2 : (x3_2 = x3)) (PreH3 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0_2 < U64_MOD)) (PreH11 : (0 <= x0_2)) (PreH12 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_ge_safety_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x2_2 = x2)) (PreH2 : (x3_2 = x3)) (PreH3 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0_2 < U64_MOD)) (PreH11 : (0 <= x0_2)) (PreH12 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_ge_safety_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x1_2 <> x1)) (PreH2 : (x2_2 = x2)) (PreH3 : (x3_2 = x3)) (PreH4 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_ge_safety_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x1_2 <> x1)) (PreH2 : (x2_2 = x2)) (PreH3 : (x3_2 = x3)) (PreH4 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_ge_safety_wit_13 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x1_2 = x1)) (PreH2 : (x2_2 = x2)) (PreH3 : (x3_2 = x3)) (PreH4 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u32_ge_safety_wit_14 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x1_2 = x1)) (PreH2 : (x2_2 = x2)) (PreH3 : (x3_2 = x3)) (PreH4 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u32_ge_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_u256 a_pre A )
  **  (store_u256 b_pre B )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
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
.

Definition u32_ge_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0_2 >= x0)) (PreH2 : (x1_2 = x1)) (PreH3 : (x2_2 = x2)) (PreH4 : (x3_2 = x3)) (PreH5 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) ,
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
  &&  “ (1 = 1) ” 
  &&  “ (A >= B) ”
  &&  (store_u256 a_pre A )
  **  (store_u256 b_pre B )
) \/
(
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0_2 >= x0)) (PreH2 : (x1_2 = x1)) (PreH3 : (x2_2 = x2)) (PreH4 : (x3_2 = x3)) (PreH5 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) ,
  TT && emp 
|--
  “ (A >= B) ”
  &&  emp
).

Definition u32_ge_return_wit_1_split_goal_1 := 
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0_2 >= x0)) (PreH2 : (x1_2 = x1)) (PreH3 : (x2_2 = x2)) (PreH4 : (x3_2 = x3)) (PreH5 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) ,
  (A >= B)
.

Definition u32_ge_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0_2 < x0)) (PreH2 : (x1_2 = x1)) (PreH3 : (x2_2 = x2)) (PreH4 : (x3_2 = x3)) (PreH5 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (A < B) ”
  &&  (store_u256 a_pre A )
  **  (store_u256 b_pre B )
) \/
(
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0_2 < x0)) (PreH2 : (x1_2 = x1)) (PreH3 : (x2_2 = x2)) (PreH4 : (x3_2 = x3)) (PreH5 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) ,
  TT && emp 
|--
  “ (A < B) ”
  &&  emp
).

Definition u32_ge_return_wit_2_split_goal_1 := 
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0_2 < x0)) (PreH2 : (x1_2 = x1)) (PreH3 : (x2_2 = x2)) (PreH4 : (x3_2 = x3)) (PreH5 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) ,
  (A < B)
.

Definition u32_ge_return_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x1_2 > x1)) (PreH2 : (x1_2 <> x1)) (PreH3 : (x2_2 = x2)) (PreH4 : (x3_2 = x3)) (PreH5 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) ,
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
  &&  “ (1 = 1) ” 
  &&  “ (A >= B) ”
  &&  (store_u256 a_pre A )
  **  (store_u256 b_pre B )
) \/
(
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x1_2 > x1)) (PreH2 : (x1_2 <> x1)) (PreH3 : (x2_2 = x2)) (PreH4 : (x3_2 = x3)) (PreH5 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) ,
  TT && emp 
|--
  “ (A >= B) ”
  &&  emp
).

Definition u32_ge_return_wit_3_split_goal_1 := 
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x1_2 > x1)) (PreH2 : (x1_2 <> x1)) (PreH3 : (x2_2 = x2)) (PreH4 : (x3_2 = x3)) (PreH5 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) ,
  (A >= B)
.

Definition u32_ge_return_wit_4 := 
(
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x1_2 <= x1)) (PreH2 : (x1_2 <> x1)) (PreH3 : (x2_2 = x2)) (PreH4 : (x3_2 = x3)) (PreH5 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (A < B) ”
  &&  (store_u256 a_pre A )
  **  (store_u256 b_pre B )
) \/
(
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x1_2 <= x1)) (PreH2 : (x1_2 <> x1)) (PreH3 : (x2_2 = x2)) (PreH4 : (x3_2 = x3)) (PreH5 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) ,
  TT && emp 
|--
  “ (A < B) ”
  &&  emp
).

Definition u32_ge_return_wit_4_split_goal_1 := 
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x1_2 <= x1)) (PreH2 : (x1_2 <> x1)) (PreH3 : (x2_2 = x2)) (PreH4 : (x3_2 = x3)) (PreH5 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH6 : (x3_2 < U64_MOD)) (PreH7 : (0 <= x3_2)) (PreH8 : (x2_2 < U64_MOD)) (PreH9 : (0 <= x2_2)) (PreH10 : (x1_2 < U64_MOD)) (PreH11 : (0 <= x1_2)) (PreH12 : (x0_2 < U64_MOD)) (PreH13 : (0 <= x0_2)) (PreH14 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH15 : (x3 < U64_MOD)) (PreH16 : (0 <= x3)) (PreH17 : (x2 < U64_MOD)) (PreH18 : (0 <= x2)) (PreH19 : (x1 < U64_MOD)) (PreH20 : (0 <= x1)) (PreH21 : (x0 < U64_MOD)) (PreH22 : (0 <= x0)) ,
  (A < B)
.

Definition u32_ge_return_wit_5 := 
(
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x2_2 > x2)) (PreH2 : (x2_2 <> x2)) (PreH3 : (x3_2 = x3)) (PreH4 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) ,
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
  &&  “ (1 = 1) ” 
  &&  “ (A >= B) ”
  &&  (store_u256 a_pre A )
  **  (store_u256 b_pre B )
) \/
(
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x2_2 > x2)) (PreH2 : (x2_2 <> x2)) (PreH3 : (x3_2 = x3)) (PreH4 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) ,
  TT && emp 
|--
  “ (A >= B) ”
  &&  emp
).

Definition u32_ge_return_wit_5_split_goal_1 := 
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x2_2 > x2)) (PreH2 : (x2_2 <> x2)) (PreH3 : (x3_2 = x3)) (PreH4 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) ,
  (A >= B)
.

Definition u32_ge_return_wit_6 := 
(
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x2_2 <= x2)) (PreH2 : (x2_2 <> x2)) (PreH3 : (x3_2 = x3)) (PreH4 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (A < B) ”
  &&  (store_u256 a_pre A )
  **  (store_u256 b_pre B )
) \/
(
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x2_2 <= x2)) (PreH2 : (x2_2 <> x2)) (PreH3 : (x3_2 = x3)) (PreH4 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) ,
  TT && emp 
|--
  “ (A < B) ”
  &&  emp
).

Definition u32_ge_return_wit_6_split_goal_1 := 
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x2_2 <= x2)) (PreH2 : (x2_2 <> x2)) (PreH3 : (x3_2 = x3)) (PreH4 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) ,
  (A < B)
.

Definition u32_ge_return_wit_7 := 
(
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x3_2 > x3)) (PreH2 : (x3_2 <> x3)) (PreH3 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0_2 < U64_MOD)) (PreH11 : (0 <= x0_2)) (PreH12 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
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
  &&  “ (1 = 1) ” 
  &&  “ (A >= B) ”
  &&  (store_u256 a_pre A )
  **  (store_u256 b_pre B )
) \/
(
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x3_2 > x3)) (PreH2 : (x3_2 <> x3)) (PreH3 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0_2 < U64_MOD)) (PreH11 : (0 <= x0_2)) (PreH12 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  TT && emp 
|--
  “ (A >= B) ”
  &&  emp
).

Definition u32_ge_return_wit_7_split_goal_1 := 
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x3_2 > x3)) (PreH2 : (x3_2 <> x3)) (PreH3 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0_2 < U64_MOD)) (PreH11 : (0 <= x0_2)) (PreH12 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (A >= B)
.

Definition u32_ge_return_wit_8 := 
(
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x3_2 <= x3)) (PreH2 : (x3_2 <> x3)) (PreH3 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0_2 < U64_MOD)) (PreH11 : (0 <= x0_2)) (PreH12 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (A < B) ”
  &&  (store_u256 a_pre A )
  **  (store_u256 b_pre B )
) \/
(
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x3_2 <= x3)) (PreH2 : (x3_2 <> x3)) (PreH3 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0_2 < U64_MOD)) (PreH11 : (0 <= x0_2)) (PreH12 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  TT && emp 
|--
  “ (A < B) ”
  &&  emp
).

Definition u32_ge_return_wit_8_split_goal_1 := 
forall (B: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x3_2 <= x3)) (PreH2 : (x3_2 <> x3)) (PreH3 : (A = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0_2 < U64_MOD)) (PreH11 : (0 <= x0_2)) (PreH12 : (B = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) ,
  (A < B)
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.

Axiom proof_of_u32_ge_safety_wit_1 : u32_ge_safety_wit_1.
Axiom proof_of_u32_ge_safety_wit_2 : u32_ge_safety_wit_2.
Axiom proof_of_u32_ge_safety_wit_3 : u32_ge_safety_wit_3.
Axiom proof_of_u32_ge_safety_wit_4 : u32_ge_safety_wit_4.
Axiom proof_of_u32_ge_safety_wit_5 : u32_ge_safety_wit_5.
Axiom proof_of_u32_ge_safety_wit_6 : u32_ge_safety_wit_6.
Axiom proof_of_u32_ge_safety_wit_7 : u32_ge_safety_wit_7.
Axiom proof_of_u32_ge_safety_wit_8 : u32_ge_safety_wit_8.
Axiom proof_of_u32_ge_safety_wit_9 : u32_ge_safety_wit_9.
Axiom proof_of_u32_ge_safety_wit_10 : u32_ge_safety_wit_10.
Axiom proof_of_u32_ge_safety_wit_11 : u32_ge_safety_wit_11.
Axiom proof_of_u32_ge_safety_wit_12 : u32_ge_safety_wit_12.
Axiom proof_of_u32_ge_safety_wit_13 : u32_ge_safety_wit_13.
Axiom proof_of_u32_ge_safety_wit_14 : u32_ge_safety_wit_14.
Axiom proof_of_u32_ge_entail_wit_1 : u32_ge_entail_wit_1.
Axiom proof_of_u32_ge_return_wit_1 : u32_ge_return_wit_1.
Axiom proof_of_u32_ge_return_wit_2 : u32_ge_return_wit_2.
Axiom proof_of_u32_ge_return_wit_3 : u32_ge_return_wit_3.
Axiom proof_of_u32_ge_return_wit_4 : u32_ge_return_wit_4.
Axiom proof_of_u32_ge_return_wit_5 : u32_ge_return_wit_5.
Axiom proof_of_u32_ge_return_wit_6 : u32_ge_return_wit_6.
Axiom proof_of_u32_ge_return_wit_7 : u32_ge_return_wit_7.
Axiom proof_of_u32_ge_return_wit_8 : u32_ge_return_wit_8.

End VC_Correct.
