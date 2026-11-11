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

(*----- Function u32_eq_zero -----*)

Definition u32_eq_zero_safety_wit_1 := 
forall (a_pre: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u32_eq_zero_safety_wit_2 := 
forall (a_pre: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_eq_zero_safety_wit_3 := 
forall (a_pre: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_eq_zero_safety_wit_4 := 
forall (a_pre: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_eq_zero_entail_wit_1 := 
forall (a_pre: Z) (A: Z) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_u256 a_pre A )
|--
  EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (A = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
.

Definition u32_eq_zero_return_wit_1 := 
(
forall (a_pre: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor x0 x1) x2) x3) = 0)) (PreH2 : (A = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH3 : (x3 < U64_MOD)) (PreH4 : (0 <= x3)) (PreH5 : (x2 < U64_MOD)) (PreH6 : (0 <= x2)) (PreH7 : (x1 < U64_MOD)) (PreH8 : (0 <= x1)) (PreH9 : (x0 < U64_MOD)) (PreH10 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 1) ” 
  &&  “ (A = 0) ”
  &&  (store_u256 a_pre A )
) \/
(
forall (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor x0 x1) x2) x3) = 0)) (PreH2 : (A = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH3 : (x3 < U64_MOD)) (PreH4 : (0 <= x3)) (PreH5 : (x2 < U64_MOD)) (PreH6 : (0 <= x2)) (PreH7 : (x1 < U64_MOD)) (PreH8 : (0 <= x1)) (PreH9 : (x0 < U64_MOD)) (PreH10 : (0 <= x0)) ,
  TT && emp 
|--
  “ (A = 0) ”
  &&  emp
).

Definition u32_eq_zero_return_wit_1_split_goal_1 := 
forall (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor x0 x1) x2) x3) = 0)) (PreH2 : (A = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH3 : (x3 < U64_MOD)) (PreH4 : (0 <= x3)) (PreH5 : (x2 < U64_MOD)) (PreH6 : (0 <= x2)) (PreH7 : (x1 < U64_MOD)) (PreH8 : (0 <= x1)) (PreH9 : (x0 < U64_MOD)) (PreH10 : (0 <= x0)) ,
  (A = 0)
.

Definition u32_eq_zero_return_wit_2 := 
(
forall (a_pre: Z) (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor x0 x1) x2) x3) <> 0)) (PreH2 : (A = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH3 : (x3 < U64_MOD)) (PreH4 : (0 <= x3)) (PreH5 : (x2 < U64_MOD)) (PreH6 : (0 <= x2)) (PreH7 : (x1 < U64_MOD)) (PreH8 : (0 <= x1)) (PreH9 : (x0 < U64_MOD)) (PreH10 : (0 <= x0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (A <> 0) ”
  &&  (store_u256 a_pre A )
) \/
(
forall (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor x0 x1) x2) x3) <> 0)) (PreH2 : (A = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH3 : (x3 < U64_MOD)) (PreH4 : (0 <= x3)) (PreH5 : (x2 < U64_MOD)) (PreH6 : (0 <= x2)) (PreH7 : (x1 < U64_MOD)) (PreH8 : (0 <= x1)) (PreH9 : (x0 < U64_MOD)) (PreH10 : (0 <= x0)) ,
  TT && emp 
|--
  “ (A <> 0) ”
  &&  emp
).

Definition u32_eq_zero_return_wit_2_split_goal_1 := 
forall (A: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor x0 x1) x2) x3) <> 0)) (PreH2 : (A = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH3 : (x3 < U64_MOD)) (PreH4 : (0 <= x3)) (PreH5 : (x2 < U64_MOD)) (PreH6 : (0 <= x2)) (PreH7 : (x1 < U64_MOD)) (PreH8 : (0 <= x1)) (PreH9 : (x0 < U64_MOD)) (PreH10 : (0 <= x0)) ,
  (A <> 0)
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.

Axiom proof_of_u32_eq_zero_safety_wit_1 : u32_eq_zero_safety_wit_1.
Axiom proof_of_u32_eq_zero_safety_wit_2 : u32_eq_zero_safety_wit_2.
Axiom proof_of_u32_eq_zero_safety_wit_3 : u32_eq_zero_safety_wit_3.
Axiom proof_of_u32_eq_zero_safety_wit_4 : u32_eq_zero_safety_wit_4.
Axiom proof_of_u32_eq_zero_entail_wit_1 : u32_eq_zero_entail_wit_1.
Axiom proof_of_u32_eq_zero_return_wit_1 : u32_eq_zero_return_wit_1.
Axiom proof_of_u32_eq_zero_return_wit_2 : u32_eq_zero_return_wit_2.

End VC_Correct.
