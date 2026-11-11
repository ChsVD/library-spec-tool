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

(*----- Function bignum_is_equal -----*)

Definition bignum_is_equal_safety_wit_1_non_alias := 
forall (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((b_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((b_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((b_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((b_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((a_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((a_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((a_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((a_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bignum_is_equal_safety_wit_2_non_alias := 
forall (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((b_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((b_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((b_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((b_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((a_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((a_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((a_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((a_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bignum_is_equal_safety_wit_3_non_alias := 
forall (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((b_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((b_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((b_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((b_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((a_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((a_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((a_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((a_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bignum_is_equal_safety_wit_4_non_alias := 
forall (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((b_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((b_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((b_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((b_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((a_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((a_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((a_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((a_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bignum_is_equal_safety_wit_5_non_alias := 
forall (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((b_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((b_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((b_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((b_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((a_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((a_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((a_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((a_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition bignum_is_equal_safety_wit_6_non_alias := 
forall (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((b_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((b_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((b_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((b_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((a_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((a_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((a_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((a_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition bignum_is_equal_safety_wit_7_non_alias := 
forall (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((b_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((b_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((b_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((b_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((a_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((a_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((a_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((a_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition bignum_is_equal_safety_wit_8_non_alias := 
forall (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((b_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((b_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((b_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((b_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((a_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((a_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((a_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((a_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition bignum_is_equal_entail_wit_1_non_alias := 
forall (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_u256_limbs a_pre A_non_alias )
  **  (store_u256_limbs b_pre B_non_alias )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
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
  &&  (((b_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((b_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((b_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((b_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((a_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((a_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((a_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((a_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
.

Definition bignum_is_equal_return_wit_1_non_alias := 
(
forall (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor (Z.lxor x0 x0_2) (Z.lxor x1 x1_2)) (Z.lxor x2 x2_2)) (Z.lxor x3 x3_2)) = 0)) (PreH2 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) ,
  (((b_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((b_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((b_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((b_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((a_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((a_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((a_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((a_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (1 = 1) ” 
  &&  “ (A_non_alias = B_non_alias) ”
  &&  (store_u256_limbs a_pre A_non_alias )
  **  (store_u256_limbs b_pre B_non_alias )
) \/
(
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor (Z.lxor x0 x0_2) (Z.lxor x1 x1_2)) (Z.lxor x2 x2_2)) (Z.lxor x3 x3_2)) = 0)) (PreH2 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) ,
  TT && emp 
|--
  “ (A_non_alias = B_non_alias) ”
  &&  emp
).

Definition bignum_is_equal_return_wit_1_non_alias_split_goal_1 := 
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor (Z.lxor x0 x0_2) (Z.lxor x1 x1_2)) (Z.lxor x2 x2_2)) (Z.lxor x3 x3_2)) = 0)) (PreH2 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) ,
  (A_non_alias = B_non_alias)
.

Definition bignum_is_equal_return_wit_2_non_alias := 
(
forall (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor (Z.lxor x0 x0_2) (Z.lxor x1 x1_2)) (Z.lxor x2 x2_2)) (Z.lxor x3 x3_2)) <> 0)) (PreH2 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) ,
  (((b_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((b_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((b_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((b_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((a_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((a_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((a_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((a_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 = 0) ” 
  &&  “ (A_non_alias <> B_non_alias) ”
  &&  (store_u256_limbs a_pre A_non_alias )
  **  (store_u256_limbs b_pre B_non_alias )
) \/
(
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor (Z.lxor x0 x0_2) (Z.lxor x1 x1_2)) (Z.lxor x2 x2_2)) (Z.lxor x3 x3_2)) <> 0)) (PreH2 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) ,
  TT && emp 
|--
  “ (A_non_alias <> B_non_alias) ”
  &&  emp
).

Definition bignum_is_equal_return_wit_2_non_alias_split_goal_1 := 
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor (Z.lxor x0 x0_2) (Z.lxor x1 x1_2)) (Z.lxor x2 x2_2)) (Z.lxor x3 x3_2)) <> 0)) (PreH2 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) ,
  (A_non_alias <> B_non_alias)
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.

Axiom proof_of_bignum_is_equal_safety_wit_1_non_alias : bignum_is_equal_safety_wit_1_non_alias.
Axiom proof_of_bignum_is_equal_safety_wit_2_non_alias : bignum_is_equal_safety_wit_2_non_alias.
Axiom proof_of_bignum_is_equal_safety_wit_3_non_alias : bignum_is_equal_safety_wit_3_non_alias.
Axiom proof_of_bignum_is_equal_safety_wit_4_non_alias : bignum_is_equal_safety_wit_4_non_alias.
Axiom proof_of_bignum_is_equal_safety_wit_5_non_alias : bignum_is_equal_safety_wit_5_non_alias.
Axiom proof_of_bignum_is_equal_safety_wit_6_non_alias : bignum_is_equal_safety_wit_6_non_alias.
Axiom proof_of_bignum_is_equal_safety_wit_7_non_alias : bignum_is_equal_safety_wit_7_non_alias.
Axiom proof_of_bignum_is_equal_safety_wit_8_non_alias : bignum_is_equal_safety_wit_8_non_alias.
Axiom proof_of_bignum_is_equal_entail_wit_1_non_alias : bignum_is_equal_entail_wit_1_non_alias.
Axiom proof_of_bignum_is_equal_return_wit_1_non_alias : bignum_is_equal_return_wit_1_non_alias.
Axiom proof_of_bignum_is_equal_return_wit_2_non_alias : bignum_is_equal_return_wit_2_non_alias.

End VC_Correct.
