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
Import Snaive_C_Rules.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.

(*----- Function montg_equal_one -----*)

Definition montg_equal_one_safety_wit_1 := 
forall (src_pre: Z) (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((src_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((src_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((src_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((src_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_equal_one_safety_wit_2 := 
forall (src_pre: Z) (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((src_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((src_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((src_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((src_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_equal_one_safety_wit_3 := 
forall (src_pre: Z) (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((src_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((src_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((src_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((src_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_equal_one_safety_wit_4 := 
forall (src_pre: Z) (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((src_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((src_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((src_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((src_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_equal_one_safety_wit_5 := 
forall (src_pre: Z) (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((src_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((src_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((src_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((src_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition montg_equal_one_safety_wit_6 := 
forall (src_pre: Z) (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((src_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((src_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((src_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((src_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition montg_equal_one_safety_wit_7 := 
forall (src_pre: Z) (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((src_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((src_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((src_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((src_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition montg_equal_one_safety_wit_8 := 
forall (src_pre: Z) (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) ,
  ((( &( "ret" ) )) # Bool  |->_)
  **  (((src_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((src_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((src_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((src_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition montg_equal_one_entail_wit_1 := 
forall (src_pre: Z) (A_raw: Z) ,
  (store_u256_limbs ( &( "MONTG_ONE" ) ) MONTG_ONE_Z )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_u256_limbs src_pre A_raw )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (((src_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((src_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((src_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((src_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
.

Definition montg_equal_one_return_wit_1 := 
(
forall (src_pre: Z) (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor (Z.lxor x0_2 x0) (Z.lxor x1_2 x1)) (Z.lxor x2_2 x2)) (Z.lxor x3_2 x3)) = 0)) (PreH2 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) ,
  (((src_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((src_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((src_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((src_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (1 = 1) ” 
  &&  “ (A_raw = MONTG_ONE_Z) ”
  &&  (store_u256_limbs src_pre A_raw )
  **  (store_montg_one )
) \/
(
forall (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 >= 0)) (PreH6 : (x1 >= 0)) (PreH7 : (x2 >= 0)) (PreH8 : (x3 >= 0)) (PreH9 : ((Z.lor (Z.lor (Z.lor (Z.lxor x0_2 x0) (Z.lxor x1_2 x1)) (Z.lxor x2_2 x2)) (Z.lxor x3_2 x3)) = 0)) (PreH10 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) ,
  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (A_raw = MONTG_ONE_Z) ”
  &&  (store_montg_one )
).

Definition montg_equal_one_return_wit_1_split_goal_1 := 
forall (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 >= 0)) (PreH6 : (x1 >= 0)) (PreH7 : (x2 >= 0)) (PreH8 : (x3 >= 0)) (PreH9 : ((Z.lor (Z.lor (Z.lor (Z.lxor x0_2 x0) (Z.lxor x1_2 x1)) (Z.lxor x2_2 x2)) (Z.lxor x3_2 x3)) = 0)) (PreH10 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) ,
  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (A_raw = MONTG_ONE_Z) ”
.

Definition montg_equal_one_return_wit_1_split_goal_spatial := 
forall (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 >= 0)) (PreH6 : (x1 >= 0)) (PreH7 : (x2 >= 0)) (PreH8 : (x3 >= 0)) (PreH9 : ((Z.lor (Z.lor (Z.lor (Z.lxor x0_2 x0) (Z.lxor x1_2 x1)) (Z.lxor x2_2 x2)) (Z.lxor x3_2 x3)) = 0)) (PreH10 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) ,
  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  (store_montg_one )
.

Definition montg_equal_one_return_wit_2 := 
(
forall (src_pre: Z) (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.lor (Z.lor (Z.lor (Z.lxor x0_2 x0) (Z.lxor x1_2 x1)) (Z.lxor x2_2 x2)) (Z.lxor x3_2 x3)) <> 0)) (PreH2 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) ,
  (((src_pre + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((src_pre + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((src_pre + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((src_pre + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 = 0) ” 
  &&  “ (A_raw <> MONTG_ONE_Z) ”
  &&  (store_u256_limbs src_pre A_raw )
  **  (store_montg_one )
) \/
(
forall (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 >= 0)) (PreH6 : (x1 >= 0)) (PreH7 : (x2 >= 0)) (PreH8 : (x3 >= 0)) (PreH9 : ((Z.lor (Z.lor (Z.lor (Z.lxor x0_2 x0) (Z.lxor x1_2 x1)) (Z.lxor x2_2 x2)) (Z.lxor x3_2 x3)) <> 0)) (PreH10 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) ,
  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (A_raw <> MONTG_ONE_Z) ”
  &&  (store_montg_one )
).

Definition montg_equal_one_return_wit_2_split_goal_1 := 
forall (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 >= 0)) (PreH6 : (x1 >= 0)) (PreH7 : (x2 >= 0)) (PreH8 : (x3 >= 0)) (PreH9 : ((Z.lor (Z.lor (Z.lor (Z.lxor x0_2 x0) (Z.lxor x1_2 x1)) (Z.lxor x2_2 x2)) (Z.lxor x3_2 x3)) <> 0)) (PreH10 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) ,
  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (A_raw <> MONTG_ONE_Z) ”
.

Definition montg_equal_one_return_wit_2_split_goal_spatial := 
forall (A_raw: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 >= 0)) (PreH6 : (x1 >= 0)) (PreH7 : (x2 >= 0)) (PreH8 : (x3 >= 0)) (PreH9 : ((Z.lor (Z.lor (Z.lor (Z.lxor x0_2 x0) (Z.lxor x1_2 x1)) (Z.lxor x2_2 x2)) (Z.lxor x3_2 x3)) <> 0)) (PreH10 : (A_raw = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) ,
  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  (store_montg_one )
.

Definition montg_equal_one_partial_solve_wit_1 := 
forall (src_pre: Z) (A_raw: Z) ,
  (store_u256_limbs src_pre A_raw )
  **  (store_montg_one )
|--
  (store_montg_one )
  **  (store_u256_limbs src_pre A_raw )
.

Definition montg_equal_one_which_implies_wit_1 := 
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

Definition montg_equal_one_derive_field_by_raw := 
forall (src_pre: Z) (P_field: Z) (A_field: Z) ,
  “ (src_pre = P_field) ” 
  &&  “ (0 <= A_field) ” 
  &&  “ (A_field < SM2_P_Z) ”
  &&  (store_fp P_field A_field )
  **  (store_montg_one )
|--
EX (A_raw: Z) ,
  ((store_u256_limbs src_pre A_raw )
  **  (store_montg_one ))
  **
  (((EX retval_2,
  “ (retval_2 = 0) ” 
  &&  “ (A_raw <> MONTG_ONE_Z) ”
  &&  (store_u256_limbs src_pre A_raw )
  **  (store_montg_one ))
  ||
  (EX retval_2,
  “ (retval_2 = 1) ” 
  &&  “ (A_raw = MONTG_ONE_Z) ”
  &&  (store_u256_limbs src_pre A_raw )
  **  (store_montg_one )))
  -*
  ((EX retval,
  “ (src_pre = P_field) ” 
  &&  “ (retval = 1) ” 
  &&  “ (A_field = MONTG_ONE_Z) ”
  &&  (store_fp P_field A_field )
  **  (store_montg_one ))
  ||
  (EX retval,
  “ (src_pre = P_field) ” 
  &&  “ (retval = 0) ” 
  &&  “ (A_field <> MONTG_ONE_Z) ”
  &&  (store_fp P_field A_field )
  **  (store_montg_one ))))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.

Axiom proof_of_montg_equal_one_safety_wit_1 : montg_equal_one_safety_wit_1.
Axiom proof_of_montg_equal_one_safety_wit_2 : montg_equal_one_safety_wit_2.
Axiom proof_of_montg_equal_one_safety_wit_3 : montg_equal_one_safety_wit_3.
Axiom proof_of_montg_equal_one_safety_wit_4 : montg_equal_one_safety_wit_4.
Axiom proof_of_montg_equal_one_safety_wit_5 : montg_equal_one_safety_wit_5.
Axiom proof_of_montg_equal_one_safety_wit_6 : montg_equal_one_safety_wit_6.
Axiom proof_of_montg_equal_one_safety_wit_7 : montg_equal_one_safety_wit_7.
Axiom proof_of_montg_equal_one_safety_wit_8 : montg_equal_one_safety_wit_8.
Axiom proof_of_montg_equal_one_entail_wit_1 : montg_equal_one_entail_wit_1.
Axiom proof_of_montg_equal_one_return_wit_1 : montg_equal_one_return_wit_1.
Axiom proof_of_montg_equal_one_return_wit_2 : montg_equal_one_return_wit_2.
Axiom proof_of_montg_equal_one_partial_solve_wit_1 : montg_equal_one_partial_solve_wit_1.
Axiom proof_of_montg_equal_one_which_implies_wit_1 : montg_equal_one_which_implies_wit_1.
Axiom proof_of_montg_equal_one_derive_field_by_raw : montg_equal_one_derive_field_by_raw.

End VC_Correct.
